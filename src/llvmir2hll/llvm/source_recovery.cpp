#include <llvm/IR/IRBuilder.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Support/KnownBits.h>
#include "retdec/bin2llvmir/utils/llvm.h"
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Transforms/Utils/Local.h>
#include <set>
#include "retdec/config/config.h"
#include "retdec/llvmir2hll/ir/function.h"
#include "retdec/llvmir2hll/ir/int_type.h"
#include "retdec/llvmir2hll/ir/pointer_type.h"
#include "retdec/llvmir2hll/ir/module.h"
#include "retdec/llvmir2hll/ir/variable.h"
#include "retdec/llvmir2hll/ir/const_int.h"
#include "retdec/llvmir2hll/ir/assign_stmt.h"
#include "retdec/llvmir2hll/ir/and_op_expr.h"
#include "retdec/llvmir2hll/ir/or_op_expr.h"
#include "retdec/llvmir2hll/ir/var_def_stmt.h"
#include "retdec/llvmir2hll/ir/const_array.h"
#include "retdec/llvmir2hll/ir/array_index_op_expr.h"
#include "retdec/llvmir2hll/ir/neq_op_expr.h"
#include "retdec/llvmir2hll/ir/eq_op_expr.h"
#include "retdec/llvmir2hll/ir/cast_expr.h"
#include "retdec/llvmir2hll/ir/if_stmt.h"
#include "retdec/llvmir2hll/ir/return_stmt.h"
#include "retdec/llvmir2hll/optimizer/func_optimizer.h"
#include "retdec/llvmir2hll/analysis/goto_target_analysis.h"
#include "retdec/llvmir2hll/analysis/alias_analysis/alias_analyses/simple_alias_analysis.h"
#include "retdec/llvmir2hll/analysis/alias_analysis/alias_analysis.h"
#include "retdec/llvmir2hll/support/expression_negater.h"
#include "retdec/llvmir2hll/utils/ir.h"
#include "retdec/llvmir2hll/llvm/source_recovery.h"
#include "retdec/bin2llvmir/utils/counter_provenance.h"

namespace retdec {
namespace llvmir2hll {
namespace {
bool fixedStackOffset(llvm::Value *value, llvm::AllocaInst *frame,
		const llvm::DataLayout &layout, int64_t &offset) {
	if (value == frame) { offset = 0; return true; }
	if (auto *cast = llvm::dyn_cast<llvm::BitCastInst>(value))
		return fixedStackOffset(cast->getOperand(0), frame, layout, offset);
	if (auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(value)) {
		llvm::APInt delta(layout.getPointerSizeInBits(), 0);
		if (!gep->accumulateConstantOffset(layout, delta)
				|| !fixedStackOffset(gep->getPointerOperand(), frame, layout, offset)) return false;
		offset += delta.getSExtValue();
		return true;
	}
	return false;
}

void recoverStackTables(llvm::Module &module, const config::Config &config) {
	if (module.getDataLayout().getPointerSizeInBits() != 32) return;
	for (auto &function : module) {
		if (function.size() != 1) continue;
		auto &block = function.front();
		for (auto it = block.begin(); it != block.end(); ++it) {
			auto *call = llvm::dyn_cast<llvm::CallInst>(&*it);
			if (!call) continue;
			auto *target = llvm::dyn_cast<llvm::IntToPtrInst>(call->getCalledValue());
			auto *load = target ? llvm::dyn_cast<llvm::LoadInst>(target->getOperand(0)) : nullptr;
			auto *address = load ? llvm::dyn_cast<llvm::IntToPtrInst>(load->getPointerOperand()) : nullptr;
			auto *sum = address ? llvm::dyn_cast<llvm::BinaryOperator>(address->getOperand(0)) : nullptr;
			if (!sum || sum->getOpcode() != llvm::Instruction::Add || !load->hasOneUse()
					|| load->isVolatile() || load->isAtomic() || !target->hasOneUse()) continue;
			auto *base = llvm::dyn_cast<llvm::BinaryOperator>(sum->getOperand(0));
			auto *scale = llvm::dyn_cast<llvm::BinaryOperator>(sum->getOperand(1));
			if (!base || base->getOpcode() != llvm::Instruction::Add || !scale
					|| scale->getOpcode() != llvm::Instruction::Mul) continue;
			auto *start = llvm::dyn_cast<llvm::ConstantInt>(base->getOperand(1));
			auto *stride = llvm::dyn_cast<llvm::ConstantInt>(scale->getOperand(1));
			auto *ptr = llvm::dyn_cast<llvm::PtrToIntInst>(base->getOperand(0));
			auto *frame = ptr ? llvm::dyn_cast<llvm::AllocaInst>(ptr->getPointerOperand()) : nullptr;
			if (!frame || !start || !stride || stride->getZExtValue() != 4) continue;
			std::map<int64_t, llvm::StoreInst*> stores;
			std::set<llvm::Value*> seen;
			std::vector<llvm::Value*> pending{frame};
			bool safe = true;
			while (!pending.empty() && safe) {
				auto *value = pending.back(); pending.pop_back();
				if (!seen.insert(value).second) continue;
				for (auto *user : value->users()) {
					if (user == ptr || user == base || user == sum || user == address || user == load) continue;
					if (llvm::isa<llvm::BitCastInst>(user) || llvm::isa<llvm::GetElementPtrInst>(user)) {
						pending.push_back(user); continue;
					}
					auto *store = llvm::dyn_cast<llvm::StoreInst>(user);
					int64_t offset;
					if (!store || store->getParent() != &block || store->isVolatile() || store->isAtomic()
							|| !store->getValueOperand()->getType()->isIntegerTy(32)
							|| !llvm::isa<llvm::ConstantInt>(store->getValueOperand())
							|| !fixedStackOffset(store->getPointerOperand(), frame, module.getDataLayout(), offset)
							|| !stores.emplace(offset, store).second) { safe = false; break; }
				}
			}
			if (!safe || stores.empty() || !ptr->hasOneUse() || !base->hasOneUse()
					|| !sum->hasOneUse() || !address->hasOneUse()) continue;
			int64_t expected = start->getSExtValue();
			for (const auto &entry : stores) {
				bool before = false;
				for (auto &instruction : block) {
					if (&instruction == load) break;
					if (&instruction == entry.second) before = true;
				}
				if (entry.first != expected || !before) safe = false;
				expected += 4;
			}
			if (!safe) continue;
			std::vector<const common::Function*> declarations;
			bool declared = call->arg_empty() && call->use_empty()
					&& call->getCallingConv() == llvm::CallingConv::C
					&& !call->isTailCall() && call->getNumOperandBundles() == 0
					&& call->getAttributes().isEmpty();
			for (const auto &entry : stores) {
				auto address = llvm::cast<llvm::ConstantInt>(entry.second->getValueOperand())->getZExtValue();
				auto *source = config.functions.getFunctionByStartAddress(address);
				declared &= source && source->parameters.empty() && !source->isVariadic()
						&& source->returnType.getLlvmIr() == "void";
				declarations.push_back(source);
			}
			auto *handlerType = declared
				? llvm::FunctionType::get(llvm::Type::getVoidTy(module.getContext()), false)->getPointerTo()
				: target->getType();
			if (declared) {
				for (auto *source : declarations) {
					auto *named = module.getNamedValue(source->getName());
					if (named && named->getType() != handlerType) declared = false;
				}
				if (!declared) handlerType = target->getType();
			}
			llvm::IRBuilder<> builder(frame);
			auto *tableType = llvm::ArrayType::get(handlerType, stores.size());
			auto *table = builder.CreateAlloca(tableType, nullptr, "local_handlers");
			table->setAlignment(4);
			unsigned index = 0;
			for (const auto &entry : stores) {
				builder.SetInsertPoint(entry.second);
				auto *slot = builder.CreateGEP(table, {builder.getInt32(0), builder.getInt32(index)});
				llvm::Value *value = nullptr;
				if (declared) {
					auto *type = llvm::cast<llvm::FunctionType>(handlerType->getPointerElementType());
					value = module.getOrInsertFunction(declarations[index]->getName(), type);
				} else {
					value = builder.CreateIntToPtr(entry.second->getValueOperand(), handlerType);
				}
				++index;
				builder.CreateStore(value, slot);
				auto *oldAddress = llvm::dyn_cast<llvm::Instruction>(entry.second->getPointerOperand());
				entry.second->eraseFromParent();
				if (oldAddress) llvm::RecursivelyDeleteTriviallyDeadInstructions(oldAddress);
			}
			builder.SetInsertPoint(load);
			auto *slot = builder.CreateGEP(table, {builder.getInt32(0), scale->getOperand(0)});
			auto *handler = builder.CreateLoad(slot);
			if (declared) {
				builder.SetInsertPoint(call);
				builder.CreateCall(handler);
				it = call->eraseFromParent();
				--it;
			} else {
				target->replaceAllUsesWith(handler);
			}
			llvm::RecursivelyDeleteTriviallyDeadInstructions(target);
		}
	}
}

void recoverDeclaredArrays(llvm::Module &module, const config::Config &config) {
	const auto &layout = module.getDataLayout();
	if (layout.getPointerSizeInBits() != 32) return;
	for (auto &function : module) for (auto &block : function) {
		for (auto &instruction : block) {
			auto *load = llvm::dyn_cast<llvm::LoadInst>(&instruction);
			if (!load || load->isVolatile() || load->isAtomic()) continue;
			auto *pointer = llvm::dyn_cast<llvm::IntToPtrInst>(load->getPointerOperand());
			auto *add = pointer ? llvm::dyn_cast<llvm::BinaryOperator>(pointer->getOperand(0)) : nullptr;
			if (!add || add->getOpcode() != llvm::Instruction::Add || !add->getType()->isIntegerTy(32)) continue;
			auto *low = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(1));
			auto *base = llvm::dyn_cast<llvm::BinaryOperator>(add->getOperand(0));
			if (!low || !base || base->getOpcode() != llvm::Instruction::Or) continue;
			auto *high = llvm::dyn_cast<llvm::ConstantInt>(base->getOperand(1));
			if (!high) continue;
			auto *offset = base->getOperand(0);
			auto known = llvm::computeKnownBits(offset, layout);
			if ((known.Zero & high->getValue()) != high->getValue()) continue;
			auto address = (high->getValue() + low->getValue()).getZExtValue();
			auto *source = config.globals.getObjectByAddress(address);
			if (!source) continue;
			auto *type = bin2llvmir::llvm_utils::stringToLlvmType(module.getContext(), source->type.getLlvmIr());
			auto *array = llvm::dyn_cast_or_null<llvm::ArrayType>(type);
			if (!array || array->getElementType() != load->getType()
					|| source->type.getLlvmIr().compare(0, 5, "[0 x ") != 0) continue;
			if (source->type.getLlvmIr().compare(0, 5, "[0 x ") == 0) {
				array = llvm::ArrayType::get(array->getElementType(), 0);
				type = array;
			}
			auto size = layout.getTypeAllocSize(array->getElementType());
			if (!size || (size & (size - 1)) || (known.Zero.getZExtValue() & (size - 1)) != size - 1) continue;
			auto *named = module.getNamedValue(source->getName());
			auto *global = llvm::dyn_cast_or_null<llvm::GlobalVariable>(named);
			if (named && (!global || global->getValueType() != type)) continue;
			if (!global) global = new llvm::GlobalVariable(module, type, false,
				llvm::GlobalValue::ExternalLinkage, nullptr, source->getName());
			llvm::IRBuilder<> builder(load);
			auto *index = builder.CreateUDiv(offset, builder.getInt32(size));
			load->setOperand(0, builder.CreateGEP(global, {builder.getInt32(0), index}));
		}
	}
}

void recoverMembershipPredicates(llvm::Module &module) {
	for (auto &function : module) {
		for (auto &block : function) {
			auto *sw = llvm::dyn_cast<llvm::SwitchInst>(block.getTerminator());
			if (!sw || sw->getNumCases() < 2 || sw->getNumCases() > 8) continue;
			auto *destination = sw->case_begin()->getCaseSuccessor();
			bool same = destination != sw->getDefaultDest();
			for (auto &entry : sw->cases()) same &= entry.getCaseSuccessor() == destination;
			if (!same || llvm::isa<llvm::PHINode>(destination->begin())
					|| llvm::isa<llvm::PHINode>(sw->getDefaultDest()->begin())) continue;
			llvm::IRBuilder<> builder(sw);
			llvm::Value *condition = nullptr;
			for (auto &entry : sw->cases()) {
				auto *equal = builder.CreateICmpEQ(sw->getCondition(), entry.getCaseValue());
				condition = condition ? builder.CreateOr(condition, equal) : equal;
			}
			builder.CreateCondBr(condition, destination, sw->getDefaultDest());
			sw->eraseFromParent();
		}
	}
}

class ForwardGuardRecovery final : public FuncOptimizer {
public:
	explicit ForwardGuardRecovery(ShPtr<Module> module) : FuncOptimizer(module) {}
	std::string getId() const override { return "ForwardGuardRecovery"; }
private:
	void visit(ShPtr<IfStmt> statement) override {
		FuncOptimizer::visit(statement);
		if (statement->hasElseClause() || statement->hasElseIfClauses()) return;
		auto exit = cast<ReturnStmt>(skipEmptyStmts(statement->getFirstIfBody()));
		auto following = statement->getSuccessor();
		if (!exit || !isa<ConstInt>(exit->getRetVal()) || exit->getSuccessor()
				|| !following || !endsWithRetOrUnreach(following)) return;
		if (GotoTargetAnalysis::hasGotoTargets(following)
				|| GotoTargetAnalysis::hasGotoTargets(statement->getFirstIfBody())) return;
		auto body = statement->getFirstIfBody();
		statement->setFirstIfCond(ExpressionNegater::negate(statement->getFirstIfCond()));
		statement->setSuccessor(body);
		statement->setFirstIfBody(following);
	}
};

class TableInitializerRecovery final : public FuncOptimizer {
public:
	explicit TableInitializerRecovery(ShPtr<Module> module) : FuncOptimizer(module) {}
	std::string getId() const override { return "TableInitializerRecovery"; }
private:
	void visit(ShPtr<VarDefStmt> definition) override {
		FuncOptimizer::visit(definition);
		auto type = cast<ArrayType>(definition->getVar()->getType());
		if (!type || definition->getInitializer() || definition->getVar()->isExternal()
				|| type->getDimensions().size() != 1 || type->getDimensions()[0] > 16
				|| GotoTargetAnalysis::hasGotoTargets(definition)) return;
		ConstArray::ArrayValue values;
		std::vector<ShPtr<Statement>> stores;
		auto next = skipEmptyStmts(definition->getSuccessor());
		for (std::size_t i = 0; i < type->getDimensions()[0]; ++i) {
			auto assign = cast<AssignStmt>(next);
			auto slot = assign ? cast<ArrayIndexOpExpr>(assign->getLhs()) : nullptr;
			auto index = slot ? cast<ConstInt>(slot->getIndex()) : nullptr;
			auto handler = assign ? cast<Variable>(assign->getRhs()) : nullptr;
			auto function = handler ? module->getFuncByName(handler->getName()) : nullptr;
			if (!slot || slot->getBase() != definition->getVar() || !index
					|| index->getValue() != i || !function || function->getAsVar() != handler
					|| assign->isGotoTarget()) return;
			values.push_back(cast<Expression>(handler->clone()));
			stores.push_back(assign);
			next = skipEmptyStmts(assign->getSuccessor());
		}
		if (values.empty()) return;
		definition->setInitializer(ConstArray::create(values, type));
		for (auto store : stores) Statement::removeStatement(store);
	}
};

class MembershipReturnRecovery final : public FuncOptimizer {
public:
	explicit MembershipReturnRecovery(ShPtr<Module> module) : FuncOptimizer(module), aliases(SimpleAliasAnalysis::create()) {
		aliases->init(module);
	}
	std::string getId() const override { return "MembershipReturnRecovery"; }
private:
	bool scalar(ShPtr<Expression> expr, ShPtr<Variable> result) {
		if (isa<ConstInt>(expr)) return true;
		if (auto var = cast<Variable>(expr))
			return var != result && currFunc->hasLocalVar(var) && !var->isExternal()
				&& !aliases->mayBePointed(var) && isa<IntType>(var->getType());
		if (auto conversion = cast<CastExpr>(expr)) return scalar(conversion->getOperand(), result);
		return false;
	}
	bool terms(ShPtr<Expression> expr, ShPtr<Variable> result,
			std::vector<ShPtr<Expression>> &out) {
		if (auto conjunction = cast<AndOpExpr>(expr))
			return terms(conjunction->getFirstOperand(), result, out)
				&& terms(conjunction->getSecondOperand(), result, out);
		auto unequal = cast<NeqOpExpr>(expr);
		if (!unequal || !scalar(unequal->getFirstOperand(), result)
				|| !scalar(unequal->getSecondOperand(), result)) return false;
		out.push_back(expr);
		return out.size() <= 8;
	}
	void visit(ShPtr<AssignStmt> init) override {
		FuncOptimizer::visit(init);
		auto result = cast<Variable>(init->getLhs());
		auto initial = cast<ConstInt>(init->getRhs());
		auto branch = cast<IfStmt>(skipEmptyStmts(init->getSuccessor()));
		if (!result || !currFunc->hasLocalVar(result) || result->isExternal()
				|| aliases->mayBePointed(result) || !initial
				|| (!initial->isOne() && !initial->isZero())
				|| !branch || branch->hasElseClause() || branch->hasElseIfClauses()) return;
		auto update = cast<AssignStmt>(skipEmptyStmts(branch->getFirstIfBody()));
		auto exit = cast<ReturnStmt>(skipEmptyStmts(branch->getSuccessor()));
		if (!update || skipEmptyStmts(update->getSuccessor()) || update->getLhs() != result
				|| !exit || exit->getRetVal() != result || exit->getSuccessor()
				|| GotoTargetAnalysis::hasGotoTargets(init)) return;
		if (initial->isZero()) {
			if (!isa<NeqOpExpr>(branch->getFirstIfCond()) || !isa<NeqOpExpr>(update->getRhs())) return;
			auto condition = OrOpExpr::create(
				ExpressionNegater::negate(cast<Expression>(branch->getFirstIfCond()->clone())),
				ExpressionNegater::negate(cast<Expression>(update->getRhs()->clone())));
			init->setSuccessor(IfStmt::create(condition, ReturnStmt::create(cast<Expression>(initial->clone())),
				ReturnStmt::create(ConstInt::create(1, 32))));
			return;
		}
		auto final = cast<EqOpExpr>(update->getRhs());
		if (!final || !scalar(final->getFirstOperand(), result)
				|| !scalar(final->getSecondOperand(), result)) return;
		std::vector<ShPtr<Expression>> conditions;
		if (!terms(branch->getFirstIfCond(), result, conditions) || conditions.size() < 2) return;
		ShPtr<Statement> chain = IfStmt::create(cast<Expression>(conditions.back()->clone()),
			ReturnStmt::create(cast<Expression>(final->clone())),
			ReturnStmt::create(cast<Expression>(initial->clone())));
		conditions.pop_back();
		for (auto it = conditions.rbegin(); it != conditions.rend(); ++it)
			chain = IfStmt::create(ExpressionNegater::negate(cast<Expression>((*it)->clone())),
				ReturnStmt::create(cast<Expression>(initial->clone())), chain);
		init->removeSuccessor();
		Statement::replaceStatement(init, chain);
	}
	ShPtr<AliasAnalysis> aliases;
};

bool onlyLowBitsUsed(const llvm::Argument &arg, unsigned bits) {
	if (arg.use_empty()) return false;
	for (auto *user : arg.users()) {
		if (auto *trunc = llvm::dyn_cast<llvm::TruncInst>(user)) {
			if (trunc->getType()->getIntegerBitWidth() <= bits) continue;
		}
		if (auto *op = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
			auto *c = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(1));
			if (c && op->getOperand(0) == &arg) {
				if (op->getOpcode() == llvm::Instruction::And
						&& c->getValue().getActiveBits() <= bits) continue;
				if (op->getOpcode() == llvm::Instruction::URem
						&& c->getValue().isPowerOf2()
						&& c->getValue().logBase2() <= bits) continue;
			}
		}
		return false;
	}
	return true;
}
}

void recoverPointerExpressions(llvm::Module &module, const config::Config &config) {
	if (config.architecture.isMipsOrPic32()) {
		bin2llvmir::counter_provenance::validate(module);
		bin2llvmir::counter_provenance::restoreTestedValue(module);
		recoverStackTables(module, config);
		recoverDeclaredArrays(module, config);
	}
	recoverMembershipPredicates(module);
	const auto &layout = module.getDataLayout();
	std::vector<llvm::IntToPtrInst*> candidates;
	for (auto &function : module)
		for (auto &block : function)
			for (auto &instruction : block)
				if (auto *cast = llvm::dyn_cast<llvm::IntToPtrInst>(&instruction))
					candidates.push_back(cast);
	for (auto *cast : candidates) {
		auto *add = llvm::dyn_cast<llvm::BinaryOperator>(cast->getOperand(0));
		if (!add || add->getOpcode() != llvm::Instruction::Add) continue;
		llvm::PtrToIntInst *base = nullptr;
		llvm::ConstantInt *offset = nullptr;
		for (unsigned i = 0; i < 2; ++i) {
			base = llvm::dyn_cast<llvm::PtrToIntInst>(add->getOperand(i));
			offset = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(1-i));
			if (base && offset) break;
		}
		if (!base || !offset) continue;
		auto *pointer = llvm::cast<llvm::PointerType>(base->getPointerOperand()->getType());
		if (pointer->getAddressSpace() != 0 || cast->getType()->getPointerAddressSpace() != 0
				|| base->getType()->getIntegerBitWidth() != layout.getPointerSizeInBits()) continue;
		llvm::IRBuilder<> builder(cast);
		auto *bytes = builder.CreateBitCast(base->getPointerOperand(), builder.getInt8PtrTy());
		auto *address = builder.CreateGEP(bytes, offset);
		auto *typed = builder.CreateBitCast(address, cast->getType());
		cast->replaceAllUsesWith(typed);
		cast->eraseFromParent();
		if (add->use_empty()) add->eraseFromParent();
		if (base->use_empty()) base->eraseFromParent();
	}
}

void recoverSourceSignatures(ShPtr<Module> module, const config::Config &config) {
	if (!config.architecture.isMipsOrPic32()) return;
	ForwardGuardRecovery(module).optimize();
	MembershipReturnRecovery(module).optimize();
	TableInitializerRecovery(module).optimize();
	for (auto f = module->func_begin(); f != module->func_end(); ++f) {
		auto function = *f;
		auto *machine = module->getLLVMModule()->getFunction(function->getInitialName());
		auto *source = config.functions.getFunctionByName(function->getInitialName());
		if (!machine || !source || machine->isDeclaration()
				|| source->parameters.size() != function->getNumOfParams()) continue;
		auto params = function->getParams();
		auto arg = machine->arg_begin();
		std::size_t index = 0;
		for (const auto &parameter : source->parameters) {
			const auto &spelling = parameter.type.getCType();
			unsigned bits = spelling == "unsigned char" || spelling == "uint8_t" ? 8
				: spelling == "unsigned short" || spelling == "uint16_t" ? 16 : 0;
			if (bits && arg->getType()->isIntegerTy() && onlyLowBitsUsed(*arg, bits))
				params[index]->setType(IntType::create(arg->getType()->getIntegerBitWidth(), false));
			++arg; ++index;
		}
		function->setParams(params);
	}
}

namespace {

ShPtr<Type> unsignedBaseType(ShPtr<Type> type) {
	if (auto pointer = cast<PointerType>(type))
		return PointerType::create(unsignedBaseType(pointer->getContainedType()));
	if (auto integer = cast<IntType>(type))
		return integer->isUnsigned() ? type : IntType::create(integer->getSize(), false);
	return type;
}

}

void applyDeclaredAccessQualifiers(ShPtr<Module> module, const config::Config &config) {
	for (const auto &object : config.globals) {
		if (!object.type.isVolatile()) continue;
		auto variable = module->getGlobalVarByName(object.getName());
		if (!variable) continue;
		if (object.type.hasUnsignedBaseType())
			variable->setType(unsignedBaseType(variable->getType()));
		variable->markAsVolatile();
	}
}
}
}
