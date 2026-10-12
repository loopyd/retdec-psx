#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Metadata.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Support/KnownBits.h>
#include "retdec/bin2llvmir/utils/llvm.h"
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/ValueHandle.h>
#include <llvm/Transforms/Utils/Local.h>
#include <set>
#include <map>
#include <algorithm>
#include <optional>
#include <stdexcept>
#include "retdec/config/config.h"
#include "retdec/llvmir2hll/ir/function.h"
#include "retdec/llvmir2hll/ir/int_type.h"
#include "retdec/llvmir2hll/ir/void_type.h"
#include "retdec/llvmir2hll/ir/empty_stmt.h"
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
#include "retdec/llvmir2hll/ir/address_op_expr.h"
#include "retdec/llvmir2hll/ir/bit_cast_expr.h"
#include "retdec/llvmir2hll/ir/add_op_expr.h"
#include "retdec/llvmir2hll/ir/sub_op_expr.h"
#include "retdec/llvmir2hll/ir/mul_op_expr.h"
#include "retdec/llvmir2hll/ir/bit_and_op_expr.h"
#include "retdec/llvmir2hll/ir/bit_or_op_expr.h"
#include "retdec/llvmir2hll/ir/bit_xor_op_expr.h"
#include "retdec/llvmir2hll/ir/cast_expr.h"
#include "retdec/llvmir2hll/ir/ext_cast_expr.h"
#include "retdec/llvmir2hll/ir/trunc_cast_expr.h"
#include "retdec/llvmir2hll/ir/global_var_def.h"
#include "retdec/llvmir2hll/analysis/value_analysis.h"
#include "retdec/llvmir2hll/analysis/var_uses_visitor.h"
#include "retdec/llvmir2hll/support/visitors/ordered_all_visitor.h"
#include "retdec/llvmir2hll/ir/if_stmt.h"
#include "retdec/llvmir2hll/ir/return_stmt.h"
#include "retdec/llvmir2hll/ir/switch_stmt.h"
#include "retdec/llvmir2hll/ir/break_stmt.h"
#include "retdec/llvmir2hll/ir/deref_op_expr.h"
#include "retdec/llvmir2hll/graphs/cfg/cfg_builders/non_recursive_cfg_builder.h"
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
struct ProvenSignedScale {
	llvm::BinaryOperator *operation;
	llvm::Value *input;
	unsigned shift;
};

std::optional<ProvenSignedScale> proveSignedScale(llvm::Value &value) {
	auto *scaled = llvm::dyn_cast<llvm::BinaryOperator>(&value);
	if (!scaled || !scaled->getType()->isIntegerTy(32)) return {};
	unsigned shift = 0;
	llvm::Value *input = nullptr;
	if (scaled->getOpcode() == llvm::Instruction::Mul) {
		for (unsigned i = 0; i < 2; ++i) {
			auto *factor = llvm::dyn_cast<llvm::ConstantInt>(scaled->getOperand(i));
			if (!factor) continue;
			if (factor->getValue() == llvm::APInt(32, 0x10000)) shift = 16;
			else if (factor->getValue() == llvm::APInt(32, 0x1000000)) shift = 24;
			else continue;
			input = scaled->getOperand(1 - i);
			break;
		}
	} else if (scaled->getOpcode() == llvm::Instruction::Shl) {
		auto *count = llvm::dyn_cast<llvm::ConstantInt>(scaled->getOperand(1));
		if (!count || (count->getValue() != llvm::APInt(32, 16)
				&& count->getValue() != llvm::APInt(32, 24))) return {};
		shift = unsigned(count->getZExtValue());
		input = scaled->getOperand(0);
	}
	if (!input || !input->getType()->isIntegerTy(32) || llvm::isa<llvm::UndefValue>(input)
			|| scaled->hasNoSignedWrap() || scaled->hasNoUnsignedWrap()) return {};
	return ProvenSignedScale{scaled, input, shift};
}

struct ProvenSignedComparison {
	llvm::ICmpInst *comparison;
	llvm::CmpInst::Predicate predicate;
	llvm::APInt boundary;
};

std::optional<ProvenSignedComparison> proveSignedScaledComparison(
		llvm::ICmpInst &comparison, llvm::Value &scaled, unsigned shift) {
	if (!comparison.getOperand(0)->getType()->isIntegerTy(32)) return {};
	auto predicate = comparison.getPredicate();
	if (predicate != llvm::ICmpInst::ICMP_SLT && predicate != llvm::ICmpInst::ICMP_SGE
			&& predicate != llvm::ICmpInst::ICMP_SGT && predicate != llvm::ICmpInst::ICMP_SLE) return {};
	llvm::ConstantInt *constant = nullptr;
	if (comparison.getOperand(0) == &scaled) {
		constant = llvm::dyn_cast<llvm::ConstantInt>(comparison.getOperand(1));
	} else if (comparison.getOperand(1) == &scaled) {
		constant = llvm::dyn_cast<llvm::ConstantInt>(comparison.getOperand(0));
		predicate = llvm::ICmpInst::getSwappedPredicate(predicate);
	}
	if (!constant) return {};
	llvm::APInt boundary = constant->getValue();
	if (predicate == llvm::ICmpInst::ICMP_SGT || predicate == llvm::ICmpInst::ICMP_SLE) {
		if (boundary.isMaxSignedValue()) return {};
		boundary += llvm::APInt(32, 1);
		predicate = predicate == llvm::ICmpInst::ICMP_SGT
			? llvm::ICmpInst::ICMP_SGE : llvm::ICmpInst::ICMP_SLT;
	}
	if (!(boundary & llvm::APInt::getLowBitsSet(32, shift)).isNullValue()) return {};
	return ProvenSignedComparison{&comparison, predicate, boundary.ashr(shift)};
}

llvm::Value *createSignedView(const ProvenSignedScale &scale, llvm::Instruction &before) {
	auto *narrow = new llvm::TruncInst(scale.input,
		llvm::Type::getIntNTy(before.getContext(), 32 - scale.shift), "", &before);
	return new llvm::SExtInst(narrow, scale.input->getType(), "", &before);
}

bool hasOnlyLocationMetadata(const llvm::Instruction &instruction) {
	llvm::SmallVector<std::pair<unsigned, llvm::MDNode*>, 4> attachments;
	instruction.getAllMetadata(attachments);
	const unsigned address = instruction.getContext().getMDKindID("insn.addr");
	return std::all_of(attachments.begin(), attachments.end(), [&](const auto &attachment) {
		return attachment.first == llvm::LLVMContext::MD_dbg || attachment.first == address;
	});
}

void recoverSharedSignedViews(llvm::Function &function) {
	std::vector<llvm::WeakTrackingVH> roots;
	for (auto &block : function) for (auto &instruction : block)
		if (instruction.getType()->isIntegerTy(32)
				&& (llvm::isa<llvm::BinaryOperator>(instruction)
					|| llvm::isa<llvm::SelectInst>(instruction))) roots.emplace_back(&instruction);
	for (auto &handle : roots) {
		llvm::Value *live = handle;
		auto *root = llvm::dyn_cast_or_null<llvm::Instruction>(live);
		if (!root || !root->getParent() || root->isUsedByMetadata()) continue;
		auto *selection = llvm::dyn_cast<llvm::SelectInst>(root);
		std::vector<ProvenSignedScale> scales;
		if (selection) {
			if (!selection->getCondition()->getType()->isIntegerTy(1)
					|| llvm::isa<llvm::UndefValue>(selection->getCondition())
					|| llvm::isa<llvm::SelectInst>(selection->getCondition())
					|| !hasOnlyLocationMetadata(*selection)) continue;
			for (unsigned i = 1; i < 3; ++i) {
				if (llvm::isa<llvm::ConstantInt>(selection->getOperand(i))) continue;
				auto scale = proveSignedScale(*selection->getOperand(i));
				if (!scale || !scale->operation->hasOneUse()
						|| llvm::isa<llvm::SelectInst>(scale->input)) {
					scales.clear();
					break;
				}
				scales.push_back(*scale);
			}
			if (scales.empty()) continue;
		} else {
			auto scale = proveSignedScale(*root);
			if (!scale || root->hasMetadata() || llvm::isa<llvm::SelectInst>(scale->input)) continue;
			scales.push_back(*scale);
		}
		unsigned shift = scales.front().shift;
		if (std::any_of(scales.begin(), scales.end(), [&](const auto &scale) {
				return scale.shift != shift;
			})) continue;
		if (selection) {
			bool aligned = true;
			for (unsigned i = 1; i < 3; ++i)
				if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(selection->getOperand(i)))
					aligned &= (constant->getValue() & llvm::APInt::getLowBitsSet(32, shift)).isNullValue();
			if (!aligned) continue;
		}
		std::vector<ProvenSignedComparison> comparisons;
		std::vector<llvm::BinaryOperator*> shifts;
		bool supported = true;
		for (auto *user : root->users()) {
			if (auto *comparison = llvm::dyn_cast<llvm::ICmpInst>(user)) {
				auto proof = proveSignedScaledComparison(*comparison, *root, shift);
				if (!proof || comparison->isUsedByMetadata() || !hasOnlyLocationMetadata(*comparison)) {
					supported = false;
					break;
				}
				comparisons.push_back(*proof);
				continue;
			}
			auto *right = llvm::dyn_cast<llvm::BinaryOperator>(user);
			auto *count = right ? llvm::dyn_cast<llvm::ConstantInt>(right->getOperand(1)) : nullptr;
			if (!right || right->getOpcode() != llvm::Instruction::AShr
					|| !right->getType()->isIntegerTy(32) || right->getOperand(0) != root
					|| !count || count->getValue() != llvm::APInt(32, shift)
					|| right->hasMetadata() || right->isUsedByMetadata()) {
				supported = false;
				break;
			}
			shifts.push_back(right);
		}
		if (!supported || comparisons.empty() || shifts.empty()) continue;
		llvm::Value *view = root;
		std::set<llvm::BinaryOperator*> cleanup;
		for (const auto &scale : scales) {
			auto *signedValue = createSignedView(scale, *root);
			if (selection) {
				for (unsigned i = 1; i < 3; ++i)
					if (selection->getOperand(i) == scale.operation) selection->setOperand(i, signedValue);
			} else view = signedValue;
			cleanup.insert(scale.operation);
		}
		if (selection)
			for (unsigned i = 1; i < 3; ++i)
				if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(selection->getOperand(i)))
					selection->setOperand(i, llvm::ConstantInt::get(function.getContext(), constant->getValue().ashr(shift)));
		for (const auto &proof : comparisons) {
			proof.comparison->setOperand(0, view);
			proof.comparison->setOperand(1, llvm::ConstantInt::get(function.getContext(), proof.boundary));
			proof.comparison->setPredicate(proof.predicate);
		}
		for (auto *right : shifts) {
			right->replaceAllUsesWith(view);
			right->eraseFromParent();
		}
		for (auto *operation : cleanup)
			if (operation->use_empty() && !operation->hasMetadata() && !operation->isUsedByMetadata())
				operation->eraseFromParent();
	}
}

void recoverSignedScaledPredicates(llvm::Function &function) {
	for (auto &block : function) for (auto &instruction : block) {
		auto *comparison = llvm::dyn_cast<llvm::ICmpInst>(&instruction);
		if (!comparison) continue;
		unsigned operand = llvm::isa<llvm::ConstantInt>(comparison->getOperand(1)) ? 0 : 1;
		auto scale = proveSignedScale(*comparison->getOperand(operand));
		if (!scale) continue;
		auto proof = proveSignedScaledComparison(*comparison, *scale->operation, scale->shift);
		if (!proof) continue;
		comparison->setOperand(0, createSignedView(*scale, *comparison));
		comparison->setOperand(1, llvm::ConstantInt::get(function.getContext(), proof->boundary));
		comparison->setPredicate(proof->predicate);
		if (scale->operation->use_empty()) scale->operation->eraseFromParent();
	}
}

struct ProvenUnsignedQuotient {
	llvm::Value *unsignedInput;
	llvm::BinaryOperator *wideShift;
	uint32_t divisor;
	unsigned discardedLowBits;
};

std::optional<ProvenUnsignedQuotient> proveUnsignedQuotient(
		llvm::Value &value, unsigned discardedLowBits = 0) {
	auto *shift = llvm::dyn_cast<llvm::BinaryOperator>(&value);
	if (!shift || !shift->getType()->isIntegerTy(64)
			|| shift->getOpcode() != llvm::Instruction::LShr || shift->isExact()) return {};
	auto *count = llvm::dyn_cast<llvm::ConstantInt>(shift->getOperand(1));
	auto *product = llvm::dyn_cast<llvm::BinaryOperator>(shift->getOperand(0));
	if (!count || count->getValue().uge(64) || !product
			|| product->getOpcode() != llvm::Instruction::Mul) return {};
	unsigned exponent = unsigned(count->getZExtValue()) + discardedLowBits;
	if (discardedLowBits >= 32 || exponent < 32 || exponent >= 64) return {};
	llvm::ConstantInt *factor = nullptr;
	llvm::ZExtInst *extend = nullptr;
	for (unsigned i = 0; i < 2; ++i) {
		factor = llvm::dyn_cast<llvm::ConstantInt>(product->getOperand(i));
		extend = llvm::dyn_cast<llvm::ZExtInst>(product->getOperand(1 - i));
		if (factor && extend) break;
	}
	if (!factor || !extend || factor->isZero() || factor->getValue().getActiveBits() > 32
			|| !extend->getSrcTy()->isIntegerTy()
			|| extend->getSrcTy()->getIntegerBitWidth() > 32) return {};
	const llvm::APInt maximum(128, UINT32_MAX);
	const llvm::APInt scale = llvm::APInt(128, 1).shl(exponent);
	const llvm::APInt multiplier = factor->getValue().zext(128);
	const llvm::APInt maximumProduct = (llvm::APInt(128, 1).shl(
		extend->getSrcTy()->getIntegerBitWidth()) - 1) * multiplier;
	if ((product->hasNoUnsignedWrap() && maximumProduct.ugt(llvm::APInt(128, UINT64_MAX)))
			|| (product->hasNoSignedWrap() && maximumProduct.ugt(llvm::APInt(128, INT64_MAX)))) return {};
	const llvm::APInt divisor = (scale + multiplier - 1).udiv(multiplier);
	if (divisor.isNullValue() || divisor.ugt(maximum)) return {};
	const llvm::APInt error = multiplier * divisor - scale;
	auto exactAt = [&](const llvm::APInt &quotient, const llvm::APInt &remainder) {
		return (quotient * error + remainder * multiplier).ult(scale);
	};
	const llvm::APInt fullBuckets = (maximum + 1).udiv(divisor);
	if (!fullBuckets.isNullValue() && !exactAt(fullBuckets - 1, divisor - 1)) return {};
	if (!exactAt(maximum.udiv(divisor), maximum.urem(divisor))) return {};
	return ProvenUnsignedQuotient{extend->getOperand(0), shift,
		uint32_t(divisor.getZExtValue()), discardedLowBits};
}

bool collectLow32Slice(llvm::Value &value, std::optional<ProvenUnsignedQuotient> &proof,
		std::vector<llvm::Instruction*> &slice, std::set<llvm::Value*> &seen) {
	if (!value.getType()->isIntegerTy()) return false;
	if (value.getType()->getIntegerBitWidth() <= 32 || llvm::isa<llvm::ConstantInt>(value)) return true;
	if (!seen.insert(&value).second) return true;
	if (auto quotient = proveUnsignedQuotient(value)) {
		if (proof && proof->wideShift != quotient->wideShift) return false;
		proof = quotient;
		slice.push_back(quotient->wideShift);
		return true;
	}
	if (auto *cast = llvm::dyn_cast<llvm::CastInst>(&value)) {
		if ((cast->getOpcode() != llvm::Instruction::Trunc
				&& cast->getOpcode() != llvm::Instruction::ZExt
				&& cast->getOpcode() != llvm::Instruction::SExt)
				|| !collectLow32Slice(*cast->getOperand(0), proof, slice, seen)) return false;
		slice.push_back(cast);
		return true;
	}
	auto *operation = llvm::dyn_cast<llvm::BinaryOperator>(&value);
	if (!operation) return false;
	switch (operation->getOpcode()) {
		case llvm::Instruction::Add:
		case llvm::Instruction::Sub:
		case llvm::Instruction::Mul:
		case llvm::Instruction::And:
		case llvm::Instruction::Or:
		case llvm::Instruction::Xor:
			break;
		case llvm::Instruction::Shl: {
			auto *count = llvm::dyn_cast<llvm::ConstantInt>(operation->getOperand(1));
			if (!count || count->getValue().uge(32)) return false;
			break;
		}
		default:
			return false;
	}
	if (auto *overflow = llvm::dyn_cast<llvm::OverflowingBinaryOperator>(operation))
		if (overflow->hasNoUnsignedWrap() || overflow->hasNoSignedWrap()) return false;
	for (auto &operand : operation->operands())
		if (!collectLow32Slice(*operand, proof, slice, seen)) return false;
	slice.push_back(operation);
	return true;
}

std::optional<ProvenUnsignedQuotient> proveMaskedUnsignedQuotient(
		llvm::Value &value, unsigned sinkWidth, uint32_t &mask,
		std::vector<llvm::Instruction*> &slice) {
	auto *operation = llvm::dyn_cast<llvm::BinaryOperator>(&value);
	if (!operation || operation->getOpcode() != llvm::Instruction::And
			|| !operation->getType()->isIntegerTy()) return {};
	llvm::ConstantInt *constant = nullptr;
	llvm::Value *shifted = nullptr;
	for (unsigned i = 0; i < 2; ++i)
		if ((constant = llvm::dyn_cast<llvm::ConstantInt>(operation->getOperand(i)))) {
			shifted = operation->getOperand(1 - i);
			break;
		}
	if (!constant || constant->isZero() || constant->getValue().getActiveBits() > sinkWidth) return {};
	unsigned observedBits = constant->getValue().getActiveBits();
	mask = uint32_t(constant->getZExtValue());
	unsigned discardedLowBits = constant->getValue().countTrailingZeros();
	if (discardedLowBits >= 32) return {};
	while (auto *cast = llvm::dyn_cast<llvm::CastInst>(shifted)) {
		if ((cast->getOpcode() != llvm::Instruction::Trunc
				&& cast->getOpcode() != llvm::Instruction::ZExt
				&& cast->getOpcode() != llvm::Instruction::SExt)
				|| !cast->getSrcTy()->isIntegerTy() || !cast->getDestTy()->isIntegerTy()
				|| observedBits > cast->getSrcTy()->getIntegerBitWidth()
				|| observedBits > cast->getDestTy()->getIntegerBitWidth()) return {};
		slice.push_back(cast);
		shifted = cast->getOperand(0);
	}
	auto proof = proveUnsignedQuotient(*shifted, discardedLowBits);
	if (!proof) return {};
	slice.push_back(proof->wideShift);
	slice.push_back(operation);
	return proof;
}

llvm::Value *rebuildLow32(llvm::Value &value, const ProvenUnsignedQuotient &proof,
		const std::vector<llvm::Instruction*> &slice, llvm::IRBuilder<> &builder) {
	std::map<llvm::Value*, llvm::Value*> lowered;
	auto low32 = [&](llvm::Value *operand) -> llvm::Value* {
		auto found = lowered.find(operand);
		if (found != lowered.end()) return found->second;
		if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(operand))
			return builder.getInt32(constant->getValue().zextOrTrunc(32).getZExtValue());
		return builder.CreateZExtOrTrunc(operand, builder.getInt32Ty());
	};
	auto *input = builder.CreateZExtOrTrunc(proof.unsignedInput, builder.getInt32Ty());
	lowered[proof.wideShift] = builder.Insert(llvm::BinaryOperator::CreateUDiv(
		input, builder.getInt32(proof.divisor)));
	for (auto *instruction : slice) {
		if (instruction == proof.wideShift) continue;
		llvm::Value *replacement = nullptr;
		if (auto *cast = llvm::dyn_cast<llvm::CastInst>(instruction)) {
			auto *operand = cast->getOperand(0);
			replacement = cast->getOpcode() == llvm::Instruction::SExt
				&& operand->getType()->getIntegerBitWidth() < 32
				? builder.CreateSExt(operand, builder.getInt32Ty()) : low32(operand);
		} else {
			auto *operation = llvm::cast<llvm::BinaryOperator>(instruction);
			replacement = builder.Insert(llvm::BinaryOperator::Create(operation->getOpcode(),
				low32(operation->getOperand(0)), low32(operation->getOperand(1))));
		}
		if (auto *replacementInstruction = llvm::dyn_cast<llvm::Instruction>(replacement))
			if (replacement != instruction->getOperand(0)) {
				replacementInstruction->setMetadata("insn.addr", instruction->getMetadata("insn.addr"));
				replacementInstruction->setDebugLoc(instruction->getDebugLoc());
			}
		lowered[instruction] = replacement;
	}
	return low32(&value);
}

bool recoverUnsignedReciprocalSinks(llvm::Function &function) {
	std::vector<llvm::WeakTrackingVH> sinks;
	for (auto &block : function) for (auto &instruction : block)
		if (instruction.getType()->isIntegerTy()
				&& instruction.getType()->getIntegerBitWidth() <= 32
				&& (llvm::isa<llvm::TruncInst>(instruction)
					|| instruction.getOpcode() == llvm::Instruction::And)) sinks.emplace_back(&instruction);
	bool changed = false;
	for (auto &handle : sinks) {
		llvm::Value *live = handle;
		auto *sink = llvm::dyn_cast_or_null<llvm::Instruction>(live);
		if (!sink || !sink->getParent()) continue;
		auto *trunc = llvm::dyn_cast<llvm::TruncInst>(sink);
		llvm::Value *expression = trunc ? trunc->getOperand(0) : sink;
		std::vector<llvm::Instruction*> slice;
		uint32_t mask = 0;
		auto proof = proveMaskedUnsignedQuotient(*expression,
			sink->getType()->getIntegerBitWidth(), mask, slice);
		bool masked = bool(proof);
		if (!masked) {
			slice.clear();
			std::set<llvm::Value*> seen;
			if (!trunc || !collectLow32Slice(*expression, proof, slice, seen) || !proof) continue;
		}
		llvm::IRBuilder<> builder(sink);
		llvm::Value *replacement = nullptr;
		if (masked) {
			auto *input = builder.CreateZExtOrTrunc(proof->unsignedInput, builder.getInt32Ty());
			replacement = builder.Insert(llvm::BinaryOperator::CreateUDiv(input, builder.getInt32(proof->divisor)));
			if (proof->discardedLowBits)
				replacement = builder.Insert(llvm::BinaryOperator::CreateShl(
					replacement, builder.getInt32(proof->discardedLowBits)));
			replacement = builder.Insert(llvm::BinaryOperator::CreateAnd(replacement, builder.getInt32(mask)));
		} else replacement = rebuildLow32(*expression, *proof, slice, builder);
		replacement = builder.CreateTruncOrBitCast(replacement, sink->getType());
		if (auto *instruction = llvm::dyn_cast<llvm::Instruction>(replacement)) {
			instruction->copyMetadata(*sink);
			instruction->setDebugLoc(sink->getDebugLoc());
		}
		auto *product = llvm::cast<llvm::BinaryOperator>(proof->wideShift->getOperand(0));
		slice.push_back(product);
		for (auto &operand : product->operands())
			if (auto *extend = llvm::dyn_cast<llvm::ZExtInst>(operand)) slice.push_back(extend);
		std::vector<llvm::WeakTrackingVH> cleanup;
		for (auto *instruction : slice)
			if (instruction != sink) cleanup.emplace_back(instruction);
		sink->replaceAllUsesWith(replacement);
		sink->eraseFromParent();
		bool deleted = true;
		while (deleted) {
			deleted = false;
			for (auto &candidate : cleanup) {
				llvm::Value *value = candidate;
				auto *instruction = llvm::dyn_cast_or_null<llvm::Instruction>(value);
				if (instruction && llvm::isInstructionTriviallyDead(instruction)) {
					instruction->eraseFromParent();
					deleted = true;
				}
			}
		}
		changed = true;
	}
	return changed;
}

namespace original_expression {
using Expression = common::OriginalSourceExpression;
using Disposition = common::ReturnDisposition;
template<typename T, typename Predicate>
inline const T* unique(const std::vector<T>& rows, Predicate matches) {
	const T* result = nullptr;
	for (const auto& row : rows) if (matches(row)) {
		if (result) return nullptr;
		result = &row;
	}
	return result;
}

inline std::optional<Expression> bind(const common::Function& function, uint64_t rightPc) {
	if (!function.returnDisposition || !function.originalCallSummary
			|| function.returnDisposition->kind != Disposition::Kind::Value
			|| !function.originalCallSummary->declaration.isComplete()) return {};
	const auto& evidence = function.returnDisposition->evidence;
	if (!evidence.decodeComplete || !evidence.analysisComplete
			|| evidence.symbol != function.getName()) return {};
	auto instruction = [&](uint64_t pc) {
		return unique(evidence.instructions, [&](const auto& row) { return row.pc == pc; });
	};
	const auto* right = instruction(rightPc);
	if (!right || right->word >> 26 || ((right->word >> 21) & 31)
			|| (right->word & 63) != 3) return {};
	unsigned shift = (right->word >> 6) & 31;
	if (shift != 16 && shift != 24) return {};
	const auto* rightDef = unique(evidence.definitions, [&](const auto& row) {
		return row.pc == rightPc && row.reg == ((right->word >> 11) & 31);
	});
	if (!rightDef || rightDef->inputs.size() != 1) return {};
	const auto* leftDef = unique(evidence.definitions, [&](const auto& row) {
		return row.id == rightDef->inputs.front();
	});
	if (!leftDef || leftDef->pc >= rightPc || leftDef->pc < evidence.start
			|| rightPc >= evidence.end) return {};
	const auto* left = instruction(leftDef->pc);
	if (!left || left->word >> 26 || ((left->word >> 21) & 31)
			|| (left->word & 63) || ((left->word >> 6) & 31) != shift
			|| ((left->word >> 11) & 31) != leftDef->reg
			|| ((right->word >> 16) & 31) != leftDef->reg
			|| !leftDef->reg || !rightDef->reg) return {};
	unsigned entry = (left->word >> 16) & 31;
	if (entry < 4 || entry > 7 || !leftDef->inputs.empty()
			|| leftDef->entries != std::vector<unsigned>{entry}
			|| leftDef->formals != std::vector<unsigned>{entry}
			|| rightDef->entries != leftDef->entries || rightDef->formals != leftDef->formals
			|| std::count(function.originalCallSummary->parameterRegisters.begin(),
				function.originalCallSummary->parameterRegisters.end(), entry) != 1) return {};
	for (const auto* definition : {leftDef, rightDef})
		if (definition->width != 32 || definition->delayed || !definition->bad.empty()
				|| definition->origin != "instruction" || definition->operation != "shift-immediate") return {};
	for (const auto* row : {left, right}) {
		unsigned destination = (row->word >> 11) & 31;
		if (row->owner != evidence.symbol || row->bytes != 4 || !row->mapped || row->undef
				|| std::find(row->fullWidthRegisters.begin(), row->fullWidthRegisters.end(), destination)
					== row->fullWidthRegisters.end()) return {};
	}
	for (uint64_t pc = left->pc; pc < rightPc; pc += 4) {
		const auto* edge = unique(evidence.edges, [&](const auto& row) { return row.from == pc; });
		if (!edge || edge->to != pc + 4 || edge->delayOwner || edge->kind != "fallthrough") return {};
	}
	for (const auto& edge : evidence.edges)
		if (left->pc <= edge.to && edge.to <= rightPc
				&& (edge.delayOwner || (edge.to > left->pc && edge.from + 4 != edge.to))) return {};
	for (const auto& call : evidence.calls)
		if (left->pc <= call.pc && call.pc <= rightPc) return {};
	return Expression{left->pc, rightPc, leftDef->id, rightDef->id, entry, 32 - shift};
}


bool hasPc(const llvm::Instruction& instruction, uint64_t pc) {
	auto* node = instruction.getMetadata("insn.addr");
	auto* value = node && node->getNumOperands() == 1
		? llvm::mdconst::dyn_extract<llvm::ConstantInt>(node->getOperand(0)) : nullptr;
	return value && value->getType()->isIntegerTy(64) && value->getZExtValue() == pc;
}

llvm::Argument* entryFor(llvm::Instruction& root, const Expression& expression,
		const common::Function& source) {
	if (!root.getType()->isIntegerTy(32) || !hasPc(root, expression.rightPc)) return nullptr;
	llvm::Value* input = nullptr;
	if (auto* extend = llvm::dyn_cast<llvm::SExtInst>(&root)) {
		auto* trunc = llvm::dyn_cast<llvm::TruncInst>(extend->getOperand(0));
		if (trunc && trunc->getType()->isIntegerTy(expression.viewWidth)
				&& trunc->getFunction() == root.getFunction()) input = trunc->getOperand(0);
	} else if (auto* right = llvm::dyn_cast<llvm::BinaryOperator>(&root)) {
		unsigned amount = 32 - expression.viewWidth;
		auto* count = llvm::dyn_cast<llvm::ConstantInt>(right->getOperand(1));
		auto* left = llvm::dyn_cast<llvm::BinaryOperator>(right->getOperand(0));
		if (right->getOpcode() != llvm::Instruction::AShr || !count
				|| count->getZExtValue() != amount || !left || !left->getType()->isIntegerTy(32)
				|| left->getFunction() != root.getFunction()
				|| (left->getOpcode() != llvm::Instruction::Shl && left->getOpcode() != llvm::Instruction::Mul)
				|| left->hasNoSignedWrap() || left->hasNoUnsignedWrap()) return nullptr;
		if (left->getOpcode() == llvm::Instruction::Shl) {
			auto* shift = llvm::dyn_cast<llvm::ConstantInt>(left->getOperand(1));
			if (shift && shift->getZExtValue() == amount) input = left->getOperand(0);
		} else if (left->getOpcode() == llvm::Instruction::Mul) {
			for (unsigned i = 0; i < 2; ++i)
				if (auto* factor = llvm::dyn_cast<llvm::ConstantInt>(left->getOperand(i)))
					if (factor->getZExtValue() == (uint64_t(1) << amount)) input = left->getOperand(1 - i);
		}
	}
	auto* entry = llvm::dyn_cast_or_null<llvm::Argument>(input);
	if (!entry || !entry->getType()->isIntegerTy(32) || entry->getParent() != root.getFunction()) return nullptr;
	const auto& registers = source.originalCallSummary->parameterRegisters;
	return registers.size() == entry->getParent()->arg_size() && entry->getArgNo() < registers.size()
		&& registers[entry->getArgNo()] == expression.entryRegister ? entry : nullptr;
}

void recover(llvm::Function& function, common::Function& source,
		const std::optional<common::OriginalSourceForm>& form) {
	source.originalSourceExpressions.clear();
	if (form) {
		source.originalSourceForms = std::vector<common::OriginalSourceFormApplication>{};
		source.originalSourceFormFailures.clear();
	}
	if (!source.returnDisposition || !source.originalCallSummary) return;
	auto& evidence = source.returnDisposition->evidence;
	auto& obligations = evidence.obligations;
	obligations.erase(std::remove_if(obligations.begin(), obligations.end(), [](const auto& row) {
		return row.domain == "source-expression" && row.reason == "applied-sign-extraction-origin-unresolved";
	}), obligations.end());
	for (const auto& row : evidence.instructions) {
		auto expression = bind(source, row.pc);
		if (!expression) continue;
		if (form) {
			if (source.originalSourceExpressions.size() >= Disposition::RowLimit)
				throw std::runtime_error("original-expression-witnesses-exhausted");
			source.originalSourceForms->push_back({unsigned(source.originalSourceExpressions.size()),
				common::SourceFormUnresolved{"source-form-census-not-run"}});
			source.originalSourceExpressions.push_back(*expression);
			if (obligations.size() >= Disposition::RowLimit)
				throw std::runtime_error("original-expression-obligations-exhausted");
			obligations.push_back({expression->rightPc, "source-expression", "source-form-census-not-run"});
		}
		llvm::Instruction* root = nullptr;
		llvm::Argument* entry = nullptr;
		unsigned matches = 0;
		for (auto& block : function) for (auto& instruction : block)
			if (auto* argument = entryFor(instruction, *expression, source)) {
				root = &instruction;
				entry = argument;
				++matches;
			}
		if (matches == 1) {
			if (!llvm::isa<llvm::SExtInst>(root)) {
				auto* trunc = new llvm::TruncInst(entry,
					llvm::IntegerType::get(function.getContext(), expression->viewWidth), "", root);
				auto* extend = new llvm::SExtInst(trunc, root->getType(), "", root);
				extend->setMetadata("insn.addr", root->getMetadata("insn.addr"));
				if (entryFor(*extend, *expression, source) != entry)
					throw std::runtime_error("original-expression-replacement-unbound");
				root->replaceAllUsesWith(extend);
				root->eraseFromParent();
				root = extend;
			}
			if (form) {
				auto& context = function.getContext();
				auto number = [&](uint64_t value) -> llvm::Metadata* {
					return llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(
						llvm::Type::getInt64Ty(context), value));
				};
				root->setMetadata("retdec.original.source-expression", llvm::MDNode::get(context, {
					llvm::MDString::get(context, source.getName()), number(expression->leftPc),
					number(expression->rightPc), number(expression->leftDefinition),
					number(expression->rightDefinition), number(expression->entryRegister),
					number(expression->viewWidth), number(entry->getArgNo())}));
			} else source.originalSourceExpressions.push_back(*expression);
		} else {
			if (obligations.size() >= Disposition::RowLimit)
				throw std::runtime_error("original-expression-obligations-exhausted");
			obligations.push_back({expression->rightPc, "source-expression",
				"applied-sign-extraction-origin-unresolved"});
		}
	}
}
}

void restoreSignedNarrowLoadEqualities(llvm::Function& function, const common::Function& source) {
	if (source.getName() != function.getName().str() || !source.returnDisposition
			|| !source.originalCallSummary || !source.getStart().isDefined()
			|| !source.getEnd().isDefined()) return;
	const auto& evidence = source.returnDisposition->evidence;
	const auto& summary = *source.originalCallSummary;
	if (evidence.symbol != source.getName() || summary.function.empty()
			|| !evidence.decodeComplete || !evidence.analysisComplete
			|| evidence.start != source.getStart().getValue()
			|| evidence.end != source.getEnd().getValue() || evidence.start >= evidence.end
			|| evidence.end > uint64_t(UINT32_MAX) + 1 || evidence.start % 4 || evidence.end % 4) return;
	struct SignedLoadEquality {
		llvm::ICmpInst* comparison;
		llvm::LoadInst* load;
		llvm::ConstantInt* constant;
		unsigned loadOperand;
	};
	std::vector<SignedLoadEquality> matches;
	auto cleanDefinition = [](const auto& row) {
		return row.width == 32 && row.origin == "instruction" && row.bad.empty()
			&& row.entries.empty() && row.formals.empty() && !row.equalEntry
			&& row.callee.empty() && !row.available && !row.delay
			&& row.calleeDefinitions.empty() && row.substitutedEntries.empty();
	};
	for (auto& block : function) for (auto& instruction : block) {
		auto* comparison = llvm::dyn_cast<llvm::ICmpInst>(&instruction);
		if (!comparison || (comparison->getPredicate() != llvm::CmpInst::ICMP_EQ
				&& comparison->getPredicate() != llvm::CmpInst::ICMP_NE)) continue;
		llvm::LoadInst* load = nullptr;
		llvm::ConstantInt* constant = nullptr;
		unsigned loadOperand = 0;
		for (; loadOperand < 2; ++loadOperand) {
			load = llvm::dyn_cast<llvm::LoadInst>(comparison->getOperand(loadOperand));
			constant = llvm::dyn_cast<llvm::ConstantInt>(comparison->getOperand(1 - loadOperand));
			if (load && constant) break;
		}
		if (loadOperand == 2 || (!load->getType()->isIntegerTy(8) && !load->getType()->isIntegerTy(16))
				|| constant->getType() != load->getType() || constant->getValue().isNegative()
				|| constant->getValue().getActiveBits() >= load->getType()->getIntegerBitWidth()
				|| !load->hasOneUse() || load->getParent() != &block || load->isVolatile()
				|| load->isAtomic() || load->getPointerOperand()->getType()->getPointerAddressSpace()) continue;
		bool precedes = false;
		for (auto& prior : block) {
			if (&prior == comparison) break;
			if (&prior == load) { precedes = true; break; }
		}
		if (!precedes) continue;
		const auto* row = original_expression::unique(evidence.instructions, [&](const auto& candidate) {
			return original_expression::hasPc(*load, candidate.pc);
		});
		unsigned width = load->getType()->getIntegerBitWidth();
		if (!row || row->owner != evidence.symbol || row->bytes != 4 || !row->mapped || row->undef
				|| row->pc < evidence.start || row->pc >= evidence.end || row->pc % 4
				|| row->word >> 26 != (width == 8 ? 32u : 33u)) continue;
		unsigned survivingLoads = 0;
		for (auto& candidateBlock : function) for (auto& candidate : candidateBlock)
			if (llvm::isa<llvm::LoadInst>(candidate) && original_expression::hasPc(candidate, row->pc)) ++survivingLoads;
		unsigned destination = (row->word >> 16) & 31, baseRegister = (row->word >> 21) & 31;
		if (survivingLoads != 1 || !destination || !baseRegister
				|| std::count(row->fullWidthRegisters.begin(), row->fullWidthRegisters.end(), destination) != 1) continue;
		const auto* definition = original_expression::unique(evidence.definitions,
			[&](const auto& candidate) { return candidate.pc == row->pc; });
		const auto* access = original_expression::unique(summary.accesses,
			[&](const auto& candidate) { return candidate.pc == row->pc; });
		if (!definition || !cleanDefinition(*definition) || definition->reg != destination
				|| definition->operation != "full-register-load" || !definition->delayed
				|| definition->constant || !definition->equalityEvidence.empty()
				|| original_expression::unique(evidence.definitions, [&](const auto& candidate) {
					return candidate.id == definition->id;
				}) != definition || !access || access->kind != "read" || access->extension != "sign"
				|| access->width != width || !access->delayed || !access->addressEntries.empty()
				|| !access->valueDefinitions.empty() || !access->valueEntries.empty()
				|| access->addressDefinitions.size() != 1 || definition->inputs != access->addressDefinitions) continue;
		const auto* base = original_expression::unique(evidence.definitions, [&](const auto& candidate) {
			return candidate.id == access->addressDefinitions.front();
		});
		if (!base || !cleanDefinition(*base) || base->reg != baseRegister || base->operation != "lui"
				|| base->delayed || !base->inputs.empty() || !base->constant
				|| base->pc < evidence.start || base->pc >= row->pc || row->pc - base->pc != 4
				|| base->equalityEvidence != std::vector<uint64_t>{base->pc}
				|| original_expression::unique(evidence.definitions, [&](const auto& candidate) {
					return candidate.pc == base->pc;
				}) != base) continue;
		const auto* lui = original_expression::unique(evidence.instructions,
			[&](const auto& candidate) { return candidate.pc == base->pc; });
		if (!lui || lui->owner != evidence.symbol || lui->bytes != 4 || !lui->mapped || lui->undef
				|| lui->word >> 26 != 15 || ((lui->word >> 21) & 31)
				|| ((lui->word >> 16) & 31) != baseRegister
				|| std::count(lui->fullWidthRegisters.begin(), lui->fullWidthRegisters.end(), baseRegister) != 1
				|| *base->constant != (lui->word & 0xffff) << 16) continue;
		const auto* outgoing = original_expression::unique(evidence.edges,
			[&](const auto& candidate) { return candidate.from == lui->pc; });
		const auto* incoming = original_expression::unique(evidence.edges,
			[&](const auto& candidate) { return candidate.to == row->pc; });
		if (!outgoing || incoming != outgoing || outgoing->to != row->pc
				|| outgoing->delayOwner || outgoing->kind != "fallthrough") continue;
		auto* pointer = llvm::dyn_cast<llvm::Operator>(load->getPointerOperand());
		auto* address = pointer && pointer->getOpcode() == llvm::Instruction::IntToPtr
			? llvm::dyn_cast<llvm::ConstantInt>(pointer->getOperand(0)) : nullptr;
		uint32_t expectedAddress = *base->constant + uint32_t(int32_t(int16_t(row->word & 0xffff)));
		if (!address || !address->getType()->isIntegerTy(32) || address->getZExtValue() != expectedAddress) continue;
		matches.push_back({comparison, load, constant, loadOperand});
	}
	for (const auto& match : matches) {
		auto* type = llvm::Type::getInt32Ty(function.getContext());
		auto* extend = new llvm::SExtInst(match.load, type, "", match.comparison);
		extend->setMetadata("insn.addr", match.load->getMetadata("insn.addr"));
		extend->setDebugLoc(match.load->getDebugLoc());
		auto* constant = llvm::ConstantInt::get(type, match.constant->getZExtValue());
		auto* comparison = new llvm::ICmpInst(match.comparison, match.comparison->getPredicate(),
			match.loadOperand ? static_cast<llvm::Value*>(constant) : extend,
			match.loadOperand ? static_cast<llvm::Value*>(extend) : constant);
		comparison->copyMetadata(*match.comparison);
		comparison->setDebugLoc(match.comparison->getDebugLoc());
		comparison->takeName(match.comparison);
		match.comparison->replaceAllUsesWith(comparison);
		match.comparison->eraseFromParent();
	}
}

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

struct ProvenScalarReturnMerge {
	ShPtr<Variable> source, result;
	ShPtr<VarDefStmt> sourceDeclaration;
	ShPtr<Statement> sourceInitialization, resultInitialization;
	ShPtr<AssignStmt> update, copy;
	ShPtr<SwitchStmt> branch;
	ShPtr<ReturnStmt> exit;
};

class ScalarReturnMergeRecovery final : public FuncOptimizer {
public:
	explicit ScalarReturnMergeRecovery(ShPtr<Module> module) : FuncOptimizer(module) {}
	std::string getId() const override { return "ScalarReturnMergeRecovery"; }
private:
	bool hasExtraction = false;
	ShPtr<ValueAnalysis> values;

	void visit(ShPtr<ExtCastExpr> expression) override {
		hasExtraction = hasExtraction || expression->getOriginalExtraction();
		FuncOptimizer::visit(expression);
	}
	void visit(ShPtr<TruncCastExpr> expression) override {
		hasExtraction = hasExtraction || expression->getOriginalExtraction();
		FuncOptimizer::visit(expression);
	}
	void runOnFunction(ShPtr<Function> function) override {
		if (!function->getBody()) return;
		hasExtraction = false;
		FuncOptimizer::runOnFunction(function);
		if (hasExtraction) return;
		values = ValueAnalysis::create(SimpleAliasAnalysis::create(), false);
		values->initAliasAnalysis(module);
		if (auto merge = prove()) {
			merge->update->setLhs(merge->result);
			Statement::removeStatementButKeepDebugComment(merge->sourceInitialization);
			if (merge->sourceDeclaration != merge->sourceInitialization)
				Statement::removeStatementButKeepDebugComment(merge->sourceDeclaration);
			Statement::removeStatementButKeepDebugComment(merge->copy);
			currFunc->removeLocalVar(merge->source);
		}
	}

	bool local(ShPtr<Variable> variable) {
		return variable && currFunc->hasLocalVar(variable) && !variable->isExternal()
			&& !variable->isVolatile() && isa<IntType>(variable->getType())
			&& !variable->hasMetadata() && !values->mayBePointed(variable)
			&& !module->hasAssignedDebugName(variable)
			&& module->getDebugNameForLocalVar(currFunc, variable).empty();
	}

	std::optional<ProvenScalarReturnMerge> prove() {
		StmtSet all;
		StmtVector prefix;
		ShPtr<SwitchStmt> branch;
		ShPtr<ReturnStmt> exit;
		for (auto statement = currFunc->getBody(); statement; statement = statement->getSuccessor()) {
			if (!all.insert(statement).second || statement->getParent()
					|| statement->hasLabel() || statement->isGotoTarget()
					|| values->getValueData(statement)->hasCalls()) return {};
			if (isa<EmptyStmt>(statement)) continue;
			if (exit) return {};
			if (branch) {
				exit = cast<ReturnStmt>(statement);
				if (!exit) return {};
			} else if (auto candidate = cast<SwitchStmt>(statement)) branch = candidate;
			else if (isa<AssignStmt>(statement) || isa<VarDefStmt>(statement)) prefix.push_back(statement);
			else return {};
		}
		if (!branch || !exit || prefix.size() < 2) return {};
		std::vector<StmtVector> clauses;
		unsigned defaults = 0;
		for (auto clause = branch->clause_begin(); clause != branch->clause_end(); ++clause) {
			if (!clause->first) ++defaults;
			else if (!isa<ConstInt>(clause->first)) return {};
			StmtVector body;
			for (auto statement = clause->second; statement; statement = statement->getSuccessor()) {
				if (!all.insert(statement).second || statement->getParent() != branch
						|| statement->hasLabel() || statement->isGotoTarget()
						|| values->getValueData(statement)->hasCalls()) return {};
				if (isa<EmptyStmt>(statement)) continue;
				if ((!body.empty() && isa<BreakStmt>(body.back()))
						|| (!isa<AssignStmt>(statement) && !isa<BreakStmt>(statement))) return {};
				body.push_back(statement);
			}
			if (body.empty()) return {};
			clauses.push_back(std::move(body));
		}
		if (defaults > 1 || clauses.size() < 2) return {};
		auto uses = VarUsesVisitor::create(values, false);
		for (std::size_t i = 0; i + 1 < clauses.size(); ++i) {
			if (clauses[i].size() != 1 || !isa<BreakStmt>(clauses[i + 1].back())) continue;
			auto update = cast<AssignStmt>(clauses[i].front());
			auto copy = cast<AssignStmt>(clauses[i + 1].front());
			if (!update || !copy) continue;
			auto source = cast<Variable>(copy->getRhs());
			auto result = cast<Variable>(copy->getLhs());
			if (source == result || !local(source) || !local(result)
					|| !source->getType()->isEqualTo(result->getType())
					|| update->getLhs() != source || exit->getRetVal() != result) continue;
			ShPtr<Statement> sourceInitialization, resultInitialization;
			for (std::size_t j = prefix.size() - 2; j < prefix.size(); ++j) {
				if (getLhs(prefix[j]) == source) sourceInitialization = prefix[j];
				if (getLhs(prefix[j]) == result) resultInitialization = prefix[j];
			}
			if (!sourceInitialization || !resultInitialization) continue;
			auto initial = cast<ConstInt>(getRhs(sourceInitialization));
			auto final = cast<ConstInt>(getRhs(resultInitialization));
			if (!initial || !final || !initial->isEqualTo(final)
					|| !initial->getType()->isEqualTo(source->getType())
					|| !final->getType()->isEqualTo(result->getType())
					|| initial->hasMetadata() || final->hasMetadata()) continue;
			ShPtr<VarDefStmt> sourceDeclaration, resultDeclaration;
			bool valid = true;
			for (const auto& statement : prefix) {
				auto declaration = cast<VarDefStmt>(statement);
				if (!declaration) continue;
				if (declaration->getVar() == source) {
					if (sourceDeclaration || (declaration->getInitializer() && declaration != sourceInitialization)) valid = false;
					sourceDeclaration = declaration;
				}
				if (declaration->getVar() == result) {
					if (resultDeclaration || (declaration->getInitializer() && declaration != resultInitialization)) valid = false;
					resultDeclaration = declaration;
				}
			}
			if (!valid || !sourceDeclaration || !resultDeclaration) continue;
			StmtSet sourceAccesses{sourceDeclaration, sourceInitialization, update, copy};
			StmtSet resultAccesses{resultDeclaration, resultInitialization, copy, exit};
			StmtSet resultReads{exit};
			for (std::size_t j = 1; j + 1 < clauses[i + 1].size(); ++j) {
				auto store = cast<AssignStmt>(clauses[i + 1][j]);
				if (values->getValueData(store)->isDirRead(result)) {
					if (!isa<DerefOpExpr>(store->getLhs())) valid = false;
					resultAccesses.insert(store);
					resultReads.insert(store);
				}
			}
			auto sourceUses = uses->getUses(source, currFunc);
			auto resultUses = uses->getUses(result, currFunc);
			if (!valid || sourceUses->dirUses != sourceAccesses || resultUses->dirUses != resultAccesses
					|| !sourceUses->indirUses.empty() || !resultUses->indirUses.empty()) continue;
			for (const auto& statement : all) {
				auto accesses = values->getValueData(statement);
				if ((accesses->isDirRead(source) && statement != copy)
						|| (accesses->isDirRead(result) && !resultReads.count(statement))
						|| accesses->hasAddressTaken(source) || accesses->hasAddressTaken(result)
						|| accesses->mayBeIndirAccessed(source) || accesses->mustBeIndirAccessed(source)
						|| accesses->mayBeIndirAccessed(result) || accesses->mustBeIndirAccessed(result)) valid = false;
			}
			if (!valid) continue;
			auto cfg = NonRecursiveCFGBuilder::create()->getCFG(currFunc);
			for (const auto& statement : all)
				if (!isa<EmptyStmt>(statement) && !cfg->hasNodeForStmt(statement)) valid = false;
			if (!valid) continue;
			auto dispatch = cfg->getNodeForStmt(branch).first;
			auto updated = cfg->getNodeForStmt(update).first;
			auto synchronized = cfg->getNodeForStmt(copy).first;
			auto returned = cfg->getNodeForStmt(exit).first;
			if (updated == synchronized || dispatch == updated || dispatch == synchronized
					|| updated->getNumberOfStmts() != 1 || updated->getNumberOfPreds() != 1
					|| (*updated->pred_begin())->getSrc() != dispatch
					|| updated->getNumberOfSuccs() != 1 || updated->getFirstSucc()->getDst() != synchronized
					|| updated->getFirstSucc()->getLabel() || *synchronized->stmt_begin() != copy
					|| synchronized->getNumberOfPreds() != 2 || synchronized->getNumberOfSuccs() != 1
					|| synchronized->getFirstSucc()->getDst() != returned || synchronized->getFirstSucc()->getLabel()) continue;
			std::set<ShPtr<CFG::Node>> predecessors;
			for (auto edge = synchronized->pred_begin(); edge != synchronized->pred_end(); ++edge)
				predecessors.insert((*edge)->getSrc());
			if (predecessors != std::set<ShPtr<CFG::Node>>{dispatch, updated}) continue;
			std::set<ShPtr<CFG::Node>> destinations;
			for (const auto& clause : clauses) destinations.insert(cfg->getNodeForStmt(clause.front()).first);
			if (!defaults) destinations.insert(returned);
			if (dispatch->getNumberOfSuccs() != destinations.size()) continue;
			for (auto edge = dispatch->succ_begin(); edge != dispatch->succ_end(); ++edge)
				if (!destinations.erase((*edge)->getDst())) valid = false;
			if (!valid || !destinations.empty()) continue;
			return ProvenScalarReturnMerge{source, result, sourceDeclaration, sourceInitialization,
				resultInitialization, update, copy, branch, exit};
		}
		return {};
	}
};

struct ByteReadEdge {
	ShPtr<Expression> parent;
	unsigned operand;
};

struct ProvenByteLoadLocal {
	ShPtr<Variable> local;
	ShPtr<Statement> definition;
	ShPtr<Expression> load;
	ShPtr<IntType> originalType;
	std::vector<ByteReadEdge> reads;
};

class OriginalZeroExtendedByteLocals final : public FuncOptimizer {
public:
	OriginalZeroExtendedByteLocals(ShPtr<Module> module, const config::Config& config):
		FuncOptimizer(module), retained(config) {}
	std::string getId() const override { return "OriginalZeroExtendedByteLocals"; }
private:
	const config::Config& retained;
	const common::Function* source = nullptr;
	llvm::Function* machine = nullptr;
	ShPtr<ValueAnalysis> values;
	StmtVector statements;

	bool graph(ShPtr<Expression> expression, std::set<ShPtr<Expression>>& seen) {
		if (!expression || isa<Variable>(expression) || isa<Constant>(expression)) return true;
		if (seen.size() >= common::ReturnDisposition::RowLimit || !seen.insert(expression).second) return false;
		if (auto conversion = cast<CastExpr>(expression)) return graph(conversion->getOperand(), seen);
		if (auto unary = cast<UnaryOpExpr>(expression)) return graph(unary->getOperand(), seen);
		if (auto binary = cast<BinaryOpExpr>(expression))
			return graph(binary->getFirstOperand(), seen) && graph(binary->getSecondOperand(), seen);
		return false;
	}

	bool collect(ShPtr<Statement> first, ShPtr<Statement> parent, StmtSet& seen,
			std::set<ShPtr<Expression>>& expressions) {
		bool exited = false;
		for (auto statement = first; statement; statement = statement->getSuccessor()) {
			if (seen.size() >= common::ReturnDisposition::RowLimit || !seen.insert(statement).second
					|| statement->getParent() != parent || statement->hasLabel() || statement->isGotoTarget()) return false;
			statements.push_back(statement);
			if (isa<EmptyStmt>(statement)) continue;
			if (exited) return false;
			if (auto assignment = cast<AssignStmt>(statement)) {
				if (!graph(assignment->getLhs(), expressions) || !graph(assignment->getRhs(), expressions)) return false;
			} else if (auto declaration = cast<VarDefStmt>(statement)) {
				if (!graph(declaration->getInitializer(), expressions)) return false;
			} else if (auto branch = cast<IfStmt>(statement)) {
				if (branch->hasElseIfClauses() || !graph(branch->getFirstIfCond(), expressions)
						|| !collect(branch->getFirstIfBody(), branch, seen, expressions)
						|| !collect(branch->getElseClause(), branch, seen, expressions)) return false;
			} else if (auto exit = cast<ReturnStmt>(statement)) {
				if (!graph(exit->getRetVal(), expressions)) return false;
				exited = true;
			} else return false;
		}
		return true;
	}

	ShPtr<Variable> byteObject(ShPtr<Expression> expression, uint64_t& offset) {
		offset = 0;
		auto type = expression ? cast<IntType>(expression->getType()) : nullptr;
		if (!type || type->getSize() != 8 || expression->hasMetadata()) return {};
		if (auto direct = cast<Variable>(expression))
			return module->isGlobalVar(direct) && !direct->isVolatile() ? direct : nullptr;
		ShPtr<Expression> pointer;
		if (auto dereference = cast<DerefOpExpr>(expression)) pointer = dereference->getOperand();
		else if (auto index = cast<ArrayIndexOpExpr>(expression)) {
			auto constant = cast<ConstInt>(index->getIndex());
			if (!constant || constant->isNegative() || constant->getValue().getActiveBits() > 2) return {};
			offset = constant->getValue().getZExtValue();
			pointer = index->getBase();
		} else return {};
		if (pointer->hasMetadata()) return {};
		if (auto conversion = cast<BitCastExpr>(pointer)) {
			auto destination = cast<PointerType>(conversion->getType());
			auto byte = destination ? cast<IntType>(destination->getContainedType()) : nullptr;
			if (!byte || byte->getSize() != 8) return {};
			pointer = conversion->getOperand();
		}
		auto address = cast<AddressOpExpr>(pointer);
		auto object = address ? cast<Variable>(address->getOperand()) : nullptr;
		return object && !address->hasMetadata() && module->isGlobalVar(object) && !object->isVolatile()
			? object : nullptr;
	}

	bool memory(ShPtr<Expression> expression, uint64_t pc, bool read) {
		uint64_t offset;
		auto object = byteObject(expression, offset);
		if (!object || object->hasMetadata() || object->isVolatile()) return false;
		const auto& evidence = source->returnDisposition->evidence;
		const auto& summary = *source->originalCallSummary;
		const auto* row = original_expression::unique(evidence.instructions,
			[&](const auto& candidate) { return candidate.pc == pc; });
		const auto* access = original_expression::unique(summary.accesses,
			[&](const auto& candidate) { return candidate.pc == pc; });
		const auto* address = access ? std::get_if<common::OriginalFixedMemoryAddress>(&access->address) : nullptr;
		if (!row || !address || !row->mapped || row->undef || row->bytes != 4 || row->owner != evidence.symbol
				|| row->pc < evidence.start || row->pc >= evidence.end || row->pc % 4
				|| row->word >> 26 != (read ? 36u : 40u) || access->width != 8
				|| access->kind != (read ? "read" : "write") || access->extension != (read ? "zero" : "none")
				|| access->delayed != read || !access->addressEntries.empty() || (read && !((row->word >> 16) & 31))
				|| !address->alignment.isComplete()
				|| !std::holds_alternative<common::OriginalFileBytes>(address->fileBytes)) return false;
		auto instruction = retained.parameters.getPsxMemoryContext()->resolve(pc, 4);
		if (!instruction) return false;
		for (unsigned i = 0; i < 4; ++i)
			if (instruction->bytes[i] != uint8_t(row->word >> (8 * i))) return false;
		unsigned hllMatches = 0;
		for (const auto& statement : statements) {
			if (statement->getAddress() != pc || (!isa<AssignStmt>(statement) && !isa<VarDefStmt>(statement))) continue;
			uint64_t candidateOffset;
			if (byteObject(read ? getRhs(statement) : getLhs(statement), candidateOffset)) ++hllMatches;
		}
		if (hllMatches != 1) return false;
		const auto& views = *source->sharedOriginalAddressViews;
		const auto* view = original_expression::unique(views, [&](const auto& candidate) {
			return std::find(candidate.accessPcs.begin(), candidate.accessPcs.end(), pc) != candidate.accessPcs.end();
		});
		auto objectType = cast<IntType>(object->getType());
		if (!view || !objectType || (view->width != 8 && view->width != 16 && view->width != 32)
				|| std::count(view->accessPcs.begin(), view->accessPcs.end(), pc) != 1
				|| objectType->getSize() != view->width || offset >= view->width / 8
				|| uint64_t(view->start) + offset != address->value || object->getInitialName() != view->symbol) return false;
		auto* global = machine->getParent()->getNamedGlobal(view->symbol);
		auto* marker = global ? global->getMetadata("retdec.original.address-view") : nullptr;
		if (!global || !global->isDeclaration() || global->isConstant() || global->getAddressSpace()
				|| !global->getValueType()->isIntegerTy(view->width) || !marker || marker->getNumOperands() != 5) return false;
		auto* owner = llvm::dyn_cast<llvm::MDString>(marker->getOperand(0).get());
		auto* identity = llvm::dyn_cast<llvm::MDString>(marker->getOperand(1).get());
		auto number = [&](unsigned index, uint64_t expected) {
			auto* value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(marker->getOperand(index));
			return value && value->getType()->isIntegerTy(64) && value->getZExtValue() == expected;
		};
		if (!owner || owner->getString() != source->getName() || !identity || identity->getString() != summary.function
				|| !number(2, view - views.data()) || !number(3, view->start) || !number(4, view->width)) return false;
		llvm::Instruction* matched = nullptr;
		for (auto& block : *machine) for (auto& candidate : block) {
			if ((!llvm::isa<llvm::LoadInst>(candidate) && !llvm::isa<llvm::StoreInst>(candidate))
					|| !original_expression::hasPc(candidate, pc)) continue;
			if (matched) return false;
			matched = &candidate;
		}
		auto* load = llvm::dyn_cast_or_null<llvm::LoadInst>(matched);
		auto* store = llvm::dyn_cast_or_null<llvm::StoreInst>(matched);
		if ((read && (!load || !load->getType()->isIntegerTy(8) || load->isVolatile() || load->isAtomic()))
				|| (!read && (!store || !store->getValueOperand()->getType()->isIntegerTy(8)
					|| store->isVolatile() || store->isAtomic()))) return false;
		auto* pointer = load ? load->getPointerOperand() : store->getPointerOperand();
		if (pointer->getType()->getPointerAddressSpace()) return false;
		uint64_t llvmOffset = 0;
		if (auto* index = llvm::dyn_cast<llvm::GEPOperator>(pointer)) {
			auto* constant = index->getNumIndices() == 1 ? llvm::dyn_cast<llvm::ConstantInt>(index->getOperand(1)) : nullptr;
			if (!index->getSourceElementType()->isIntegerTy(8) || !constant || constant->getValue().isNegative()
					|| constant->getValue().getActiveBits() > 2) return false;
			llvmOffset = constant->getZExtValue();
			pointer = index->getPointerOperand();
		}
		if (auto* conversion = llvm::dyn_cast<llvm::Operator>(pointer))
			if (conversion->getOpcode() == llvm::Instruction::BitCast) pointer = conversion->getOperand(0);
		return pointer == global && llvmOffset == offset;
	}

	bool follows(ShPtr<Statement> definition, ShPtr<Statement> read) {
		for (auto ancestor = read; ancestor; ancestor = ancestor->getParent())
			for (auto next = definition->getSuccessor(); next; next = next->getSuccessor())
				if (next == ancestor) return true;
		return false;
	}

	bool readEdges(ShPtr<Expression> expression, ShPtr<Variable> local, bool byte,
			ShPtr<Expression> parent, unsigned operand, std::vector<ByteReadEdge>& edges) {
		if (!expression || expression->hasMetadata()) return false;
		auto type = cast<IntType>(expression->getType());
		bool equality = isa<EqOpExpr>(expression) || isa<NeqOpExpr>(expression);
		if (!type || (type->getSize() != 8 && type->getSize() != 16 && type->getSize() != 32
				&& !(equality && type->getSize() == 1))) return false;
		if (expression == local) {
			if (!byte || !parent) return false;
			edges.push_back({parent, operand});
			return true;
		}
		if (isa<ConstInt>(expression)) return true;
		if (auto variable = cast<Variable>(expression))
			return currFunc->hasLocalVar(variable) && !variable->isExternal() && !variable->isVolatile();
		if (auto conversion = cast<CastExpr>(expression)) {
			auto input = cast<IntType>(conversion->getOperand()->getType());
			auto extension = cast<ExtCastExpr>(conversion);
			auto truncation = cast<TruncCastExpr>(conversion);
			if (!input || (!isa<BitCastExpr>(conversion) && !extension && !truncation)
					|| (extension && (extension->getOriginalExtraction()
						|| extension->getVariant() == ExtCastExpr::Variant::FPExt))
					|| (truncation && truncation->getOriginalExtraction())) return false;
			return readEdges(conversion->getOperand(), local,
				byte || type->getSize() == 8 || (extension && input->getSize() == 8), conversion, 0, edges);
		}
		auto binary = cast<BinaryOpExpr>(expression);
		if (!binary) return false;
		if (isa<EqOpExpr>(binary) || isa<NeqOpExpr>(binary)) {
			auto lhs = cast<IntType>(binary->getFirstOperand()->getType());
			auto rhs = cast<IntType>(binary->getSecondOperand()->getType());
			bool direct = (binary->getFirstOperand() == local && isa<ConstInt>(binary->getSecondOperand()))
				|| (binary->getSecondOperand() == local && isa<ConstInt>(binary->getFirstOperand()));
			if (!direct || !lhs || !rhs || lhs->getSize() != 8 || rhs->getSize() != 8
					|| !lhs->isSigned() || !rhs->isSigned()) return false;
			byte = true;
		} else if (!byte || (!isa<AddOpExpr>(binary) && !isa<SubOpExpr>(binary) && !isa<MulOpExpr>(binary)
				&& !isa<BitAndOpExpr>(binary) && !isa<BitOrOpExpr>(binary) && !isa<BitXorOpExpr>(binary))) return false;
		return readEdges(binary->getFirstOperand(), local, byte, binary, 0, edges)
			&& readEdges(binary->getSecondOperand(), local, byte, binary, 1, edges);
	}

	std::optional<ProvenByteLoadLocal> prove(ShPtr<Variable> local) {
		auto type = cast<IntType>(local->getType());
		if (!type || type->getSize() != 8 || !type->isSigned() || local->isExternal() || local->isVolatile()
				|| local->hasMetadata() || values->mayBePointed(local) || module->hasAssignedDebugName(local)
				|| !module->getDebugNameForLocalVar(currFunc, local).empty()) return {};
		ProvenByteLoadLocal candidate{local, nullptr, nullptr, type, {}};
		ShPtr<VarDefStmt> declaration;
		StmtSet observed;
		for (const auto& statement : statements) {
			auto data = values->getValueData(statement);
			if (data->hasCalls() || data->hasAddressTaken(local) || data->mayBeIndirAccessed(local)
					|| data->mustBeIndirAccessed(local)) return {};
			if (data->isDirAccessed(local)) observed.insert(statement);
			if (auto definition = cast<VarDefStmt>(statement)) if (definition->getVar() == local) {
				if (declaration) return {};
				declaration = definition;
			}
			if (!data->isDirWritten(local)) continue;
			if ((!isa<AssignStmt>(statement) && !isa<VarDefStmt>(statement)) || getLhs(statement) != local) return {};
			auto rhs = getRhs(statement);
			if (!rhs) continue;
			if (candidate.definition || data->isDirRead(local) || !statement->getAddress().isDefined()
					|| !memory(rhs, statement->getAddress().getValue(), true)) return {};
			candidate.definition = statement;
			candidate.load = rhs;
		}
		if (!declaration || !candidate.definition) return {};
		auto uses = VarUsesVisitor::create(values, false)->getUses(local, currFunc);
		if (uses->dirUses != observed || !uses->indirUses.empty()) return {};
		for (const auto& statement : observed) {
			auto data = values->getValueData(statement);
			std::size_t before = candidate.reads.size();
			if (data->isDirRead(local)) {
				if (!follows(candidate.definition, statement)) return {};
				ShPtr<Expression> expression;
				bool byte = false;
				if (auto assignment = cast<AssignStmt>(statement)) {
					if (values->getValueData(assignment->getLhs())->isDirAccessed(local)) return {};
					expression = assignment->getRhs();
					byte = statement->getAddress().isDefined()
						&& memory(assignment->getLhs(), statement->getAddress().getValue(), false);
				} else if (auto definition = cast<VarDefStmt>(statement)) expression = definition->getInitializer();
				else if (auto branch = cast<IfStmt>(statement)) expression = branch->getFirstIfCond();
				else if (auto exit = cast<ReturnStmt>(statement)) expression = exit->getRetVal();
				if (!readEdges(expression, local, byte, nullptr, 0, candidate.reads)) return {};
			}
			if (data->getDirNumOfUses(local)
					!= candidate.reads.size() - before + (data->isDirWritten(local) ? 1 : 0)) return {};
		}
		return candidate.reads.empty() ? std::nullopt : std::optional<ProvenByteLoadLocal>{candidate};
	}

	void runOnFunction(ShPtr<Function> function) override {
		currFunc = function;
		machine = module->getLLVMModule()->getFunction(function->getInitialName());
		source = retained.functions.getFunctionByName(function->getInitialName());
		const auto& scope = retained.parameters.getOriginalCallScope();
		const auto& context = retained.parameters.getPsxMemoryContext();
		if (!machine || machine->isDeclaration() || !function->getBody() || !source || !scope || !context
				|| !source->returnDisposition || !source->originalCallSummary || !source->sharedOriginalAddressViews
				|| source->sharedOriginalAddressViews->empty() || !source->getStart().isDefined() || !source->getEnd().isDefined()
				|| source->getName() != machine->getName().str() || source->getStart() != retained.parameters.getEntryPoint()) return;
		const auto& summary = *source->originalCallSummary;
		const auto& evidence = source->returnDisposition->evidence;
		bool ordinary = source->originalBodyCandidate
			&& std::holds_alternative<common::OriginalOrdinaryBody>(*source->originalBodyCandidate)
			&& source->returnDisposition->kind == common::ReturnDisposition::Kind::Unknown;
		bool value = source->returnDisposition->kind == common::ReturnDisposition::Kind::Value
			&& summary.result.isComplete() && summary.declaration.isComplete();
		if ((!ordinary && !value) || !summary.entry.isComplete() || !summary.control.isComplete() || !evidence.decodeComplete
				|| !evidence.analysisComplete || !evidence.calls.empty() || evidence.selection != "selected-root"
				|| evidence.symbol != source->getName() || summary.function != scope->root.key
				|| evidence.start != scope->root.start || evidence.end != scope->root.end || evidence.start >= evidence.end
				|| evidence.start != source->getStart().getValue() || evidence.end != source->getEnd().getValue()) return;
		auto root = context->resolve(evidence.start, evidence.end - evidence.start);
		if (!root || root->image->id != scope->root.imageId || root->image->payloadHash != scope->payloadHash) return;
		statements.clear();
		StmtSet seen;
		std::set<ShPtr<Expression>> expressions;
		if (!collect(function->getBody(), nullptr, seen, expressions)) return;
		values = ValueAnalysis::create(SimpleAliasAnalysis::create(), false);
		values->initAliasAnalysis(module);
		std::vector<ProvenByteLoadLocal> candidates;
		for (const auto& local : function->getLocalVars())
			if (auto candidate = prove(local)) candidates.push_back(std::move(*candidate));
		for (const auto& candidate : candidates) {
			auto load = BitCastExpr::create(candidate.load, IntType::create(8, false));
			if (auto assignment = cast<AssignStmt>(candidate.definition)) assignment->setRhs(load);
			else cast<VarDefStmt>(candidate.definition)->setInitializer(load);
			for (const auto& edge : candidate.reads) {
				auto read = BitCastExpr::create(candidate.local, candidate.originalType);
				if (auto conversion = cast<CastExpr>(edge.parent)) conversion->setOperand(read);
				else if (edge.operand) cast<BinaryOpExpr>(edge.parent)->setSecondOperand(read);
				else cast<BinaryOpExpr>(edge.parent)->setFirstOperand(read);
			}
		}
		for (const auto& candidate : candidates) candidate.local->setType(IntType::create(8, false));
		values.reset();
	}
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

void recoverOriginalAddressViews(llvm::Function& function, common::Function& source,
		const config::Config& config) {
	source.sharedOriginalAddressViews.reset();
	const auto& scope = config.parameters.getOriginalCallScope();
	const auto& context = config.parameters.getPsxMemoryContext();
	const auto& layout = function.getParent()->getDataLayout();
	if (!scope || !context || !source.returnDisposition || !source.originalCallSummary
			|| source.getName() != function.getName().str() || !source.getStart().isDefined()
			|| !source.getEnd().isDefined() || source.getStart() != config.parameters.getEntryPoint()
			|| function.isDeclaration() || !function.getReturnType()->isIntegerTy(32)
			|| layout.getPointerSizeInBits() != 32 || !layout.isLittleEndian()) return;
	const auto& disposition = *source.returnDisposition;
	const auto& evidence = disposition.evidence;
	const auto& summary = *source.originalCallSummary;
	bool ordinary = source.originalBodyCandidate
		&& std::holds_alternative<common::OriginalOrdinaryBody>(*source.originalBodyCandidate)
		&& disposition.kind == common::ReturnDisposition::Kind::Unknown;
	bool value = disposition.kind == common::ReturnDisposition::Kind::Value
		&& summary.result.isComplete() && summary.declaration.isComplete();
	if ((!ordinary && !value) || !summary.entry.isComplete() || !summary.control.isComplete()
			|| summary.pendingEntry != "requires-no-pending-gpr-loads" || summary.exits.empty()
			|| !evidence.decodeComplete || !evidence.analysisComplete || !evidence.calls.empty()
			|| evidence.selection != "selected-root" || evidence.symbol != source.getName()
			|| evidence.start != source.getStart().getValue() || evidence.end != source.getEnd().getValue()
			|| scope->root.start != evidence.start || scope->root.end != evidence.end
			|| scope->root.key != summary.function || summary.function.empty()
			|| evidence.start >= evidence.end || evidence.start % 4 || evidence.end % 4
			|| evidence.end > uint64_t(UINT32_MAX) + 1
			|| evidence.instructions.size() != (evidence.end - evidence.start) / 4
			|| evidence.instructions.size() > common::ReturnDisposition::RowLimit
			|| summary.accesses.empty() || summary.accesses.size() > common::ReturnDisposition::RowLimit) return;
	auto instructions = context->resolve(evidence.start, evidence.end - evidence.start);
	if (!instructions || instructions->image->id != scope->root.imageId
			|| instructions->image->payloadHash != scope->payloadHash) return;
	std::map<uint64_t, const common::OriginalMemoryAccess*> accesses;
	std::vector<const common::OriginalMemoryAccess*> ordered;
	for (const auto& access : summary.accesses) {
		const auto* address = std::get_if<common::OriginalFixedMemoryAddress>(&access.address);
		const auto* bytes = address ? std::get_if<common::OriginalFileBytes>(&address->fileBytes) : nullptr;
		if (!address || !bytes || !address->alignment.isComplete()
				|| (access.width != 8 && access.width != 16 && access.width != 32)
				|| common::psxRamAddress(address->value) != std::optional<uint64_t>{address->value}
				|| address->value % (access.width / 8) || !access.addressEntries.empty()
				|| bytes->bytes.size() != access.width / 8 || !bytes->mappingBytes
				|| common::psxRamAddress(bytes->mappingStart) != std::optional<uint64_t>{bytes->mappingStart}
				|| bytes->mappingBytes > 0x80200000ull - bytes->mappingStart
				|| bytes->payloadOffset > bytes->mappingBytes
				|| bytes->bytes.size() > bytes->mappingBytes - bytes->payloadOffset
				|| uint64_t(bytes->mappingStart) + bytes->payloadOffset != address->value
				|| !accesses.emplace(access.pc, &access).second) return;
		auto span = context->resolve(address->value, access.width / 8);
		if (!span || common::psxRamAddress(span->image->loadAddress) != std::optional<uint64_t>{bytes->mappingStart}
				|| span->image->payload->size() != bytes->mappingBytes || span->payloadOffset != bytes->payloadOffset
				|| !std::equal(bytes->bytes.begin(), bytes->bytes.end(), span->bytes)) return;
		ordered.push_back(&access);
	}
	unsigned observed = 0;
	for (size_t i = 0; i < evidence.instructions.size(); ++i) {
		const auto& row = evidence.instructions[i];
		if (row.pc != evidence.start + 4 * i || row.owner != evidence.symbol
				|| row.bytes != 4 || !row.mapped || row.undef) return;
		for (unsigned j = 0; j < 4; ++j)
			if (instructions->bytes[4 * i + j] != uint8_t(row.word >> (8 * j))) return;
		unsigned op = row.word >> 26;
		bool read = op == 32 || op == 33 || op == 35 || op == 36 || op == 37;
		bool write = op == 40 || op == 41 || op == 43;
		if (!read && !write) {
			if (accesses.count(row.pc) || (32 <= op && op <= 46) || op == 3
					|| (!op && (row.word & 63) == 9)) return;
			continue;
		}
		auto found = accesses.find(row.pc);
		if (found == accesses.end()) return;
		const auto& access = *found->second;
		unsigned width = op == 32 || op == 36 || op == 40 ? 8 : op == 33 || op == 37 || op == 41 ? 16 : 32;
		std::string extension = write || width == 32 ? "none" : op == 32 || op == 33 ? "sign" : "zero";
		if (access.kind != (read ? "read" : "write") || access.width != width
				|| access.extension != extension || access.delayed != read) return;
		++observed;
	}
	if (observed != accesses.size()) return;
	std::map<uint64_t, llvm::Instruction*> matches;
	for (auto& block : function) for (auto& instruction : block) {
		if (llvm::isa<llvm::CallInst>(instruction) || llvm::isa<llvm::InvokeInst>(instruction)) return;
		auto* load = llvm::dyn_cast<llvm::LoadInst>(&instruction);
		auto* store = llvm::dyn_cast<llvm::StoreInst>(&instruction);
		if (!load && !store) continue;
		auto* pointer = load ? load->getPointerOperand() : store->getPointerOperand();
		if (auto* local = llvm::dyn_cast<llvm::AllocaInst>(pointer)) {
			auto* type = local->getAllocatedType();
			if (local->getFunction() != &function || local->isArrayAllocation()
					|| local->getType()->getPointerAddressSpace()
					|| (!type->isIntegerTy(8) && !type->isIntegerTy(16) && !type->isIntegerTy(32))) return;
			for (auto* user : local->users()) {
				auto* read = llvm::dyn_cast<llvm::LoadInst>(user);
				auto* write = llvm::dyn_cast<llvm::StoreInst>(user);
				if (read) {
					if (read->getFunction() != &function || read->getPointerOperand() != local
							|| read->getType() != type || read->isVolatile() || read->isAtomic()) return;
				} else if (write) {
					if (write->getFunction() != &function || write->getPointerOperand() != local
							|| write->getValueOperand()->getType() != type || write->isVolatile() || write->isAtomic()) return;
				} else return;
			}
			continue;
		}
		auto* node = instruction.getMetadata("insn.addr");
		auto* pc = node && node->getNumOperands() == 1
			? llvm::mdconst::dyn_extract<llvm::ConstantInt>(node->getOperand(0)) : nullptr;
		if (!pc || !pc->getType()->isIntegerTy(64)) return;
		auto found = accesses.find(pc->getZExtValue());
		if (found == accesses.end() || !matches.emplace(found->first, &instruction).second) return;
		const auto& access = *found->second;
		auto* type = load ? load->getType() : store->getValueOperand()->getType();
		auto* cast = llvm::dyn_cast<llvm::Operator>(pointer);
		auto* address = cast && cast->getOpcode() == llvm::Instruction::IntToPtr
			? llvm::dyn_cast<llvm::ConstantInt>(cast->getOperand(0)) : nullptr;
		if ((load && (access.kind != "read" || load->isVolatile() || load->isAtomic()))
				|| (store && (access.kind != "write" || store->isVolatile() || store->isAtomic()))
				|| !type->isIntegerTy(access.width) || pointer->getType()->getPointerAddressSpace()
				|| !address || !address->getType()->isIntegerTy(32)
				|| address->getZExtValue() != std::get<common::OriginalFixedMemoryAddress>(access.address).value) return;
	}
	if (matches.size() != accesses.size()) return;
	std::sort(ordered.begin(), ordered.end(), [](const auto* a, const auto* b) {
		const auto& left = std::get<common::OriginalFixedMemoryAddress>(a->address);
		const auto& right = std::get<common::OriginalFixedMemoryAddress>(b->address);
		return a->width != b->width ? a->width > b->width : left.value < right.value;
	});
	struct ScalarSpan {
		common::OriginalAddressSpanView view;
		const common::OriginalFileBytes* backing;
	};
	std::vector<ScalarSpan> spans;
	bool mixed = false;
	for (const auto* access : ordered) {
		const auto& address = std::get<common::OriginalFixedMemoryAddress>(access->address);
		const auto& bytes = std::get<common::OriginalFileBytes>(address.fileBytes);
		ScalarSpan* overlap = nullptr;
		for (auto& span : spans) {
			if (uint64_t(address.value) + access->width / 8 <= span.view.start
					|| uint64_t(span.view.start) + span.view.width / 8 <= address.value) continue;
			if (overlap || address.value < span.view.start
					|| uint64_t(address.value) + access->width / 8 > uint64_t(span.view.start) + span.view.width / 8
					|| (access->width != 8 && (access->width != span.view.width || address.value != span.view.start))) return;
			overlap = &span;
		}
		if (!overlap) {
			spans.push_back({{"", address.value, access->width, {access->pc}}, &bytes});
			continue;
		}
		auto offset = address.value - overlap->view.start;
		if (bytes.mappingStart != overlap->backing->mappingStart || bytes.mappingBytes != overlap->backing->mappingBytes
				|| bytes.payloadOffset != overlap->backing->payloadOffset + offset
				|| !std::equal(bytes.bytes.begin(), bytes.bytes.end(), overlap->backing->bytes.begin() + offset)) return;
		mixed |= access->width == 8 && overlap->view.width > 8;
		overlap->view.accessPcs.push_back(access->pc);
	}
	if (!mixed) return;
	std::sort(spans.begin(), spans.end(), [](const auto& a, const auto& b) { return a.view.start < b.view.start; });
	for (auto& span : spans) {
		span.view.symbol = "original_address_" + std::to_string(span.view.start);
		if (function.getParent()->getNamedValue(span.view.symbol)) return;
		std::sort(span.view.accessPcs.begin(), span.view.accessPcs.end());
	}
	auto views = std::make_shared<std::vector<common::OriginalAddressSpanView>>();
	auto& llvmContext = function.getContext();
	auto number = [&](uint64_t n) -> llvm::Metadata* {
		return llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(llvm::Type::getInt64Ty(llvmContext), n));
	};
	for (auto& span : spans) {
		auto& view = span.view;
		auto* scalar = new llvm::GlobalVariable(*function.getParent(), llvm::Type::getIntNTy(llvmContext, view.width),
			false, llvm::GlobalValue::ExternalLinkage, nullptr, view.symbol);
		scalar->setMetadata("retdec.original.address-view", llvm::MDNode::get(llvmContext, {
			llvm::MDString::get(llvmContext, source.getName()), llvm::MDString::get(llvmContext, summary.function),
			number(views->size()), number(view.start), number(view.width)}));
		for (auto pc : view.accessPcs) {
			const auto& access = *accesses.at(pc);
			auto* instruction = matches.at(pc);
			llvm::Value* pointer = scalar;
			if (access.width != view.width) {
				llvm::IRBuilder<> builder(instruction);
				pointer = builder.CreateBitCast(scalar, builder.getInt8PtrTy());
				auto offset = std::get<common::OriginalFixedMemoryAddress>(access.address).value - view.start;
				if (offset) pointer = builder.CreateGEP(pointer, builder.getInt32(offset));
			}
			instruction->setOperand(llvm::isa<llvm::LoadInst>(instruction) ? 0 : 1, pointer);
		}
		views->push_back(std::move(view));
	}
	source.sharedOriginalAddressViews = std::move(views);
}
}

void recoverPointerExpressions(llvm::Module &module, config::Config &config) {
	if (config.parameters.isOriginalOnlyReturnRecovery()) {
		for (auto& function : module) {
			if (config.architecture.isMipsOrPic32()) {
				recoverUnsignedReciprocalSinks(function);
				recoverSharedSignedViews(function);
				recoverSignedScaledPredicates(function);
			}
			if (auto* source = config.functions.getFunctionByName(function.getName().str())) {
				original_expression::recover(function, const_cast<common::Function&>(*source),
					config.parameters.getOriginalSourceForm());
				const auto& scope = config.parameters.getOriginalCallScope();
				if (config.architecture.isMipsOrPic32() && scope
						&& source->returnDisposition && source->originalCallSummary) {
					const auto& evidence = source->returnDisposition->evidence;
					unsigned identities = 0;
					auto matchIdentity = [&](const common::ReviewedOriginalFunction& row) {
						identities += row.start == evidence.start && row.end == evidence.end
							&& row.key == source->originalCallSummary->function;
					};
					matchIdentity(scope->root);
					for (const auto& row : scope->callees) matchIdentity(row);
					if (identities == 1) {
						restoreSignedNarrowLoadEqualities(function, *source);
						recoverOriginalAddressViews(function, const_cast<common::Function&>(*source), config);
					}
				}
			}
		}
		return;
	}
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
	if (config.parameters.isOriginalOnlyReturnRecovery()) ScalarReturnMergeRecovery(module).optimize();
	for (auto f = module->func_begin(); f != module->func_end(); ++f) {
		auto function = *f;
		auto *machine = module->getLLVMModule()->getFunction(function->getInitialName());
		auto *source = config.functions.getFunctionByName(function->getInitialName());
		if (source && source->originalBodyCandidate) {
			if (!config.parameters.isOriginalOnlyReturnRecovery()
					|| source->getStart() != config.parameters.getEntryPoint()
					|| !source->returnDisposition
					|| source->returnDisposition->kind != common::ReturnDisposition::Kind::Unknown)
				throw std::runtime_error("invalid-original-body-candidate-projection");
			if (std::holds_alternative<common::OriginalOrdinaryBody>(*source->originalBodyCandidate)
					|| std::holds_alternative<common::OriginalEntryStackWordBody>(*source->originalBodyCandidate)) {
				if (!machine || machine->isDeclaration() || !function->getBody())
					throw std::runtime_error("original-body-proposal-lowering-incomplete");
				if (std::holds_alternative<common::OriginalEntryStackWordBody>(*source->originalBodyCandidate)
						&& (machine->arg_size() != 5 || function->getNumOfParams() != 5
							|| !machine->getReturnType()->isIntegerTy(32)))
					throw std::runtime_error("conditional-stack-word-projection-incomplete");
				continue;
			}
			if (!std::holds_alternative<common::OriginalEmptyVoidBody>(*source->originalBodyCandidate))
				throw std::runtime_error("invalid-original-body-candidate-projection");
			function->setRetType(VoidType::create());
			function->setParams({}); function->setLocalVars({}); function->setVarArg(false);
			function->setBody(EmptyStmt::create(nullptr, source->getStart()));
			continue;
		}
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
	if (config.parameters.isOriginalOnlyReturnRecovery()) OriginalZeroExtendedByteLocals(module, config).optimize();
}

namespace {

class OriginalSourceFormCensus final: public OrderedAllVisitor {
public:
	OriginalSourceFormCensus(ShPtr<Module> module, config::Config& config):
		OrderedAllVisitor(true, true), module(module), retained(config),
		form(*config.parameters.getOriginalSourceForm()),
		values(ValueAnalysis::create(SimpleAliasAnalysis::create(), false)) {
		values->initAliasAnalysis(module);
		uses = VarUsesVisitor::create(values, false);
	}

	void run() {
		for (const auto& source : retained.functions) {
			auto& writable = const_cast<common::Function&>(source);
			if (source.originalSourceExpressions.size() > common::ReturnDisposition::RowLimit)
				throw std::runtime_error("original-source-form-census-exhausted");
			writable.originalSourceForms = std::vector<common::OriginalSourceFormApplication>{};
			writable.originalSourceFormFailures.clear();
			rows[&writable].resize(source.originalSourceExpressions.size());
			for (unsigned i = 0; i < source.originalSourceExpressions.size(); ++i)
				writable.originalSourceForms->push_back({i, common::SourceFormUnresolved{"source-form-census-not-run"}});
		}
		for (auto i = module->global_var_begin(); i != module->global_var_end(); ++i) (*i)->accept(this);
		for (auto i = module->func_begin(); i != module->func_end(); ++i) {
			current = *i;
			restart();
			current->accept(this);
		}
		current.reset();
		for (auto& entry : rows) {
			auto& source = *entry.first;
			for (unsigned i = 0; i < entry.second.size(); ++i) {
				auto& row = entry.second[i];
				const auto& witness = source.originalSourceExpressions[i];
				if (source.returnDisposition) {
					auto& obligations = source.returnDisposition->evidence.obligations;
					obligations.erase(std::remove_if(obligations.begin(), obligations.end(), [&](const auto& item) {
						return item.pc == witness.rightPc && item.domain == "source-expression"
							&& item.reason == "source-form-census-not-run";
					}), obligations.end());
				}
				auto rebound = original_expression::bind(source, witness.rightPc);
				if (!rebound || !(*rebound == witness)
						|| std::count(source.originalSourceExpressions.begin(),
							source.originalSourceExpressions.end(), witness) != 1)
					row.reason = "source-form-witness-unresolved";
				if (row.reason.empty() && !row.occurrences) row.reason = "source-form-association-missing";
				if (!row.reason.empty()) {
					refuse(&source, witness.rightPc, row.reason);
					source.originalSourceForms->at(i) = {i, common::SourceFormUnresolved{row.reason}};
				} else source.originalSourceForms->at(i) = {i, common::SourceFormReady{row.occurrences}};
			}
		}
		if (failed) throw std::runtime_error("original-source-form-census-unresolved");
	}

private:
	using OrderedAllVisitor::visit;
	struct Row { unsigned occurrences = 0; std::string reason; };
	std::map<common::Function*, std::vector<Row>> rows;
	std::map<ShPtr<Variable>, bool> safeParameters;
	ShPtr<Module> module;
	config::Config& retained;
	common::OriginalSourceForm form;
	ShPtr<ValueAnalysis> values;
	ShPtr<VarUsesVisitor> uses;
	ShPtr<Function> current;
	ShPtr<TruncCastExpr> enclosedTrunc;
	bool failed = false;
	std::map<common::Function*, unsigned> actualOccurrences;

	void refuse(common::Function* source, uint64_t pc, const std::string& reason) {
		failed = true;
		if (!source) return;
		auto& failures = source->originalSourceFormFailures;
		if (std::find(failures.begin(), failures.end(), reason) == failures.end()) failures.push_back(reason);
		if (!source->returnDisposition) return;
		auto& obligations = source->returnDisposition->evidence.obligations;
		if (std::any_of(obligations.begin(), obligations.end(), [&](const auto& row) {
			return row.pc == pc && row.domain == "source-expression" && row.reason == reason;
		})) return;
		if (obligations.size() >= common::ReturnDisposition::RowLimit)
			throw std::runtime_error("original-expression-obligations-exhausted");
		obligations.push_back({pc, "source-expression", reason});
	}

	Row* locate(Extraction association) {
		auto* found = retained.functions.getFunctionByName(association->functionInitialName());
		auto* source = const_cast<common::Function*>(found);
		if (!source) { refuse(nullptr, association->witness().rightPc, "source-form-owner-missing"); return nullptr; }
		auto& count = actualOccurrences[source];
		if (++count > common::ReturnDisposition::ReferenceLimit)
			throw std::runtime_error("original-source-form-occurrences-exhausted");
		unsigned matches = 0, index = 0;
		for (unsigned i = 0; i < source->originalSourceExpressions.size(); ++i)
			if (source->originalSourceExpressions[i] == association->witness()) { ++matches; index = i; }
		if (matches != 1) {
			refuse(source, association->witness().rightPc, "source-form-witness-unresolved");
			return nullptr;
		}
		return &rows.at(source)[index];
	}

	bool parameterIsSafe(ShPtr<Variable> parameter) {
		auto cached = safeParameters.find(parameter);
		if (cached != safeParameters.end()) return cached->second;
		bool safe = !parameter->isVolatile() && !values->mayBePointed(parameter);
		auto locations = uses->getUses(parameter, current);
		auto check = [&](const StmtSet& statements) {
			for (const auto& statement : statements) {
				auto data = values->getValueData(statement);
				if (data->isDirWritten(parameter) || data->mayBeIndirWritten(parameter)
						|| data->mustBeIndirWritten(parameter) || data->hasAddressTaken(parameter)) safe = false;
			}
		};
		check(locations->dirUses); check(locations->indirUses);
		safeParameters.emplace(parameter, safe);
		return safe;
	}

	void visit(ShPtr<ExtCastExpr> expression) override {
		auto association = expression->getOriginalExtraction();
		if (!association) { OrderedAllVisitor::visit(expression); return; }
		auto* row = locate(association);
		auto trunc = cast<TruncCastExpr>(expression->getOperand());
		auto resultType = cast<IntType>(expression->getType());
		auto viewType = trunc ? cast<IntType>(trunc->getType()) : nullptr;
		auto parameter = association->parameter();
		auto parameterType = cast<IntType>(parameter->getType());
		auto* source = retained.functions.getFunctionByName(association->functionInitialName());
		bool intact = current && current->isDefinition()
			&& current->getInitialName() == association->functionInitialName()
			&& source && source->originalCallSummary && source->originalCallSummary->declaration.isComplete()
			&& source->originalCallSummary->parameterRegisters.size() == current->getParams().size()
			&& association->form() == form && association->formalOrdinal() < current->getParams().size()
			&& source->originalCallSummary->parameterRegisters[association->formalOrdinal()] == association->witness().entryRegister
			&& current->getParams()[association->formalOrdinal()] == parameter
			&& parameterType && parameterType->getSize() == 32
			&& expression->getVariant() == ExtCastExpr::Variant::SExt
			&& resultType && resultType->getSize() == 32 && resultType->isSigned()
			&& trunc && trunc->getOriginalExtraction() == association && trunc->getOperand() == parameter
			&& viewType && viewType->getSize() == association->witness().viewWidth && viewType->isSigned()
			&& (viewType->getSize() == 8 || viewType->getSize() == 16);
		if (intact) intact = parameterIsSafe(parameter);
		if (row) {
			if (intact) ++row->occurrences;
			else row->reason = "source-form-association-altered-or-unqualified";
		}
		auto previous = enclosedTrunc;
		enclosedTrunc = trunc;
		OrderedAllVisitor::visit(expression);
		enclosedTrunc = previous;
	}

	void visit(ShPtr<TruncCastExpr> expression) override {
		if (auto association = expression->getOriginalExtraction()) {
			auto* row = locate(association);
			if (expression != enclosedTrunc && row) row->reason = "source-form-associated-truncation-orphaned";
		}
		OrderedAllVisitor::visit(expression);
	}
};

}

void validateOriginalSourceForms(ShPtr<Module> module, config::Config& config) {
	if (!config.parameters.isOriginalOnlyReturnRecovery() || !config.parameters.getOriginalSourceForm()) return;
	OriginalSourceFormCensus(module, config).run();
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
