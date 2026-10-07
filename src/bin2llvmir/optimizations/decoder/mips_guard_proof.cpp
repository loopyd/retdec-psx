#include "mips_call_effects.h"
#include <array>
#include <deque>
#include <map>
#include <set>
#include <tuple>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Instructions.h>
#include "retdec/bin2llvmir/providers/abi/abi.h"

namespace retdec { namespace bin2llvmir {
namespace {
using namespace llvm;
struct Range {
	uint64_t lo = 0, hi = UINT32_MAX;
	bool exact() const { return lo == hi; }
};
using Registers = std::array<Range, 32>;
using Values = std::map<Value*, Range>;

int reg(Value* value, Abi* abi) {
	if (!abi->isGeneralPurposeRegister(value)) return -1;
	return abi->getRegisterId(value) - MIPS_REG_0;
}

bool effects(CallInst* call, uint32_t& writes) {
	auto* node = call->getMetadata("retdec.mips.leaf.effects");
	if (!node || node->getNumOperands() != 3) return false;
	auto* value = mdconst::dyn_extract<ConstantInt>(node->getOperand(1));
	if (!value) return false;
	writes = value->getZExtValue() | (uint32_t(1) << 31);
	return true;
}

Range valueRange(Value* value, const Values& values) {
	if (auto* constant = dyn_cast<ConstantInt>(value))
		return {constant->getZExtValue(), constant->getZExtValue()};
	auto found = values.find(value);
	if (found != values.end()) return found->second;
	if (value->getType()->isIntegerTy() && value->getType()->getIntegerBitWidth() < 32)
		return {0, (uint64_t(1) << value->getType()->getIntegerBitWidth()) - 1};
	return {};
}

Range operation(Instruction& instruction, const Values& values) {
	auto* type = instruction.getType();
	if (!type->isIntegerTy() || type->getIntegerBitWidth() > 32) return {};
	unsigned bits = type->getIntegerBitWidth();
	uint64_t mask = (uint64_t(1) << bits) - 1;
	Range top{0, mask};
	for (auto& operand : instruction.operands())
		if (operand->getType()->isIntegerTy()
				&& operand->getType()->getIntegerBitWidth() > 32) return top;
	Range a = valueRange(instruction.getOperand(0), values);
	if (isa<ZExtInst>(instruction)) return a;
	if (isa<TruncInst>(instruction)) {
		if (a.exact()) return {a.lo & mask, a.lo & mask};
		return a.hi <= mask ? a : top;
	}
	if (isa<SExtInst>(instruction)) {
		unsigned from = instruction.getOperand(0)->getType()->getIntegerBitWidth();
		if (a.hi < (uint64_t(1) << (from - 1))) return a;
		return top;
	}
	if (instruction.getNumOperands() < 2) return top;
	Range b = valueRange(instruction.getOperand(1), values);
	if (auto* comparison = dyn_cast<ICmpInst>(&instruction)) {
		bool yes = false, no = false;
		switch (comparison->getPredicate()) {
		case CmpInst::ICMP_EQ:
			yes = a.exact() && b.exact() && a.lo == b.lo;
			no = a.hi < b.lo || b.hi < a.lo; break;
		case CmpInst::ICMP_NE:
			no = a.exact() && b.exact() && a.lo == b.lo;
			yes = a.hi < b.lo || b.hi < a.lo; break;
		case CmpInst::ICMP_ULT: yes = a.hi < b.lo; no = a.lo >= b.hi; break;
		case CmpInst::ICMP_ULE: yes = a.hi <= b.lo; no = a.lo > b.hi; break;
		case CmpInst::ICMP_UGT: yes = a.lo > b.hi; no = a.hi <= b.lo; break;
		case CmpInst::ICMP_UGE: yes = a.lo >= b.hi; no = a.hi < b.lo; break;
		default: break;
		}
		return yes ? Range{1, 1} : no ? Range{0, 0} : Range{0, 1};
	}
	if (auto* select = dyn_cast<SelectInst>(&instruction)) {
		Range c = valueRange(select->getFalseValue(), values);
		if (a.exact()) return a.lo ? b : c;
		return {std::min(b.lo, c.lo), std::max(b.hi, c.hi)};
	}
	switch (instruction.getOpcode()) {
	case Instruction::Add:
		if (a.exact() && b.exact()) return {(a.lo + b.lo) & mask, (a.lo + b.lo) & mask};
		if (a.hi + b.hi <= mask) return {a.lo + b.lo, a.hi + b.hi};
		break;
	case Instruction::Sub:
		if (a.exact() && b.exact()) return {(a.lo - b.lo) & mask, (a.lo - b.lo) & mask};
		if (a.lo >= b.hi) return {a.lo - b.hi, a.hi - b.lo};
		break;
	case Instruction::And:
		if (a.exact() && b.exact()) return {a.lo & b.lo, a.lo & b.lo};
		if (a.exact()) return {0, std::min(a.lo, b.hi)};
		if (b.exact()) return {0, std::min(b.lo, a.hi)};
		break;
	case Instruction::Or:
		if (a.exact() && b.exact()) return {a.lo | b.lo, a.lo | b.lo};
		break;
	case Instruction::Shl:
		if (b.exact() && b.lo < bits && (a.hi << b.lo) <= mask)
			return {a.lo << b.lo, a.hi << b.lo};
		break;
	case Instruction::LShr:
		if (b.exact() && b.lo < bits) return {a.lo >> b.lo, a.hi >> b.lo};
		break;
	default: break;
	}
	return top;
}

Range initial(BasicBlock* block, unsigned index, Abi* abi,
		std::set<BasicBlock*> visiting, unsigned& budget) {
	if (!budget || !visiting.insert(block).second) return {};
	--budget;
	for (auto it = block->rbegin(); it != block->rend(); ++it) {
		if (auto* call = dyn_cast<CallInst>(&*it)) {
			uint32_t writes;
			if (!effects(call, writes) || (writes & (uint32_t(1) << index))) return {};
		}
		if (auto* store = dyn_cast<StoreInst>(&*it)) {
			if (reg(store->getPointerOperand(), abi) != int(index)) continue;
			auto* constant = dyn_cast<ConstantInt>(store->getValueOperand());
			return constant ? Range{constant->getZExtValue(), constant->getZExtValue()} : Range{};
		}
	}
	bool first = true;
	Range answer;
	for (auto* predecessor : predecessors(block)) {
		Range candidate = initial(predecessor, index, abi, visiting, budget);
		if (!candidate.exact()) return {};
		if (!first && answer.lo != candidate.lo) return {};
		answer = candidate;
		first = false;
	}
	return answer;
}

bool isBreakBlock(BasicBlock* block, BasicBlock* continuation) {
	auto* branch = dyn_cast<BranchInst>(block->getTerminator());
	if (!branch || !branch->isUnconditional() || branch->getSuccessor(0) != continuation)
		return false;
	bool found = false;
	for (auto& instruction : *block) {
		auto* call = dyn_cast<CallInst>(&instruction);
		if (call && call->getCalledFunction()
				&& call->getCalledFunction()->getName() == "__retdec_mips_break") found = true;
		else if (instruction.mayHaveSideEffects() && !isa<StoreInst>(instruction)
				&& !isa<BranchInst>(instruction)) return false;
		if (auto* store = dyn_cast<StoreInst>(&instruction))
			if (store->getPointerOperand()->getName() != "_asm_program_counter") return false;
	}
	return found;
}

bool prove(Loop* loop, BranchInst* guard, unsigned safe, Abi* abi,
		DominatorTree& dominators) {
	auto* header = loop->getHeader();
	auto* preheader = loop->getLoopPreheader();
	if (!preheader || !loop->getSubLoops().empty()
			|| !dominators.dominates(header, guard->getParent())) return false;
	std::set<BasicBlock*> region;
	std::deque<BasicBlock*> pending{guard->getParent()};
	while (!pending.empty()) {
		auto* block = pending.front(); pending.pop_front();
		if (!region.insert(block).second) continue;
		if (region.size() > 64 || !dominators.dominates(header, block)) return false;
		if (block != header)
			for (auto* predecessor : predecessors(block)) pending.push_back(predecessor);
	}
	for (auto* block : loop->blocks()) region.insert(block);
	Registers seed;
	for (unsigned i = 0; i < 32; ++i) {
		unsigned budget = 64;
		seed[i] = initial(preheader, i, abi, {}, budget);
	}
	seed[0] = {0, 0};
	using Key = std::pair<BasicBlock*, std::array<uint64_t, 64>>;
	std::set<Key> seen;
	std::deque<std::pair<BasicBlock*, Registers>> work{{header, seed}};
	unsigned budget = 262144, states = 0;
	bool reached = false;
	while (!work.empty()) {
		auto item = work.front(); work.pop_front();
		auto* block = item.first;
		auto registers = item.second;
		Key key; key.first = block;
		for (unsigned i = 0; i < 32; ++i) {
			key.second[2*i] = registers[i].lo;
			key.second[2*i+1] = registers[i].hi;
		}
		if (!seen.insert(key).second) continue;
		if (++states > 4096) return false;
		Values values;
		for (auto& instruction : *block) {
			if (!budget--) return false;
			if (auto* load = dyn_cast<LoadInst>(&instruction)) {
				if (!load->getType()->isIntegerTy()
						|| load->getType()->getIntegerBitWidth() > 32) return false;
				int index = reg(load->getPointerOperand(), abi);
				values[load] = index >= 0 ? registers[index] : valueRange(load, {});
			} else if (auto* store = dyn_cast<StoreInst>(&instruction)) {
				int index = reg(store->getPointerOperand(), abi);
				if (index > 0) registers[index] = valueRange(store->getValueOperand(), values);
				else if (index < 0 && store->getPointerOperand()->getName() != "_asm_program_counter"
						&& !abi->isRegister(store->getPointerOperand())) return false;
			} else if (auto* call = dyn_cast<CallInst>(&instruction)) {
				uint32_t writes;
				if (!effects(call, writes)) return false;
				for (unsigned i = 1; i < 32; ++i)
					if (writes & (uint32_t(1) << i)) registers[i] = {};
				values[call] = valueRange(call, {});
			} else if (auto* branch = dyn_cast<BranchInst>(&instruction)) {
				Range condition = branch->isConditional() ? valueRange(branch->getCondition(), values) : Range{1,1};
				if (branch == guard) {
					reached = true;
					if (!condition.exact() || condition.lo != (safe == 0 ? 1u : 0u)) return false;
					break;
				}
				for (unsigned edge = 0; edge < branch->getNumSuccessors(); ++edge) {
					if (branch->isConditional() && condition.exact() && edge != (condition.lo ? 0u : 1u)) continue;
					auto* next = branch->getSuccessor(edge);
					if (region.count(next)) work.push_back({next, registers});
				}
			} else {
				if (isa<PHINode>(instruction) || instruction.isTerminator()
						|| instruction.mayHaveSideEffects()) return false;
				for (auto& operand : instruction.operands())
					if (auto* definition = dyn_cast<Instruction>(operand.get()))
						if (definition->getParent() != block) return false;
				values[&instruction] = instruction.getNumOperands() ? operation(instruction, values) : Range{};
			}
		}
	}
	return reached;
}
}

void simplifyMipsGuards(llvm::Module* module, Abi* abi) {
	for (auto& function : *module) {
		if (function.empty()) continue;
		llvm::DominatorTree dominators(function);
		llvm::LoopInfo loops(dominators);
		std::vector<std::pair<llvm::BranchInst*, unsigned>> proven;
		for (auto& block : function) {
			auto* guard = llvm::dyn_cast<llvm::BranchInst>(block.getTerminator());
			if (!guard || !guard->isConditional()) continue;
			for (unsigned safe = 0; safe < 2; ++safe) {
				if (!isBreakBlock(guard->getSuccessor(1-safe), guard->getSuccessor(safe))) continue;
				for (auto* loop : loops)
					if (prove(loop, guard, safe, abi, dominators)) {
						proven.push_back({guard, safe}); break;
					}
			}
		}
		for (auto item : proven) {
			item.first->setCondition(llvm::ConstantInt::get(
					llvm::Type::getInt1Ty(module->getContext()), item.second == 0));
		}
	}
}
} }
