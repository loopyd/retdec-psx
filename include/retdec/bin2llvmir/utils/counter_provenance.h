#ifndef RETDEC_COUNTER_PROVENANCE_H
#define RETDEC_COUNTER_PROVENANCE_H
#include <llvm/ADT/Optional.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Metadata.h>

namespace retdec { namespace bin2llvmir {
namespace counter_provenance {
inline llvm::ConstantInt* constant(llvm::Value* value, uint64_t expected) {
	auto* number = llvm::dyn_cast<llvm::ConstantInt>(value);
	return number && number->getZExtValue() == expected ? number : nullptr;
}
inline llvm::Metadata* origin(llvm::Instruction* instruction) {
	auto* node = instruction->getMetadata("insn.addr");
	return node && node->getNumOperands() == 1 ? node->getOperand(0).get() : nullptr;
}
inline bool ordered(llvm::Instruction* first, llvm::Instruction* last) {
	if (first->getParent() != last->getParent()) return false;
	for (auto* item = first->getNextNode(); item; item = item->getNextNode())
		if (item == last) return true;
	return false;
}

inline bool capture(llvm::Module& module) {
	bool changed = false;
	for (auto& function : module) for (auto& block : function) for (auto& instruction : block) {
		auto* store = llvm::dyn_cast<llvm::StoreInst>(&instruction);
		if (!store || store->isAtomic() || !store->getValueOperand()->getType()->isIntegerTy(8)) continue;
		auto* trunc = llvm::dyn_cast<llvm::TruncInst>(store->getValueOperand());
		auto* add = trunc ? llvm::dyn_cast<llvm::BinaryOperator>(trunc->getOperand(0)) : nullptr;
		if (!add || add->getOpcode() != llvm::Instruction::Add || !add->getType()->isIntegerTy(32)
				|| add->hasNoSignedWrap() || add->hasNoUnsignedWrap() || !constant(add->getOperand(1), 1)) continue;
		auto* extend = llvm::dyn_cast<llvm::ZExtInst>(add->getOperand(0));
		auto* load = extend ? llvm::dyn_cast<llvm::LoadInst>(extend->getOperand(0)) : nullptr;
		if (!load || !load->getType()->isIntegerTy(8) || load->isAtomic()
				|| !ordered(load, add) || !ordered(add, store)) continue;
		for (auto* use : add->users()) {
			auto* mask = llvm::dyn_cast<llvm::BinaryOperator>(use);
			if (!mask || mask->getOpcode() != llvm::Instruction::And || !constant(mask->getOperand(1), 255)) continue;
			for (auto* consumer : mask->users()) {
				auto* compare = llvm::dyn_cast<llvm::ICmpInst>(consumer);
				if (!compare || !compare->isEquality() || compare->getOperand(0) != mask || !ordered(store, compare)) continue;
				auto* threshold = llvm::dyn_cast<llvm::ConstantInt>(compare->getOperand(1));
				if (!threshold || threshold->getZExtValue() > 255) continue;
				auto* a = origin(load); auto* b = origin(add); auto* c = origin(store); auto* d = origin(compare);
				if (!a || !b || !c || !d) continue;
				auto number = [&](uint64_t value) -> llvm::Metadata* {
					return llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(llvm::Type::getInt64Ty(module.getContext()), value));
				};
				store->setMetadata("retdec.counter.origin", llvm::MDNode::get(module.getContext(),
						{number(1), a, b, c, d, number(32), number(8), number(1),
						 number(threshold->getZExtValue()), number(compare->getPredicate())}));
				changed = true;
			}
		}
	}
	return changed;
}

enum class TestedValue { Old, Incremented };

struct CounterUpdate {
	llvm::LoadInst* load;
	llvm::BinaryOperator* add;
	llvm::StoreInst* store;
	llvm::ICmpInst* comparison;
	uint64_t threshold;
	TestedValue tested;
};

inline llvm::Optional<CounterUpdate> recognizedCounter(llvm::MDNode* record, llvm::StoreInst* store) {
	if (!record || record->getNumOperands() != 10 || store->isAtomic()) return llvm::None;
	auto number = [&](unsigned index) -> llvm::ConstantInt* {
		return llvm::mdconst::dyn_extract<llvm::ConstantInt>(record->getOperand(index));
	};
	for (unsigned i = 0; i < 10; ++i)
		if (!number(i)) return llvm::None;
	if (number(0)->getZExtValue() != 1 || number(5)->getZExtValue() != 32
			|| number(6)->getZExtValue() != 8 || number(7)->getZExtValue() != 1
			|| number(8)->getZExtValue() > 255) return llvm::None;
	auto* add = llvm::dyn_cast<llvm::BinaryOperator>(store->getValueOperand());
	if (!add || add->getOpcode() != llvm::Instruction::Add || !add->getType()->isIntegerTy(8)
			|| add->hasNoSignedWrap() || add->hasNoUnsignedWrap() || !constant(add->getOperand(1), 1))
		return llvm::None;
	auto* load = llvm::dyn_cast<llvm::LoadInst>(add->getOperand(0));
	if (!load || load->isAtomic() || load->getPointerOperand() != store->getPointerOperand()
			|| !ordered(load, add) || !ordered(add, store)) return llvm::None;
	for (auto* item = load->getNextNode(); item != store; item = item->getNextNode())
		if (item->mayHaveSideEffects()) return llvm::None;
	uint64_t threshold = number(8)->getZExtValue();
	llvm::ICmpInst* match = nullptr;
	TestedValue tested = TestedValue::Old;
	for (auto* item = store->getNextNode(); item; item = item->getNextNode()) {
		auto* compare = llvm::dyn_cast<llvm::ICmpInst>(item);
		if (!compare || !compare->isEquality()) continue;
		TestedValue candidate;
		if (compare->getOperand(0) == load && constant(compare->getOperand(1), (threshold - 1) & 255))
			candidate = TestedValue::Old;
		else if (compare->getOperand(0) == add && constant(compare->getOperand(1), threshold))
			candidate = TestedValue::Incremented;
		else continue;
		if (origin(load) != record->getOperand(1).get()
				|| origin(add) != record->getOperand(2).get()
				|| origin(store) != record->getOperand(3).get()
				|| origin(compare) != record->getOperand(4).get()) continue;
		if (match) return llvm::None;
		match = compare;
		tested = candidate;
	}
	if (!match) return llvm::None;
	return CounterUpdate{load, add, store, match, threshold, tested};
}

inline void validate(llvm::Module& module) {
	for (auto& function : module) for (auto& block : function) for (auto& instruction : block) {
		auto* store = llvm::dyn_cast<llvm::StoreInst>(&instruction);
		if (!store) continue;
		auto* node = store->getMetadata("retdec.counter.origin");
		if (!node) continue;
		store->setMetadata("retdec.counter.origin", nullptr);
		auto update = recognizedCounter(node, store);
		if (!update) continue;
		store->setMetadata("retdec.counter.validated", node);
		update->comparison->setMetadata("retdec.counter.validated", node);
	}
}

inline bool restoreTestedValue(llvm::Module& module) {
	bool changed = false;
	for (auto& function : module) for (auto& block : function) for (auto& instruction : block) {
		auto* store = llvm::dyn_cast<llvm::StoreInst>(&instruction);
		if (!store) continue;
		auto* record = store->getMetadata("retdec.counter.validated");
		if (!record) continue;
		store->setMetadata("retdec.counter.validated", nullptr);
		auto update = recognizedCounter(record, store);
		if (!update || update->comparison->getMetadata("retdec.counter.validated") != record) continue;
		update->comparison->setMetadata("retdec.counter.validated", nullptr);
		if (update->tested == TestedValue::Incremented) continue;
		update->comparison->setOperand(0, update->add);
		update->comparison->setOperand(1, llvm::ConstantInt::get(update->add->getType(), update->threshold));
		changed = true;
	}
	return changed;
}
} } }
#endif
