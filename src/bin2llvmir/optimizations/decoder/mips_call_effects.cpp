#include "mips_call_effects.h"
#include <functional>
#include <map>
#include <set>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Metadata.h>
#include "retdec/bin2llvmir/providers/asm_instruction.h"
#include "retdec/bin2llvmir/providers/fileimage.h"
#include "retdec/bin2llvmir/providers/config.h"
#include "retdec/fileformat/file_format/elf/elf_format.h"

namespace retdec { namespace bin2llvmir {
namespace {

bool ordinary(uint32_t word, uint32_t& writes) {
	unsigned op = word >> 26, rs = (word >> 21) & 31;
	unsigned rt = (word >> 16) & 31, rd = (word >> 11) & 31;
	unsigned shift = (word >> 6) & 31, fn = word & 63;
	unsigned destination = 0;
	if (op == 0) {
		if (fn == 0 || fn == 2 || fn == 3) {
			if (rs != 0) return false;
		} else if (fn == 4 || fn == 6 || fn == 7 || fn == 33
				|| fn == 35 || fn == 36 || fn == 37 || fn == 38
				|| fn == 39 || fn == 42 || fn == 43) {
			if (shift != 0) return false;
		} else return false;
		destination = rd;
	} else if (op == 9 || (op >= 10 && op <= 15)
			|| op == 32 || op == 33 || op == 35 || op == 36 || op == 37) {
		if (op == 15 && rs != 0) return false;
		destination = rt;
	} else return false;
	if (destination) writes |= uint32_t(1) << destination;
	return true;
}

bool mipsOne(FileImage* image) {
	auto* elf = dynamic_cast<retdec::fileformat::ElfFormat*>(image->getFileFormat());
	return elf && elf->getTargetArchitecture() == retdec::fileformat::Architecture::MIPS
			&& (elf->getFileFlags() & 0xf0000000) == 0
			&& elf->isLittleEndian();
}

}

MipsLeafEffects inspectMipsLeaf(llvm::Module* module, FileImage* image,
		uint32_t entry) {
	MipsLeafEffects result;
	if (!mipsOne(image) || (entry & 3) || entry > UINT32_MAX - 1024) return result;
	std::map<uint32_t, unsigned> state;
	std::set<uint32_t> slots, instructions;
	auto read = [&](uint32_t pc, uint32_t& word) {
		if (pc < entry || pc - entry >= 1024 || (pc & 3)) return false;
		auto* value = image->getConstantInt(llvm::Type::getInt32Ty(module->getContext()), pc);
		if (!value) return false;
		word = value->getZExtValue();
		instructions.insert(pc);
		return instructions.size() <= 256;
	};
	std::function<bool(uint32_t)> visit = [&](uint32_t pc) {
		if (slots.count(pc)) return false;
		if (state[pc]) return state[pc] == 2;
		state[pc] = 1;
		uint32_t word;
		if (!read(pc, word)) return false;
		unsigned op = word >> 26, rt = (word >> 16) & 31;
		bool ret = word == 0x03e00008;
		bool branch = op == 4 || op == 5 || ((op == 6 || op == 7) && rt == 0);
		bool jump = op == 2;
		if (ret || branch || jump) {
			uint32_t slot;
			if (state.count(pc + 4) || !read(pc + 4, slot)
					|| !ordinary(slot, result.writes)) return false;
			slots.insert(pc + 4);
			if (branch) {
				int64_t destination = int64_t(pc) + 4 + int64_t(int16_t(word)) * 4;
				if (destination < 0 || destination > UINT32_MAX
						|| !visit(uint32_t(destination)) || !visit(pc + 8)) return false;
			} else if (jump) {
				uint32_t destination = ((pc + 4) & 0xf0000000) | ((word & 0x03ffffff) << 2);
				if (!visit(destination)) return false;
			}
		} else if (!ordinary(word, result.writes) || !visit(pc + 4)) return false;
		state[pc] = 2;
		return true;
	};
	result.known = visit(entry) && !(result.writes & (uint32_t(1) << 31));
	result.instructions = instructions.size();
	if (!result.known) result.writes = UINT32_MAX;
	return result;
}

void annotateMipsLeafCalls(llvm::Module* module, FileImage* image) {
	if (!mipsOne(image)) return;
	auto* config = ConfigProvider::getConfig(module);
	if (!config) return;
	std::map<uint32_t, MipsLeafEffects> summaries;
	for (auto& pair : AsmInstruction::getLlvmToCapstoneInsnMap(module)) {
		AsmInstruction instruction(pair.first);
		auto address = instruction.getAddress();
		auto* value = image->getConstantInt(llvm::Type::getInt32Ty(module->getContext()), address);
		if (!value) continue;
		uint32_t word = value->getZExtValue();
		if ((word >> 26) != 3) continue;
		uint32_t target = ((uint32_t(address) + 4) & 0xf0000000) | ((word & 0x03ffffff) << 2);
		if (!summaries.count(target)) summaries[target] = inspectMipsLeaf(module, image, target);
		const auto& effects = summaries.at(target);
		if (!effects.known) continue;
		AsmInstruction slot(module, address + 4);
		if (!slot) continue;
		for (auto& ir : slot) {
			auto* call = llvm::dyn_cast<llvm::CallInst>(&ir);
			if (!call || !call->getCalledFunction()
					|| config->getFunctionAddress(call->getCalledFunction()) != target)
				continue;
			auto& context = module->getContext();
			auto number = [&](uint32_t n) -> llvm::Metadata* {
				return llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(
						llvm::Type::getInt32Ty(context), n));
			};
			call->setMetadata("retdec.mips.leaf.effects", llvm::MDNode::get(context,
					{number(target), number(effects.writes), number(effects.instructions)}));
		}
	}
}

} }
