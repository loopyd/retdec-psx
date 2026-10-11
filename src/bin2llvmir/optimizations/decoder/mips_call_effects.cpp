#include "mips_call_effects.h"
#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Metadata.h>
#include "retdec/bin2llvmir/providers/asm_instruction.h"
#include "retdec/bin2llvmir/providers/fileimage.h"
#include "retdec/bin2llvmir/providers/config.h"
#include "retdec/fileformat/file_format/elf/elf_format.h"
#include "retdec/loader/loader/image.h"

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

template<typename Reader>
MipsLeafEffects inspectLeaf(uint32_t entry, Reader readWord) {
	MipsLeafEffects result;
	if ((entry & 3) || entry > UINT32_MAX - 1024) return result;
	std::map<uint32_t, unsigned> state;
	std::set<uint32_t> slots, instructions;
	auto read = [&](uint32_t pc, uint32_t& word) {
		if (pc < entry || pc - entry >= 1024 || (pc & 3)) return false;
		if (!readWord(pc, word)) return false;
		instructions.insert(pc);
		if (instructions.size() <= 256) result.words.emplace(pc, word);
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
			if (ret) result.normalReturnPcs.push_back(pc);
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
	std::sort(result.normalReturnPcs.begin(), result.normalReturnPcs.end());
	return result;
}

}

MipsLeafEffects inspectMipsLeaf(llvm::Module* module, FileImage* image,
		uint32_t entry) {
	if (!mipsOne(image)) return {};
	return inspectLeaf(entry, [&](uint32_t pc, uint32_t& word) {
		auto* value = image->getConstantInt(llvm::Type::getInt32Ty(module->getContext()), pc);
		if (!value) return false;
		word = value->getZExtValue();
		return true;
	});
}

std::optional<common::OriginalCalleeContexts> inspectOriginalMipsCallees(
	FileImage* image, const config::Parameters& parameters,
	const common::ReturnDisposition::Evidence& root) {
	const auto& scope = parameters.getOriginalCallScope();
	if (!parameters.isOriginalOnlyReturnRecovery() || !scope || !image
		|| root.start != scope->root.start || root.end != scope->root.end
		|| root.selection != "selected-root") return {};
	std::map<uint32_t, std::vector<uint64_t>> targets;
	common::OriginalCalleeContexts result;
	result.imageId = scope->root.imageId; result.payloadHash = scope->payloadHash;
	for (const auto& row : root.instructions) {
		if (row.word >> 26 != 3 || !row.mapped || row.undef || row.bytes != 4 || row.owner != root.symbol
			|| row.pc < root.start || row.pc >= root.end || row.pc % 4) continue;
		uint32_t target = ((uint32_t(row.pc) + 4) & 0xf0000000) | ((row.word & 0x03ffffff) << 2);
		if (target == scope->root.start || std::any_of(scope->callees.begin(), scope->callees.end(),
			[&](const auto& peer) { return target == peer.start; })) continue;
		if (!targets.count(target) && targets.size() == 32) {
			result.remaining = {"direct-callee-context-count-bound"}; break;
		}
		targets[target].push_back(row.pc);
	}
	if (targets.empty()) return {};
	auto* format = image->getFileFormat();
	auto load = parameters.getSectionVMA();
	if (!format || !format->isRawData() || format->getSha256() != scope->payloadHash
		|| scope->payloadHash.size() != 64 || load.isUndefined() || load.getValue() > UINT32_MAX) {
		result.remaining.push_back("original-callee-image-mapping-unresolved"); return result;
	}
	const auto& payload = format->getBytes();
	result.mappingStart = uint32_t(load.getValue()); result.mappingBytes = payload.size();
	auto physical = image->getImage()->getRawSegmentData(load);
	if (payload.empty() || payload.size() > (uint64_t(1) << 32) - result.mappingStart
		|| payload != format->getLoadedBytes() || !physical.first || physical.second != payload.size()
		|| !std::equal(payload.begin(), payload.end(), physical.first)) {
		result.remaining.push_back("original-callee-physical-bytes-unresolved"); return result;
	}
	std::set<uint32_t> claimed;
	std::size_t retained = 0;
	for (const auto& target : targets) {
		common::OriginalCalleeContext context; context.entry = target.first; context.callPcs = target.second;
		auto effects = inspectLeaf(target.first, [&](uint32_t pc, uint32_t& word) {
			auto overlaps = [&](const auto& member) { return member.start <= pc && pc < member.end; };
			if (pc < result.mappingStart || uint64_t(pc) - result.mappingStart + 4 > payload.size()
				|| claimed.count(pc) || overlaps(scope->root)
				|| std::any_of(scope->callees.begin(), scope->callees.end(), overlaps)) return false;
			auto offset = uint64_t(pc) - result.mappingStart;
			word = uint32_t(payload[offset]) | uint32_t(payload[offset + 1]) << 8
				| uint32_t(payload[offset + 2]) << 16 | uint32_t(payload[offset + 3]) << 24;
			return true;
		});
		if (retained + effects.words.size() > 4096) {
			result.remaining.push_back("direct-callee-context-word-bound"); break;
		}
		context.words = std::move(effects.words); context.normalReturnPcs = std::move(effects.normalReturnPcs);
		if (effects.known) context.mayWriteGprs = effects.writes;
		for (const auto& word : context.words) claimed.insert(word.first);
		retained += context.words.size(); result.candidates.push_back(std::move(context));
	}
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
