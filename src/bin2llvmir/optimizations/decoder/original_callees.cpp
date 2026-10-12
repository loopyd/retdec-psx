#include "retdec/bin2llvmir/optimizations/decoder/decoder.h"

#include <deque>
#include <set>

namespace retdec { namespace bin2llvmir {

void Decoder::discoverOriginalDirectTarget(uint64_t callPc, uint64_t target)
{
	const auto& context = _config->getConfig().parameters.getPsxMemoryContext();
	if (!context || _originalExtents.count(target) || target % 4 || target > UINT32_MAX) return;
	auto source = context->resolve(target, 4);
	if (!source) return;
	auto conflict = [&](uint64_t pc) {
		auto extent = _originalExtents.upper_bound(pc);
		return extent != _originalExtents.begin() && pc < std::prev(extent)->second;
	};
	common::OriginalDiscoveredFunction node;
	node.start = target; node.target = source->image->target; node.imageId = source->image->id;
	node.key = node.target + "@" + common::Address(target).toHexString(); node.contextHash = context->identity();
	auto fail = [&](const char* reason) {
		node.remaining.push_back(reason);
	};
	if (_originalDiscovered.size() >= 32 || _originalDiscoveredWords >= 4096) {
		auto owner = _originalExtents.upper_bound(callPc);
		if (owner != _originalExtents.begin()) _originalDispositions[std::prev(owner)->first].evidence.obligations
			.push_back({callPc, "call", "direct-callee-discovery-bound"});
		return;
	}
	std::deque<uint64_t> pending{target};
	std::set<uint64_t> slots;
	auto read = [&](uint64_t pc, uint32_t& word, bool& transfer) {
		if (pc < target || pc - target >= 1024 || pc % 4 || conflict(pc)) return false;
		auto bytes = context->resolve(pc, 4);
		if (!bytes || bytes->image->id != node.imageId) return false;
		if (!node.words.count(pc) && (node.words.size() >= 256 || _originalDiscoveredWords + node.words.size() >= 4096)) return false;
		word = uint32_t(bytes->bytes[0]) | uint32_t(bytes->bytes[1]) << 8
			| uint32_t(bytes->bytes[2]) << 16 | uint32_t(bytes->bytes[3]) << 24;
		cs_insn* instruction = nullptr;
		auto handle = _c2l->getCapstoneEngine();
		auto decoded = cs_disasm(handle, bytes->bytes, 4, pc, 1, &instruction);
		if (!decoded) return false;
		transfer = cs_insn_group(handle, instruction, CS_GRP_JUMP)
			|| cs_insn_group(handle, instruction, CS_GRP_CALL)
			|| cs_insn_group(handle, instruction, CS_GRP_RET)
			|| cs_insn_group(handle, instruction, CS_GRP_INT)
			|| cs_insn_group(handle, instruction, CS_GRP_IRET);
		bool valid = instruction->size == 4;
		cs_free(instruction, decoded);
		if (!valid) return false;
		node.words.emplace(pc, word);
		return true;
	};
	while (!pending.empty()) {
		auto pc = pending.front(); pending.pop_front();
		if (node.words.count(pc)) {
			if (slots.count(pc)) fail("discovered-delay-slot-entry");
			continue;
		}
		uint32_t word;
		bool transfer = false;
		if (!read(pc, word, transfer)) { fail("discovered-image-or-instruction-bound"); break; }
		auto op = word >> 26, rt = (word >> 16) & 31;
		bool ret = word == 0x03e00008;
		bool branch = op == 4 || op == 5 || ((op == 6 || op == 7) && rt == 0)
			|| (op == 1 && (rt == 0 || rt == 1));
		bool jump = op == 2, call = op == 3;
		bool indirect = op == 0 && ((word & 63) == 8 || (word & 63) == 9);
		if (transfer && !ret && !branch && !jump && !call && !indirect) {
			fail("discovered-unsupported-control-transfer"); break;
		}
		if (ret || branch || jump || call || indirect) {
			uint32_t slot;
			bool slotTransfer = false;
			if (node.words.count(pc + 4) || !read(pc + 4, slot, slotTransfer)) { fail("discovered-delay-slot-unresolved"); break; }
			auto slotOp = slot >> 26;
			if (slotTransfer || slotOp == 1 || (slotOp >= 2 && slotOp <= 7)
				|| (slotOp == 0 && ((slot & 63) == 8 || (slot & 63) == 9))) {
				fail("discovered-transfer-in-delay-slot"); break;
			}
			slots.insert(pc + 4);
			if (ret) continue;
			if (indirect) { fail("discovered-indirect-transfer-unresolved"); break; }
			if (branch) {
				auto destination = int64_t(pc) + 4 + int64_t(int16_t(word)) * 4;
				if (destination < 0 || destination > UINT32_MAX) { fail("discovered-branch-overflow"); break; }
				pending.push_back(uint64_t(destination)); pending.push_back(pc + 8); continue;
			}
			if (jump) {
				pending.push_back(((pc + 4) & 0xf0000000) | ((word & 0x03ffffff) << 2)); continue;
			}
			pending.push_back(pc + 8); continue;
		}
		if ((op == 0 && ((word & 63) == 12 || (word & 63) == 13)) || op == 16 || op == 17 || op == 18 || op == 19) {
			fail("discovered-exception-or-coprocessor-transfer"); break;
		}
		pending.push_back(pc + 4);
	}
	if (node.words.empty()) return;
	node.end = node.words.rbegin()->first + 4;
	auto span = context->resolve(node.start, node.end - node.start);
	if (!span || span->image->id != node.imageId || conflict(node.end - 4)) return;
	auto next = _originalExtents.lower_bound(node.start);
	if (next != _originalExtents.end() && next->first < node.end) return;
	_originalDiscoveredWords += node.words.size();
	_originalDiscovered.emplace(target, std::move(node));
	_originalExtents.emplace(target, _originalDiscovered.at(target).end);
	uint64_t first = target, previous = target;
	for (const auto& word : _originalDiscovered.at(target).words) {
		if (word.first > previous + 4) {
			_ranges.addPrimary(common::Address(first), common::Address(previous + 4)); first = word.first;
		}
		previous = word.first;
	}
	_ranges.addPrimary(common::Address(first), common::Address(previous + 4));
	createFunction(common::Address(target));
}

} }
