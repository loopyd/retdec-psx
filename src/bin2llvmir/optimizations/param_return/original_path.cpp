#include "original_path.h"
#include <algorithm>
namespace retdec { namespace bin2llvmir {
namespace {
using EntryPath = Disposition::EntryPath;
using PathConstants = std::array<std::optional<uint32_t>, Disposition::GprCount>;
int64_t pathSigned(uint32_t value)
{
    return value & 0x80000000 ? int64_t(value) - 0x100000000LL : int64_t(value);
}

uint32_t pathShiftRight(uint32_t value, unsigned shift)
{
    return !shift ? value : (value >> shift) | ((value & 0x80000000) ? UINT32_MAX << (32 - shift) : 0);
}

bool stepEntryPath(const Disposition::Instruction& row, PathConstants& values,
    std::optional<unsigned>& pending, bool control = false)
{
    auto before = values;
    auto word = row.word;
    unsigned op = word >> 26, rs = (word >> 21) & 31, rt = (word >> 16) & 31;
    unsigned rd = (word >> 11) & 31, shift = (word >> 6) & 31, fn = word & 63;
    bool load = op == 32 || op == 33 || op == 35 || op == 36 || op == 37;
    bool store = op == 40 || op == 41 || op == 43;
    std::optional<unsigned> destination;
    std::optional<uint32_t> output;
    if (!control && !store) {
        if (load) destination = rt;
        else if (op == 0) {
            destination = rd;
            if ((fn == 0 || fn == 2 || fn == 3) && rs == 0) {
                if (before[rt]) output = fn == 0 ? *before[rt] << shift
                    : fn == 2 ? *before[rt] >> shift : pathShiftRight(*before[rt], shift);
            } else if ((fn == 4 || fn == 6 || fn == 7) && shift == 0) {
                if (before[rs] && before[rt]) {
                    unsigned count = *before[rs] & 31;
                    output = fn == 4 ? *before[rt] << count
                        : fn == 6 ? *before[rt] >> count : pathShiftRight(*before[rt], count);
                }
            } else if ((fn == 33 || fn == 35 || (fn >= 36 && fn <= 39) || fn == 42 || fn == 43) && shift == 0) {
                if (before[rs] && before[rt]) {
                    uint32_t left = *before[rs], right = *before[rt];
                    output = fn == 33 ? left + right : fn == 35 ? left - right
                        : fn == 36 ? left & right : fn == 37 ? left | right : fn == 38 ? left ^ right
                        : fn == 39 ? ~(left | right) : fn == 42 ? uint32_t(pathSigned(left) < pathSigned(right))
                        : uint32_t(left < right);
                }
            } else return false;
        } else if (op >= 9 && op <= 14) {
            destination = rt;
            if (before[rs]) {
                uint32_t value = *before[rs], immediate = uint32_t(int32_t(int16_t(word & 0xffff)));
                output = op == 9 ? value + immediate : op == 10 ? uint32_t(pathSigned(value) < pathSigned(immediate))
                    : op == 11 ? uint32_t(value < immediate) : op == 12 ? value & (word & 0xffff)
                    : op == 13 ? value | (word & 0xffff) : value ^ (word & 0xffff);
            }
        } else if (op == 15 && rs == 0) { destination = rt; output = (word & 0xffff) << 16; }
        else return false;
    }
    if (destination && *destination && std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), *destination) != 1)
        return false;
    if (pending && (load || destination != pending)) values[*pending].reset();
    pending.reset();
    if (destination && *destination) {
        if (load) pending = *destination;
        else values[*destination] = output;
    }
    values[0] = 0;
    return true;
}

}

std::optional<common::OriginalSymbolicFrame> recoverBoundPathFrame(const Disposition::EntryPath& path)
{
    struct Value {
        unsigned entry;
        int32_t offset = 0;
        uint64_t store = 0, load = 0;
        bool operator==(const Value& other) const {
            return entry == other.entry && offset == other.offset && store == other.store && load == other.load;
        }
        bool operator!=(const Value& other) const { return !(*this == other); }
    };
    std::array<std::optional<Value>, Disposition::GprCount> values{};
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) values[reg] = Value{reg};
    std::map<int32_t, Value> slots;
    std::optional<std::pair<unsigned, std::optional<Value>>> pending;
    std::optional<Value> sampledLink;
    common::OriginalSymbolicFrame frame;
    int32_t spOffset = 0;
    bool restored = false, terminal = false;
    std::set<uint64_t> visited;
    if (path.instructions.empty() || path.instructions.size() > 256) return {};
    frame.entryPc = uint32_t(path.instructions.front().pc);
    for (size_t index = 0; index < path.instructions.size(); ++index) {
        const auto& row = path.instructions[index];
        if (row.pc > UINT32_MAX - 4 || row.pc % 4 || !visited.insert(row.pc).second) return {};
        uint32_t word = row.word;
        unsigned op = word >> 26, rs = (word >> 21) & 31, rt = (word >> 16) & 31;
        unsigned rd = (word >> 11) & 31, shift = (word >> 6) & 31, fn = word & 63;
        auto before = values;
        std::optional<unsigned> destination;
        std::optional<Value> output;
        bool load = op == 32 || op == 33 || op == 35 || op == 36 || op == 37;
        bool store = op == 40 || op == 41 || op == 43;
        bool branch = op == 2 || op == 4 || op == 5 || ((op == 6 || op == 7) && rt == 0)
            || (op == 1 && (rt == 0 || rt == 1));
        if (word == 0x03e00008) {
            if (terminal || row.pc != path.terminalPc || index + 2 != path.instructions.size()
                || path.instructions[index + 1].pc != row.pc + 4 || (pending && pending->first == 31)) return {};
            sampledLink = before[31]; terminal = true;
        } else if (branch) {
            if ((op != 2 && rs == 29) || ((op == 4 || op == 5) && rt == 29)) return {};
            if (terminal || index + 2 >= path.instructions.size()
                || path.instructions[index + 1].pc != row.pc + 4) return {};
        } else if (load || store) {
            if (load && rt == 29) return {};
            if (load) destination = rt;
            if (rs == 29) {
                if ((op != 35 && op != 43) || !frame.frameBytes || restored) return {};
                int32_t offset = spOffset + int16_t(word & 0xffff);
                if (offset < -int32_t(frame.frameBytes) || offset > -4 || offset % 4) return {};
                if (store) {
                    if (rt == 29 || !before[rt] || before[rt]->entry == 29) return {};
                    slots.insert_or_assign(offset, Value{before[rt]->entry, offset, row.pc, 0});
                } else {
                    auto slot = slots.find(offset);
                    if (slot != slots.end()) { output = slot->second; output->load = row.pc; }
                }
            } else if (store) return {};
        } else if (op == 9 && rs == 29 && rt == 29) {
            int32_t adjustment = int16_t(word & 0xffff);
            if (!frame.frameBytes) {
                if (adjustment >= 0 || adjustment % 4 || spOffset) return {};
                frame.frameBytes = uint32_t(-adjustment); frame.allocationPc = uint32_t(row.pc);
                spOffset = adjustment;
            } else {
                if (restored || adjustment != int32_t(frame.frameBytes) || spOffset != -adjustment) return {};
                spOffset = 0; restored = true;
            }
            destination = 29; output = Value{29};
        } else {
            if (op == 0) {
                destination = rd;
                bool immediateShift = (fn == 0 || fn == 2 || fn == 3) && rs == 0;
                bool variableShift = (fn == 4 || fn == 6 || fn == 7) && shift == 0;
                bool arithmetic = (fn == 33 || fn == 35 || (fn >= 36 && fn <= 39) || fn == 42 || fn == 43) && shift == 0;
                if ((!immediateShift && !variableShift && !arithmetic) || rt == 29 || (!immediateShift && rs == 29)) return {};
                if (fn == 0 && !shift) output = before[rt];
                else if ((fn == 33 || fn == 37) && (rs == 0 || rt == 0)) output = before[rs == 0 ? rt : rs];
            } else if (op >= 9 && op <= 14) {
                if (rs == 29) return {};
                destination = rt;
                if (op == 9 && (word & 0xffff) == 0) output = before[rs];
            } else if (op == 15 && rs == 0) destination = rt;
            else return {};
            if (destination == 29) return {};
        }
        if (pending && (load || destination != std::optional<unsigned>{pending->first}))
            values[pending->first] = pending->second;
        pending.reset();
        if (destination && *destination) {
            if (load) pending = std::make_pair(*destination, output);
            else values[*destination] = output;
        }
    }
    if (!terminal || !restored || spOffset || pending || !sampledLink || sampledLink->entry != 31
        || !sampledLink->load || values[31] != sampledLink) return {};
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
        const auto& value = values[reg];
        if (!value || value->entry != reg || !value->store || !value->load) continue;
        common::OriginalSymbolicFrame::Register row;
        row.reg = reg; row.offset = value->offset; row.storePc = value->store;
        row.loadPcs = {value->load}; row.exitPcs = {path.terminalPc};
        frame.registers.push_back(std::move(row));
    }
    if (std::none_of(frame.registers.begin(), frame.registers.end(), [](const auto& row) { return row.reg == 31; })) return {};
    return frame;
}

std::optional<Disposition::EntryPath> deriveBoundEntryPath(const Disposition::Call& call,
    const RegisterState& before, const std::map<unsigned, Disposition::Definition>& definitions,
    const Disposition::Evidence& caller, const common::ReviewedOriginalFunction& identity,
    const Disposition::Evidence& evidence, const common::PsxMemoryContext& context)
{
    if (!call.target || call.pc > UINT32_MAX - 8) return {};
    auto instruction = std::find_if(caller.instructions.begin(), caller.instructions.end(),
        [&](const auto& row) { return row.pc == call.pc; });
    if (instruction == caller.instructions.end() || instruction->word >> 26 != 3
        || instruction->bytes != 4 || !instruction->mapped || instruction->undef || instruction->owner != caller.symbol
        || *call.target != (((call.pc + 4) & 0xf0000000) | ((instruction->word & 0x03ffffff) << 2))) return {};
    auto callBytes = context.resolve(call.pc, 4);
    if (!callBytes || instruction->word != (uint32_t(callBytes->bytes[0]) | uint32_t(callBytes->bytes[1]) << 8
        | uint32_t(callBytes->bytes[2]) << 16 | uint32_t(callBytes->bytes[3]) << 24)) return {};
    if (evidence.start != identity.start || evidence.end != identity.end || identity.start != *call.target
        || evidence.start >= evidence.end || evidence.end - evidence.start > 1024
        || evidence.start % 4 || evidence.end % 4 || evidence.instructions.empty()
        || evidence.instructions.size() > 256) return {};
    auto span = context.resolve(evidence.start, evidence.end - evidence.start);
    if (!span || span->image->id != identity.imageId) return {};
    std::map<uint64_t, const Disposition::Instruction*> instructions;
    for (const auto& row : evidence.instructions) {
        auto bytes = context.resolve(row.pc, 4);
        if (row.pc < evidence.start || row.pc >= evidence.end || row.pc % 4 || row.bytes != 4
            || !row.mapped || row.undef || row.owner != evidence.symbol || !instructions.emplace(row.pc, &row).second
            || !bytes || bytes->image->id != identity.imageId) return {};
        uint32_t word = uint32_t(bytes->bytes[0]) | uint32_t(bytes->bytes[1]) << 8
            | uint32_t(bytes->bytes[2]) << 16 | uint32_t(bytes->bytes[3]) << 24;
        if (word != row.word) return {};
    }
    EntryPath path;
    path.callee = identity.key; path.contextHash = context.identity();
    PathConstants values{}; values[0] = 0;
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
        const auto& value = before[reg];
        if (!value.constant || value.missing || !value.bad.empty()) continue;
        if (value.definitions.empty() || value.equalityEvidence.empty()) return {};
        for (auto id : value.definitions) {
            auto definition = definitions.find(id);
            if (definition == definitions.end() || definition->second.reg != reg || definition->second.width != 32
                || definition->second.constant != value.constant || !definition->second.bad.empty()) return {};
        }
        for (auto pc : value.equalityEvidence)
            if (std::none_of(caller.instructions.begin(), caller.instructions.end(), [&](const auto& row) { return row.pc == pc; })) return {};
        path.bindings.push_back({reg, *value.constant, {value.definitions.begin(), value.definitions.end()},
            {value.equalityEvidence.begin(), value.equalityEvidence.end()}});
        values[reg] = value.constant;
    }
    std::set<uint64_t> visited;
    std::optional<unsigned> pending;
    auto take = [&](uint64_t pc) -> const Disposition::Instruction* {
        auto row = instructions.find(pc);
        if (row == instructions.end() || !visited.insert(pc).second || visited.size() > 256) return nullptr;
        path.instructions.push_back({pc, row->second->word});
        return row->second;
    };
    uint64_t pc = evidence.start;
    while (true) {
        auto* row = take(pc);
        if (!row) return {};
        uint32_t word = row->word;
        unsigned op = word >> 26, rs = (word >> 21) & 31, rt = (word >> 16) & 31;
        bool terminal = word == 0x03e00008, jump = op == 2;
        bool branch = op == 4 || op == 5 || ((op == 6 || op == 7) && rt == 0)
            || (op == 1 && (rt == 0 || rt == 1));
        if (!terminal && !jump && !branch) {
            if (!stepEntryPath(*row, values, pending)) return {};
            path.edges.push_back({pc, pc + 4, {}, "fallthrough"}); pc += 4; continue;
        }
        uint64_t target = 0;
        bool taken = true;
        if (branch) {
            if (!values[rs] || ((op == 4 || op == 5) && !values[rt])) return {};
            uint32_t left = *values[rs];
            taken = op == 4 ? left == *values[rt] : op == 5 ? left != *values[rt]
                : op == 6 ? pathSigned(left) <= 0 : op == 7 ? pathSigned(left) > 0
                : rt == 0 ? pathSigned(left) < 0 : pathSigned(left) >= 0;
            EntryPath::Branch decision{pc, taken, {{rs, left}}};
            if (op == 4 || op == 5) decision.operands.push_back({rt, *values[rt]});
            path.branches.push_back(std::move(decision));
            int64_t destination = int64_t(pc) + 4 + int64_t(int16_t(word & 0xffff)) * 4;
            if (destination < 0 || destination > UINT32_MAX) return {};
            target = taken ? uint64_t(destination) : pc + 8;
        } else if (jump) target = ((pc + 4) & 0xf0000000) | ((word & 0x03ffffff) << 2);
        if (!stepEntryPath(*row, values, pending, true)) return {};
        auto* slot = take(pc + 4);
        if (!slot || !stepEntryPath(*slot, values, pending)) return {};
        path.edges.push_back({pc, pc + 4, pc, "delay-slot"});
        if (terminal) {
            if (pending) return {};
            path.terminalPc = pc;
            if (std::any_of(path.bindings.begin(), path.bindings.end(), [&](const auto& binding) {
                    return binding.reg == 31 && binding.constant == uint32_t(call.pc + 8);
                })) path.symbolicFrame = recoverBoundPathFrame(path);
            return path;
        }
        path.edges.push_back({pc + 4, target, {}, taken ? "branch" : "fallthrough"});
        pc = target;
    }
}

} }
