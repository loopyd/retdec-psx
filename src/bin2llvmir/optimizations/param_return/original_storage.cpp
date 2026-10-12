#include "original_storage.h"
#include <algorithm>
#include <iterator>
#include <limits>
#include <stdexcept>
#include "retdec/common/psx_memory.h"

namespace retdec { namespace bin2llvmir {
bool joinFact(RegisterFact& fact, const RegisterFact& incoming)
{
    auto old = fact;
    fact.possibleOneBits = fact.possibleOnes() | incoming.possibleOnes();
    fact.missing |= incoming.missing;
    fact.definitions.insert(incoming.definitions.begin(), incoming.definitions.end());
    fact.formals.insert(incoming.formals.begin(), incoming.formals.end());
    fact.entries.insert(incoming.entries.begin(), incoming.entries.end());
    if (fact.equalEntry != incoming.equalEntry) fact.equalEntry.reset();
    if (fact.constant != incoming.constant) fact.constant.reset();
    fact.equalityEvidence.insert(incoming.equalityEvidence.begin(), incoming.equalityEvidence.end());
    fact.bad.insert(incoming.bad.begin(), incoming.bad.end());
    if (fact.definitions.size() > 128 || fact.bad.size() > 64)
        throw std::runtime_error("return-flow-evidence-exhausted");
    return !(old == fact);
}

bool joinState(RegisterState& destination, const RegisterState& incoming)
{
    bool changed = destination.storage.join(incoming.storage);
    auto conditions = destination.conditionalTables.size();
    destination.conditionalTables.insert(incoming.conditionalTables.begin(), incoming.conditionalTables.end());
    changed |= conditions != destination.conditionalTables.size();
    if (destination.conditionalTables.size() > Disposition::ReferenceLimit)
        throw std::runtime_error("conditional-table-references-exhausted");
    conditions = destination.conditionalCallees.size();
    destination.conditionalCallees.insert(incoming.conditionalCallees.begin(), incoming.conditionalCallees.end());
    changed |= conditions != destination.conditionalCallees.size();
    if (destination.conditionalCallees.size() > Disposition::ReferenceLimit)
        throw std::runtime_error("conditional-callee-references-exhausted");
    for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg) {
        changed |= joinFact(destination[reg], incoming[reg]);
        if (reg >= Disposition::GprCount) continue;
        if (incoming.mayPending[reg]) {
            if (destination.mayPending[reg]) changed |= joinFact(destination.pending[reg], incoming.pending[reg]);
            else { destination.pending[reg] = incoming.pending[reg]; changed = true; }
        }
        changed |= destination.mayPending[reg] != (destination.mayPending[reg] || incoming.mayPending[reg]);
        changed |= destination.mayNoPending[reg] != (destination.mayNoPending[reg] || incoming.mayNoPending[reg]);
        destination.mayPending[reg] |= incoming.mayPending[reg];
        destination.mayNoPending[reg] |= incoming.mayNoPending[reg];
    }
    return changed;
}

std::optional<ScopedCallTransfer> ScopedCallTransfer::bind(const Disposition::Call& call,
    const common::OriginalPartialCall& proof, const common::OriginalFunctionSummary& summary,
    const RegisterState& before) {
    if (!proof.identity.isComplete() || proof.callee != summary.function || !summary.entry.isComplete()
        || summary.pendingEntry != "requires-no-pending-gpr-loads" || !summary.scopedRestoration
        || !call.target || *call.target != summary.scopedRestoration->entryPc
        || proof.delay != call.pc + 4 || proof.continuation != call.pc + 8
        || proof.actualIncomingLink != std::optional<uint32_t>{uint32_t(proof.continuation)}
        || summary.transfers.size() != Disposition::RegisterCount || summary.exits.empty()
        || std::any_of(before.mayPending.begin(), before.mayPending.end(), [](bool value) { return value; })) return {};
    const auto& transfer = summary.transfers[2];
    if (transfer.reg != 2 || transfer.kind != "assigned" || !transfer.proof.isComplete()
        || transfer.definitions.empty() || !transfer.bad.empty() || transfer.pending
        || !transfer.mayNoPending || !transfer.pendingDefinitions.empty()) return {};
    const common::OriginalScopedRestoration::Register* link = nullptr;
    for (const auto& row : summary.scopedRestoration->registers) {
        if (row.reg != 31) continue;
        if (link || row.loadPcs.empty()) return {};
        link = &row;
    }
    std::vector<uint64_t> exits;
    for (const auto& exit : summary.exits) exits.push_back(exit.pc);
    std::sort(exits.begin(), exits.end());
    if (!link || link->exitPcs != exits) return {};
    for (auto entry : transfer.entries)
        if (entry >= Disposition::RegisterCount || before[entry].missing || !before[entry].bad.empty()) return {};
    return ScopedCallTransfer(transfer);
}

bool OriginalMemoryState::Word::sameValue(const Word& other) const {
    return entry == other.entry && offset == other.offset && store == other.store;
}
bool OriginalMemoryState::Word::operator==(const Word& other) const {
    return sameValue(other) && loads == other.loads && calls == other.calls;
}
void OriginalMemoryState::invalidate() {
    _eligible = false; _words.clear(); _relations.fill({}); _pending.fill({});
    _hasPending.fill(false); _sampledLink.reset();
}
std::optional<uint32_t> OriginalMemoryState::physical(int32_t offset, unsigned bytes) const {
    if (!_observation) return {};
    int64_t address = int64_t(_observation->sp) + offset;
    if (address < 0 || address > UINT32_MAX) return {};
    auto ram = common::psxRamAddress(uint64_t(address));
    if (!ram || bytes > 0x80200000 - *ram) return {};
    return uint32_t(*ram & 0x1fffffff);
}
OriginalMemoryState OriginalMemoryState::bind(const common::OriginalEntryObservation* observation,
    const std::string& function, const std::string& imageId, const std::string& imageHash,
    const Disposition::Evidence& evidence) {
    OriginalMemoryState state;
    if (!observation || observation->function != function || observation->pc != evidence.start
        || observation->imageId != imageId || observation->imageHash != imageHash) return state;
    auto ram = common::psxRamAddress(evidence.start);
    if (!ram || evidence.start % 4 || evidence.end <= evidence.start
        || evidence.end - evidence.start > 0x80200000 - *ram
        || observation->ram.size() != 0x200000
        || evidence.instructions.size() != (evidence.end - evidence.start) / 4) return state;
    for (size_t index = 0; index < evidence.instructions.size(); ++index) {
        const auto& row = evidence.instructions[index];
        if (row.pc != evidence.start + 4 * index || !row.mapped || row.undef
            || row.bytes != 4 || row.owner != evidence.symbol) return state;
        uint32_t word = 0;
        for (unsigned byte = 0; byte < 4; ++byte)
            word |= uint32_t(observation->ram[(*ram & 0x1fffffff) + 4 * index + byte]) << (8 * byte);
        if (word != row.word) return state;
    }
    state._observation = observation; state._offsets[29] = 0;
    return state;
}
bool OriginalMemoryState::join(const OriginalMemoryState& incoming) {
    if (!_observation) return false;
    if (!_eligible) return false;
    if (!_observation || _observation != incoming._observation || !incoming._eligible || _frame != incoming._frame) {
        invalidate(); return true;
    }
    bool changed = false;
    for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg) {
        if (_offsets[reg] != incoming._offsets[reg] && _offsets[reg]) {
            _offsets[reg].reset(); changed = true;
            if (reg == 29) { invalidate(); return true; }
        }
    }
    auto joinWord = [&](std::optional<Word>& destination, const std::optional<Word>& source) {
        if (!destination) return;
        if (!source || !destination->sameValue(*source)) { destination.reset(); changed = true; return; }
        auto old = *destination;
        destination->loads.insert(source->loads.begin(), source->loads.end());
        destination->calls.insert(source->calls.begin(), source->calls.end());
        changed |= !(old == *destination);
    };
    for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg) {
        joinWord(_relations[reg], incoming._relations[reg]);
        if (reg >= Disposition::GprCount) continue;
        if (_hasPending[reg] != incoming._hasPending[reg]) {
            invalidate(); return true;
        }
        joinWord(_pending[reg], incoming._pending[reg]);
    }
    joinWord(_sampledLink, incoming._sampledLink);
    for (auto it = _words.begin(); it != _words.end();) {
        auto found = incoming._words.find(it->first);
        if (found == incoming._words.end() || !it->second.sameValue(found->second)) {
            it = _words.erase(it); changed = true; continue;
        }
        auto old = it->second;
        it->second.loads.insert(found->second.loads.begin(), found->second.loads.end());
        it->second.calls.insert(found->second.calls.begin(), found->second.calls.end());
        changed |= !(old == it->second); ++it;
    }
    return changed;
}
void OriginalMemoryState::step(const Disposition::Instruction& row, const MipsOperation& operation,
    const RegisterState& state) {
    if (!_observation || !_eligible) return;
    if (!row.mapped || row.undef || row.owner.empty() || row.bytes != 4 || operation.merge
        || operation.kind == MipsOperation::Unsupported || operation.kind == MipsOperation::Trap) {
        invalidate(); return;
    }
    const auto word = row.word;
    unsigned opcode = word >> 26, rs = (word >> 21) & 31, rt = (word >> 16) & 31;
    int32_t immediate = int16_t(word & 0xffff);
    bool adjustment = opcode == 9 && rs == 29 && rt == 29;
    bool memory = operation.kind == MipsOperation::Load || operation.kind == MipsOperation::Store;
    for (size_t index = 0; index < operation.inputs.size(); ++index) {
        unsigned reg = operation.inputs[index];
        if (_offsets[reg] && !(adjustment || (memory && index == 0))) { invalidate(); return; }
    }
    std::optional<Word> loaded, copied;
    std::optional<int32_t> adjusted;
    if (adjustment) {
        if (!_offsets[29]) { invalidate(); return; }
        int64_t offset = int64_t(*_offsets[29]) + immediate;
        if (row.pc == _observation->pc && !_frame && immediate < 0 && (-immediate) % 4 == 0) {
            _frame = uint32_t(-immediate);
            if (!physical(immediate, *_frame)) { invalidate(); return; }
        } else if (!_frame || *_offsets[29] != -int32_t(*_frame) || offset != 0) {
            invalidate(); return;
        }
        adjusted = int32_t(offset);
    }
    if (memory) {
        unsigned bytes = opcode == 32 || opcode == 36 || opcode == 40 ? 1
            : opcode == 33 || opcode == 37 || opcode == 41 ? 2 : 4;
        std::optional<uint32_t> address;
        std::optional<int32_t> offset;
        if (_offsets[rs]) {
            int64_t sum = int64_t(*_offsets[rs]) + immediate;
            if (sum >= INT32_MIN && sum <= INT32_MAX) { offset = int32_t(sum); address = physical(*offset, bytes); }
        } else if (state[rs].constant) {
            int64_t sum = int64_t(*state[rs].constant) + immediate;
            if (sum >= 0 && sum <= UINT32_MAX) {
                auto canonical = common::psxRamAddress(uint64_t(sum));
                if (canonical && bytes <= 0x80200000 - *canonical) address = uint32_t(*canonical & 0x1fffffff);
            }
        }
        if (operation.kind == MipsOperation::Store) {
            if (!address) { invalidate(); return; }
            for (auto it = _words.begin(); it != _words.end();) {
                if (*address < it->first + 4 && it->first < *address + bytes) it = _words.erase(it);
                else ++it;
            }
            if (opcode == 43 && offset && _frame && *offset >= -int32_t(*_frame)
                && *offset <= -4 && *address % 4 == 0) {
                auto entry = state[rt].equalEntry;
                if (!entry && _relations[rt]) entry = _relations[rt]->entry;
                if (entry) _words[*address] = Word{*entry, *offset, row.pc, {}, {}};
                if (_words.size() > 256) { invalidate(); return; }
            }
        } else if (opcode == 35 && address && offset && *address % 4 == 0) {
            auto found = _words.find(*address);
            if (found != _words.end() && found->second.offset == *offset) {
                loaded = found->second; loaded->loads.insert(row.pc);
            }
        }
    }
    if (operation.kind == MipsOperation::Return) {
        if (word != 0x03e00008 || _hasPending[31]) { invalidate(); return; }
        _sampledLink = _relations[31];
    }
    if (operation.destinations.size() == 1 && !memory) {
        unsigned fn = word & 63;
        if (opcode == 0 && (fn == 33 || fn == 37) && (rs == 0 || rt == 0))
            copied = _relations[rs ? rs : rt];
    }
    std::optional<unsigned> immediateDestination = operation.kind != MipsOperation::Load
        && operation.destinations.size() == 1 ? std::optional<unsigned>(operation.destinations.front()) : std::nullopt;
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
        if (_hasPending[reg] && immediateDestination != reg) _relations[reg] = _pending[reg];
        _hasPending[reg] = false; _pending[reg].reset();
    }
    for (unsigned reg : operation.destinations) {
        if (!reg) continue;
        if (std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), reg) != 1) {
            invalidate(); return;
        }
        if (reg == 29 && !adjustment) { invalidate(); return; }
        _offsets[reg] = reg == 29 ? adjusted : std::nullopt;
        if (operation.kind == MipsOperation::Load) {
            _pending[reg] = loaded; _hasPending[reg] = true;
        } else _relations[reg] = copied;
    }
}
void OriginalMemoryState::call(uint64_t pc, const common::OriginalCallContract* contract) {
    if (!_observation || !_eligible) return;
    const common::OriginalPartialCall* proof = contract ? std::get_if<common::OriginalPartialCall>(contract) : nullptr;
    if (!proof && contract) proof = &std::get<common::OriginalCompleteCall>(*contract).proof();
    if (!proof || !proof->noMemoryWrites.isComplete() || !proof->identity.isComplete()
        || !proof->inputs.isComplete() || !proof->control.isComplete()
        || proof->registerTransfers.size() != Disposition::RegisterCount
        || std::any_of(_hasPending.begin(), _hasPending.end(), [](bool value) { return value; })) {
        invalidate(); return;
    }
    for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
        const auto& transfer = proof->registerTransfers[reg];
        bool preserved = transfer.reg == reg && transfer.proof.isComplete()
            && transfer.kind == "preserved" && !transfer.pending;
        if (reg == 29 && !preserved) { invalidate(); return; }
        if (!preserved && (transfer.reg != reg || !transfer.proof.isComplete() || transfer.pending
            || transfer.equalEntry == 29 || std::find(transfer.entries.begin(), transfer.entries.end(), 29) != transfer.entries.end())) {
            invalidate(); return;
        }
        if (!preserved) { _relations[reg].reset(); _offsets[reg].reset(); }
    }
    for (auto& word : _words) word.second.calls.insert(pc);
}
void OriginalMemoryState::summarize(common::OriginalFunctionSummary& summary,
    const std::map<uint64_t, RegisterState>& exits) {
    summary.scopedRestoration.reset();
    if (exits.empty()) return;
    auto joined = exits.begin()->second.storage;
    for (auto it = std::next(exits.begin()); it != exits.end(); ++it) joined.join(it->second.storage);
    if (!joined._observation || !joined._eligible || !joined._frame || joined._offsets[29] != 0
        || !joined._sampledLink || joined._sampledLink->entry != 31 || joined._sampledLink->loads.empty()) return;
    common::OriginalScopedRestoration report;
    const auto& observation = *joined._observation;
    report.observation = observation.identity; report.stateHash = observation.stateHash;
    report.entryPc = observation.pc; report.entrySp = observation.sp; report.frameBytes = *joined._frame;
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
        const auto& relation = joined._relations[reg];
        if (!relation || relation->entry != reg || relation->loads.empty() || joined._hasPending[reg]) continue;
        auto physical = joined.physical(relation->offset, 4);
        if (!physical || relation->offset < -int32_t(report.frameBytes) || relation->offset > -4) continue;
        common::OriginalScopedRestoration::Register restored;
        restored.reg = reg; restored.offset = relation->offset; restored.physicalWord = *physical;
        restored.storePc = relation->store;
        restored.loadPcs.assign(relation->loads.begin(), relation->loads.end());
        restored.callPcs.assign(relation->calls.begin(), relation->calls.end());
        for (const auto& exit : exits) restored.exitPcs.push_back(exit.first);
        report.registers.push_back(std::move(restored));
    }
    if (!report.registers.empty()) summary.scopedRestoration = std::move(report);
}
} }
