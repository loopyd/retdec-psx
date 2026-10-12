#include "original_storage.h"
#include <algorithm>
#include <iterator>
#include <limits>
#include <stdexcept>
#include "retdec/common/psx_memory.h"

namespace retdec { namespace bin2llvmir {
bool originalIdentityCall(const OriginalIdentityFlow& flow, uint64_t pc, unsigned reg)
{
    auto call = flow.calls.find(pc);
    auto instruction = flow.instructions.find(pc), delay = flow.instructions.find(pc + 4);
    if (pc > UINT32_MAX - 8 || reg >= Disposition::RegisterCount || call == flow.calls.end()
        || instruction == flow.instructions.end() || delay == flow.instructions.end()
        || call->second.pc != pc || !call->second.contract || instruction->second->word >> 26 != 3
        || call->second.target != flow.operation(*instruction->second).target) return false;
    const auto* proof = std::get_if<common::OriginalPartialCall>(&*call->second.contract);
    if (!proof) proof = &std::get<common::OriginalCompleteCall>(*call->second.contract).proof();
    if (flow.frameUses) {
        auto use = flow.frameUses->find(pc);
        if (use != flow.frameUses->end() && use->second.preserves(reg)) {
            const auto* state = originalIdentityState(flow, pc + 8);
            if (!state || !state->conditionalCallees.count(pc)) return false;
            for (const auto* row : {instruction->second, delay->second}) {
                const auto operation = flow.operation(*row);
                if (!row->mapped || row->undef || row->bytes != 4 || row->owner != flow.symbol
                    || std::find(operation.destinations.begin(), operation.destinations.end(), reg) != operation.destinations.end()) return false;
            }
            return true;
        }
    }
    if (proof->callee.empty() || !proof->identity.isComplete() || !proof->inputs.isComplete()
        || !proof->control.isComplete() || !proof->transfers.isComplete()
        || proof->delay != pc + 4 || proof->continuation != pc + 8
        || proof->actualIncomingLink != std::optional<uint32_t>{uint32_t(pc + 8)}
        || proof->registerTransfers.size() != Disposition::RegisterCount) return false;
    for (unsigned i = 0; i < Disposition::RegisterCount; ++i) {
        const auto& transfer = proof->registerTransfers[i];
        if (transfer.reg != i || !transfer.proof.isComplete() || transfer.pending
            || !transfer.mayNoPending || !transfer.pendingDefinitions.empty()) return false;
    }
    const auto& transfer = proof->registerTransfers[reg];
    if (transfer.kind != "preserved" || transfer.equalEntry != std::optional<unsigned>{reg}) return false;
    for (const auto* row : {instruction->second, delay->second}) {
        if (!row->mapped || row->undef || row->bytes != 4 || row->pc % 4 || row->owner != flow.symbol) return false;
        auto operation = flow.operation(*row);
        if (std::find(operation.destinations.begin(), operation.destinations.end(), reg) != operation.destinations.end()) return false;
    }
    return true;
}

const RegisterState* originalIdentityState(const OriginalIdentityFlow& flow, uint64_t pc)
{
    auto state = flow.states.lower_bound({pc, 0});
    if (state == flow.states.end() || state->first.first != pc) return nullptr;
    auto next = state; ++next;
    return next != flow.states.end() && next->first.first == pc ? nullptr : &state->second;
}

bool originalIdentityWriter(const OriginalIdentityFlow& flow, uint64_t pc, unsigned reg,
    std::optional<uint64_t> expected, bool after)
{
    std::vector<std::pair<uint64_t, bool>> pending{{pc, after}};
    std::set<uint64_t> visited;
    unsigned terminals = 0, references = 0;
    while (!pending.empty()) {
        auto point = pending.back(); pending.pop_back();
        pc = point.first;
        if (point.second && !visited.insert(pc).second) continue;
        if (visited.size() > Disposition::RowLimit) return false;
        auto instruction = flow.instructions.find(pc);
        const auto* state = originalIdentityState(flow, pc);
        if (instruction == flow.instructions.end() || !state
            || state->mayPending[reg] || !state->mayNoPending[reg]) return false;
        const auto& row = *instruction->second;
        if (!row.mapped || row.undef || row.bytes != 4 || pc % 4 || row.owner != flow.symbol) return false;
        auto operation = flow.operation(row);
        if (operation.kind == MipsOperation::Call && !originalIdentityCall(flow, pc, reg)) return false;
        auto context = flow.states.lower_bound({pc, 0})->first.second;
        if (context) {
            auto owner = flow.instructions.find(context);
            if (owner == flow.instructions.end()
                || (flow.operation(*owner->second).kind == MipsOperation::Call
                    && !originalIdentityCall(flow, context, reg))) return false;
        }
        if (point.second) {
            if (operation.kind == MipsOperation::Trap || operation.kind == MipsOperation::Unsupported) return false;
            if (std::find(operation.destinations.begin(), operation.destinations.end(), reg) != operation.destinations.end()) {
                if (operation.kind == MipsOperation::Load || expected != std::optional<uint64_t>{pc}
                    || std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), reg) != 1) return false;
                ++terminals; continue;
            }
        }
        if ((*state)[reg].missing) return false;
        if (pc == flow.start) {
            if (expected) return false;
            ++terminals;
        }
        auto predecessors = flow.incoming.equal_range(pc);
        if (predecessors.first == predecessors.second) {
            if (pc == flow.start) continue;
            return false;
        }
        for (auto edge = predecessors.first; edge != predecessors.second; ++edge) {
            if (++references > Disposition::ReferenceLimit) return false;
            pending.emplace_back(edge->second->from, true);
        }
    }
    return terminals != 0;
}

std::optional<OriginalEntryOffset> originalEntryOffset(unsigned id, const OriginalIdentityFlow& flow)
{
    OriginalEntryOffset result{};
    std::set<unsigned> visited;
    std::vector<const Disposition::Definition*> chain;
    while (true) {
        if (!visited.insert(id).second || visited.size() > 128) return {};
        auto found = flow.definitions.find(id);
        if (found == flow.definitions.end()) return {};
        const auto& definition = found->second;
        auto instruction = flow.instructions.find(definition.pc);
        const auto* state = originalIdentityState(flow, definition.pc);
        if (instruction == flow.instructions.end() || !state || definition.origin != "instruction"
            || definition.width != 32 || definition.delayed || definition.constant
            || !definition.reg || definition.reg >= Disposition::GprCount || definition.inputs.size() > 1) return {};
        const auto& row = *instruction->second;
        unsigned op = row.word >> 26, rs = (row.word >> 21) & 31, rt = (row.word >> 16) & 31;
        bool copy = op == 0 && (row.word & 63) == 33 && ((row.word >> 6) & 31) == 0 && bool(rs) != bool(rt);
        unsigned source = op == 9 ? rs : rs ? rs : rt;
        unsigned destination = op == 9 ? rt : (row.word >> 11) & 31;
        if ((op != 9 && !copy) || !source || destination != definition.reg
            || definition.operation != (op == 9 ? "integer-immediate" : "integer-binary")
            || !row.mapped || row.undef || row.bytes != 4 || row.pc % 4 || row.owner != flow.symbol
            || std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), destination) != 1
            || (*state)[source].missing || state->mayPending[source] || !state->mayNoPending[source]
            || state->mayPending[destination] || !state->mayNoPending[destination]
            || definition.inputs != std::vector<unsigned>((*state)[source].definitions.begin(), (*state)[source].definitions.end())) return {};
        std::optional<uint64_t> writer;
        if (!definition.inputs.empty()) {
            auto input = flow.definitions.find(definition.inputs.front());
            if (input == flow.definitions.end() || input->second.reg != source) return {};
            writer = input->second.pc;
        }
        if (!originalIdentityWriter(flow, row.pc, source, writer)) return {};
        if (op == 9) {
            result.offset += uint32_t(int32_t(int16_t(row.word & 0xffff)));
            result.adjusted |= (row.word & 0xffff) != 0;
        }
        result.evidence.insert(row.pc); chain.push_back(&definition);
        if (!definition.inputs.empty()) { id = definition.inputs.front(); continue; }
        const auto& entry = flow.states.at({flow.start, 0})[source];
        if (entry.missing || entry.equalEntry != std::optional<unsigned>{source}
            || entry.entries != std::set<unsigned>{source}) return {};
        for (const auto* member : chain)
            if (member->entries != std::vector<unsigned>{source}
                || member->formals != std::vector<unsigned>(entry.formals.begin(), entry.formals.end())
                || member->bad != std::vector<std::string>(entry.bad.begin(), entry.bad.end())) return {};
        result.entry = source; return result;
    }
}


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

std::optional<common::OriginalSymbolicFrame> OriginalFrameContract::recover(
    const OriginalIdentityFlow& flow, const Disposition::Evidence& evidence,
    const common::OriginalFunctionSummary& summary, const std::map<uint64_t, RegisterState>& exits,
    const std::map<uint64_t, RegisterFact>& sampled) {
    if (!summary.entry.isComplete() || !evidence.decodeComplete || !evidence.analysisComplete
        || exits.empty() || summary.transfers.size() != Disposition::RegisterCount
        || !flow.instructions.count(flow.start) || flow.states.size() != flow.instructions.size()) return {};
    uint32_t allocation = flow.instructions.at(flow.start)->word;
    int32_t frame = -int32_t(int16_t(allocation & 0xffff));
    if ((allocation & 0xffff0000) != 0x27bd0000 || frame <= 0 || frame % 4
        || summary.transfers[29].kind != "preserved" || summary.transfers[29].equalEntry != 29
        || !summary.transfers[29].proof.isComplete() || summary.transfers[29].pending) return {};
    std::map<uint64_t, uint64_t> owners;
    std::map<uint64_t, std::set<uint64_t>> successors;
    std::map<uint64_t, unsigned> indegrees;
    std::map<uint64_t, int32_t> offsets;
    std::set<uint64_t> returnPcs;
    auto nestedCall = [&](uint64_t pc) {
        auto found = flow.calls.find(pc);
        if (found == flow.calls.end() || !found->second.contract) return false;
        const auto* proof = std::get_if<common::OriginalPartialCall>(&*found->second.contract);
        if (!proof) proof = &std::get<common::OriginalCompleteCall>(*found->second.contract).proof();
        const auto* settled = originalIdentityState(flow, pc + 8);
        if (!proof->identity.isComplete() || !proof->inputs.isComplete() || !proof->control.isComplete()
            || !proof->transfers.isComplete() || !proof->noMemoryWrites.isComplete()
            || found->second.target != flow.operation(*flow.instructions.at(pc)).target
            || proof->delay != pc + 4 || proof->continuation != pc + 8
            || proof->actualIncomingLink != std::optional<uint32_t>{uint32_t(pc + 8)}
            || !settled || std::any_of(settled->mayPending.begin(), settled->mayPending.end(), [](bool p) { return p; })) return false;
        return originalIdentityCall(flow, pc, 29);
    };
    for (const auto& point : flow.states) {
        uint64_t pc = point.first.first, owner = point.first.second;
        if (!owners.emplace(pc, owner).second || !flow.instructions.count(pc)) return {};
        indegrees.emplace(pc, 0);
        const auto& row = *flow.instructions.at(pc);
        const auto op = flow.operation(row);
        if (!row.mapped || row.undef || row.bytes != 4 || pc % 4 || row.owner != flow.symbol
            || op.merge || op.kind == MipsOperation::Unsupported || op.kind == MipsOperation::Trap) return {};
        bool control = op.kind == MipsOperation::Branch || op.kind == MipsOperation::Call || op.kind == MipsOperation::Return;
        if (owner && control) return {};
        bool adjustment = row.word >> 26 == 9 && ((row.word >> 21) & 31) == 29 && ((row.word >> 16) & 31) == 29;
        bool memory = op.kind == MipsOperation::Load || op.kind == MipsOperation::Store;
        for (size_t i = 0; i < op.inputs.size(); ++i)
            if (op.inputs[i] == 29 && !adjustment && !(memory && i == 0)) return {};
        if (std::find(op.destinations.begin(), op.destinations.end(), 29) != op.destinations.end() && !adjustment) return {};
        if (op.kind == MipsOperation::Call && !nestedCall(pc)) return {};
        if (memory) {
            unsigned opcode = row.word >> 26;
            if ((opcode != 35 && opcode != 43) || ((row.word >> 21) & 31) != 29
                || point.second.mayPending[29] || !point.second.mayNoPending[29]) return {};
            const auto& sp = point.second[29];
            if (sp.missing || sp.definitions.size() != 1) return {};
            auto address = originalEntryOffset(*sp.definitions.begin(), flow);
            if (!address || address->entry != 29 || address->offset != uint32_t(-frame)) return {};
            int32_t offset = -frame + int16_t(row.word & 0xffff);
            if (offset < -frame || offset > -4 || offset % 4) return {};
            offsets.emplace(pc, offset);
        }
        auto& next = successors[pc];
        if (owner) {
            if (!flow.instructions.count(owner) || owner + 4 != pc) return {};
            const auto branch = flow.operation(*flow.instructions.at(owner));
            if (branch.kind == MipsOperation::Return) {
                if (flow.instructions.at(owner)->word != 0x03e00008) return {};
                returnPcs.insert(owner);
            } else if (branch.kind == MipsOperation::Call) next.insert(owner + 8);
            else if (branch.kind == MipsOperation::Branch && branch.target) {
                next.insert(*branch.target);
                if (branch.conditional) next.insert(owner + 8);
            } else return {};
        } else next.insert(pc + 4);
    }
    if (returnPcs.size() != exits.size() || !returnPcs.count(exits.begin()->first)) return {};
    for (const auto& exit : exits) if (!returnPcs.count(exit.first)) return {};
    std::map<uint64_t, std::set<uint64_t>> reported;
    for (const auto& edge : evidence.edges) {
        if (!owners.count(edge.from) || !owners.count(edge.to)
            || edge.delayOwner.value_or(0) != owners.at(edge.to)) return {};
        reported[edge.from].insert(edge.to);
    }
    for (const auto& point : successors) {
        if (reported[point.first] != point.second) return {};
        for (auto next : point.second) {
            if (!indegrees.count(next)) return {};
            ++indegrees[next];
        }
    }
    std::vector<uint64_t> ready;
    for (const auto& point : indegrees) if (!point.second) ready.push_back(point.first);
    if (ready != std::vector<uint64_t>{flow.start}) return {};
    size_t consumed = 0;
    while (!ready.empty()) {
        uint64_t pc = ready.back(); ready.pop_back(); ++consumed;
        for (auto next : successors.at(pc)) if (!--indegrees[next]) ready.push_back(next);
    }
    if (consumed != owners.size()) return {};
    std::set<uint64_t> nestedPcs;
    for (const auto& call : flow.calls) nestedPcs.insert(call.first);
    common::OriginalSymbolicFrame report;
    report.entryPc = uint32_t(flow.start); report.frameBytes = uint32_t(frame);
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
        std::set<uint64_t> loads, crossed;
        bool valid = true;
        for (const auto& exit : exits) {
            const RegisterFact* value = &exit.second[reg];
            const RegisterState* boundary = &exit.second;
            if (reg == 31) {
                if (exit.second.mayPending[31] || !exit.second.mayNoPending[31]) { valid = false; break; }
                auto target = sampled.find(exit.first);
                boundary = originalIdentityState(flow, exit.first);
                if (target == sampled.end()) { valid = false; break; }
                value = &target->second;
            }
            if (!boundary || boundary->mayPending[reg] || !boundary->mayNoPending[reg]
                || value->missing || value->definitions.empty()) { valid = false; break; }
            for (auto id : value->definitions) {
                auto def = flow.definitions.find(id);
                if (def == flow.definitions.end() || def->second.origin != "instruction"
                    || def->second.reg != reg || def->second.width != 32 || !def->second.delayed
                    || !offsets.count(def->second.pc)) { valid = false; break; }
                uint32_t word = flow.instructions.at(def->second.pc)->word;
                if (word >> 26 != 35 || ((word >> 16) & 31) != reg) { valid = false; break; }
                loads.insert(def->second.pc);
            }
        }
        if (!valid || loads.empty()) continue;
        int32_t offset = offsets.at(*loads.begin());
        std::optional<uint64_t> store;
        for (const auto& point : offsets) {
            const auto& row = *flow.instructions.at(point.first);
            const auto* state = originalIdentityState(flow, point.first);
            if (row.word >> 26 == 43 && ((row.word >> 16) & 31) == reg && point.second == offset
                && state && !state->mayPending[reg] && state->mayNoPending[reg]
                && !(*state)[reg].missing && (*state)[reg].equalEntry == reg) {
                if (store) { valid = false; break; }
                store = point.first;
            }
        }
        if (!valid || !store) continue;
        for (auto load : loads) {
            if (offsets.at(load) != offset) { valid = false; break; }
            std::vector<uint64_t> pending;
            auto initial = flow.incoming.equal_range(load);
            for (auto e = initial.first; e != initial.second; ++e) pending.push_back(e->second->from);
            std::set<uint64_t> visited;
            unsigned terminals = 0, references = 0;
            while (!pending.empty() && valid) {
                auto pc = pending.back(); pending.pop_back();
                if (!visited.insert(pc).second) continue;
                if (pc == *store) { ++terminals; continue; }
                if (pc == flow.start) { valid = false; break; }
                const auto op = flow.operation(*flow.instructions.at(pc));
                if (op.kind == MipsOperation::Store && offsets.at(pc) == offset) { valid = false; break; }
                if (op.kind == MipsOperation::Call) crossed.insert(pc);
                if (owners.at(pc) && flow.operation(*flow.instructions.at(owners.at(pc))).kind == MipsOperation::Call)
                    crossed.insert(owners.at(pc));
                auto previous = flow.incoming.equal_range(pc);
                if (previous.first == previous.second) { valid = false; break; }
                for (auto e = previous.first; e != previous.second; ++e) {
                    if (++references > Disposition::ReferenceLimit) { valid = false; break; }
                    pending.push_back(e->second->from);
                }
            }
            if (!terminals) valid = false;
        }
        if (!valid || crossed != nestedPcs) continue;
        common::OriginalSymbolicFrame::Register restored;
        restored.reg = reg; restored.offset = offset; restored.storePc = *store;
        restored.loadPcs.assign(loads.begin(), loads.end()); restored.callPcs.assign(crossed.begin(), crossed.end());
        for (const auto& exit : exits) restored.exitPcs.push_back(exit.first);
        report.registers.push_back(std::move(restored));
    }
    if (std::none_of(report.registers.begin(), report.registers.end(), [](const auto& r) { return r.reg == 31; })) return {};
    return report;
}
std::optional<OriginalFrameContract> OriginalFrameContract::bind(const Disposition::Call& call,
    const common::OriginalPartialCall& proof, const common::OriginalFunctionSummary& summary,
    const RegisterState& before) {
    if (!summary.symbolicFrame || !summary.entry.isComplete() || !proof.identity.isComplete()
        || summary.pendingEntry != "requires-no-pending-gpr-loads" || proof.callee != summary.function
        || call.target != std::optional<uint64_t>{summary.symbolicFrame->entryPc}
        || proof.delay != call.pc + 4 || proof.continuation != call.pc + 8
        || proof.actualIncomingLink != std::optional<uint32_t>{uint32_t(call.pc + 8)}
        || summary.transfers.size() != Disposition::RegisterCount
        || std::any_of(before.mayPending.begin(), before.mayPending.end(), [](bool p) { return p; })) return {};
    std::vector<uint64_t> exits;
    for (const auto& exit : summary.exits) exits.push_back(exit.pc);
    for (const auto& row : summary.symbolicFrame->registers)
        if (row.reg == 31 && !row.loadPcs.empty() && !exits.empty() && row.exitPcs == exits)
            return OriginalFrameContract(summary);
    return {};
}
bool OriginalFrameContract::preserves(unsigned reg) const {
    if (reg >= Disposition::RegisterCount || reg == 31) return false;
    const auto& transfer = _summary->transfers[reg];
    if (transfer.reg == reg && transfer.kind == "preserved" && transfer.proof.isComplete()
        && transfer.equalEntry == reg && !transfer.pending && transfer.mayNoPending
        && transfer.pendingDefinitions.empty()) return true;
    return std::any_of(_summary->symbolicFrame->registers.begin(), _summary->symbolicFrame->registers.end(),
        [&](const auto& row) { return row.reg == reg; });
}
const common::OriginalTransfer* OriginalFrameContract::assignedResult(const RegisterState& before) const {
    const auto& transfer = _summary->transfers[2];
    if (transfer.reg != 2 || transfer.kind != "assigned" || !transfer.proof.isComplete()
        || transfer.definitions.empty() || !transfer.bad.empty() || transfer.pending
        || !transfer.mayNoPending || !transfer.pendingDefinitions.empty()) return nullptr;
    for (auto entry : transfer.entries)
        if (entry >= Disposition::RegisterCount || before[entry].missing || !before[entry].bad.empty()) return nullptr;
    return &transfer;
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
