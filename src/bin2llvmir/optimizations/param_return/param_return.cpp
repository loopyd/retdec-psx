/**
* @file src/bin2llvmir/optimizations/param_return/param_return.cpp
* @brief Detect functions' parameters and returns.
* @copyright (c) 2019 Avast Software, licensed under the MIT license
*/

#include <array>
#include <deque>
#include <functional>
#include <tuple>
#include <stdexcept>
#include <cassert>
#include <iomanip>
#include <limits>

#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>

#include "retdec/utils/container.h"
#include "retdec/utils/string.h"
#include "retdec/bin2llvmir/optimizations/param_return/filter/filter.h"
#include "retdec/bin2llvmir/optimizations/param_return/param_return.h"
#define debug_enabled false
#include "retdec/bin2llvmir/utils/llvm.h"
#include "retdec/bin2llvmir/utils/debug.h"
#include "retdec/bin2llvmir/providers/asm_instruction.h"
#include "retdec/bin2llvmir/utils/ir_modifier.h"

using namespace retdec::utils;
using namespace llvm;

namespace retdec {
namespace bin2llvmir {

//
//=============================================================================
//  ParamReturn
//=============================================================================
//

char ParamReturn::ID = 0;

static RegisterPass<ParamReturn> X(
		"retdec-param-return",
		"Function parameters and returns optimization",
		false, // Only looks at CFG
		false // Analysis Pass
);

ParamReturn::ParamReturn() :
		ModulePass(ID)
{

}

bool ParamReturn::runOnModule(Module& m)
{
	_module = &m;
	_config = ConfigProvider::getConfig(_module);
	_abi = AbiProvider::getAbi(_module);
	_image = FileImageProvider::getFileImage(_module);
	_dbgf = DebugFormatProvider::getDebugFormat(_module);
	_lti = LtiProvider::getLti(_module);
	_demangler = DemanglerProvider::getDemangler(_module);
	_collector = CollectorProvider::createCollector(_abi, _module, &_RDA);

	return run();
}

bool ParamReturn::runOnModuleCustom(
		Module& m,
		Config* c,
		Abi* abi,
		Demangler* demangler,
		FileImage* img,
		DebugFormat* dbgf,
		Lti* lti)
{
	_module = &m;
	_config = c;
	_abi = abi;
	_image = img;
	_dbgf = dbgf;
	_lti = lti;
	_demangler = demangler;
	_collector = CollectorProvider::createCollector(_abi, _module, &_RDA);

	return run();
}

bool ParamReturn::run()
{
	if (_config == nullptr)
	{
		LOG << "[ABORT] config file is not available\n";
		return false;
	}

	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
	{
		validateStrictProfile();
		try {
			_RDA.runOnModule(*_module, _abi);
			collectAllCalls();
			qualifyReturns();
			publishReturnDispositions();
			requireSelectedContracts();
			filterCalls();
			projectOriginalParameters();
			applyToIr();
			retainSelectedDefinitionOnly();
		} catch (...) {
			publishReturnDispositions();
			_RDA.clear();
			throw;
		}
		_RDA.clear();
		return false;
	}
	invalidatePreviousNativeReturnEvidence();
	_RDA.runOnModule(*_module, _abi);

	collectAllCalls();
//	dumpInfo();
	filterCalls();
//	dumpInfo();
	propagateWrapped();
//	dumpInfo();
	applyToIr();

	_RDA.clear();

	return false;
}

void ParamReturn::invalidatePreviousNativeReturnEvidence() const
{
	for (const auto& cf : _config->getConfig().functions)
		{
			const_cast<common::Function&>(cf).returnDisposition.reset();
			const_cast<common::Function&>(cf).originalCallSummary.reset();
			const_cast<common::Function&>(cf).originalSourceExpressions.clear();
		}
}

void ParamReturn::validateStrictProfile() const
{
	const auto& c = _config->getConfig();
	const auto& p = c.parameters;
    if (p.getOriginalCallScope()) {
        const auto& root = p.getOriginalCallScope()->root;
        if (p.selectedRanges.size() != 1 || p.getEntryPoint() != root.start
            || p.selectedRanges.begin()->getStart() != root.start || p.selectedRanges.begin()->getEnd() != root.end)
            throw std::runtime_error("original-call-root-selection-disagreement");
    }
	if (!_abi || !c.architecture.isMips() || c.architecture.getBitSize() != 32
		|| !c.architecture.isEndianLittle() || !c.fileFormat.isRaw32()
		|| !p.isSelectedDecodeOnly() || p.selectedRanges.size() != 1
		|| !p.selectedFunctions.empty() || !p.selectedNotFoundFunctions.empty()
		|| !p.getInputPdbFile().empty() || !p.getOrdinalNumbersDirectory().empty()
		|| !p.staticSignaturePaths.empty() || !p.userStaticSignaturePaths.empty()
		|| !p.libraryTypeInfoPaths.empty() || !p.cryptoPatternPaths.empty()
		|| !p.abiPaths.empty() || p.isDetectStaticCode()
		|| (_dbgf && (_dbgf->hasInformation() || !_dbgf->functions.empty()
			|| !_dbgf->globals.empty() || !_dbgf->types.empty())))
		throw std::runtime_error("original-only parameter/return profile rejected");
}

namespace {
using Disposition = common::ReturnDisposition;
struct RegisterFact {
	bool missing = true;
	std::set<unsigned> definitions, formals, entries;
	std::optional<unsigned> equalEntry;
	std::optional<uint32_t> constant;
	std::set<uint64_t> equalityEvidence;
	std::set<std::string> bad;
	bool operator==(const RegisterFact& other) const {
		return missing == other.missing && definitions == other.definitions
			&& formals == other.formals && entries == other.entries && bad == other.bad
			&& equalEntry == other.equalEntry && constant == other.constant
			&& equalityEvidence == other.equalityEvidence;
	}
};
struct RegisterState {
    std::array<RegisterFact, Disposition::RegisterCount> registers;
    std::array<RegisterFact, Disposition::GprCount> pending;
    std::array<bool, Disposition::GprCount> mayPending{}, mayNoPending{};
    RegisterFact& operator[](unsigned reg) { return registers[reg]; }
    const RegisterFact& operator[](unsigned reg) const { return registers[reg]; }
};
struct MipsOperation {
	enum Kind { Compute, Multiply, Load, Store, Branch, Return, Call, Unsupported } kind = Unsupported;
	std::vector<unsigned> destinations;
	std::vector<unsigned> inputs;
	std::optional<uint64_t> target;
	bool conditional = false;
	std::string name = "unsupported";
};

MipsOperation originalOperation(const Disposition::Instruction& instruction)
{
	MipsOperation result;
	auto word = instruction.word;
	unsigned op = word >> 26, rs = (word >> 21) & 31, rt = (word >> 16) & 31;
	unsigned rd = (word >> 11) & 31, fn = word & 63;
	auto branchTarget = uint64_t(int64_t(instruction.pc + 4)
		+ int64_t(int16_t(word & 0xffff)) * 4);
	if (op == 0)
	{
		if (fn == 8 && rs == 31) { result.kind = MipsOperation::Return; result.name = "jr-ra"; result.inputs = {31}; }
		else if (fn == 9) { result.kind = MipsOperation::Call; result.name = "jalr"; result.inputs = {rs}; }
		else if (fn == 0 || fn == 2 || fn == 3) {
			result.kind = MipsOperation::Compute; result.destinations = {rd};
			result.inputs = {rt}; result.name = "shift-immediate";
		}
		else if (fn == 4 || fn == 6 || fn == 7 || (32 <= fn && fn <= 39)
			|| fn == 42 || fn == 43) {
			result.kind = MipsOperation::Compute; result.destinations = {rd};
			result.inputs = {rs, rt}; result.name = "integer-binary";
		}
		else if (fn == 24 && rd == 0 && ((word >> 6) & 31) == 0) {
			result.kind = MipsOperation::Multiply; result.name = "signed-multiply";
			result.destinations = {Disposition::HiRegister, Disposition::LoRegister};
			result.inputs = {rs, rt};
		}
		else if (fn == 18 && rs == 0 && rt == 0 && ((word >> 6) & 31) == 0) {
			result.kind = MipsOperation::Compute; result.name = "mflo";
			result.destinations = {rd}; result.inputs = {Disposition::LoRegister};
		}
	}
	else if (op == 2 || op == 3) {
		result.kind = op == 2 ? MipsOperation::Branch : MipsOperation::Call;
		result.name = op == 2 ? "j" : "jal";
		result.target = ((instruction.pc + 4) & 0xf0000000) | uint64_t(word & 0x03ffffff) << 2;
		if (op == 3) result.destinations = {31};
	}
	else if (op == 4 || op == 5 || op == 6 || op == 7
		|| (op == 1 && (rt == 0 || rt == 1))) {
		result.kind = MipsOperation::Branch; result.name = "conditional-branch";
		result.inputs = (op == 4 || op == 5) ? std::vector<unsigned>{rs, rt}
			: std::vector<unsigned>{rs};
		result.conditional = true; result.target = branchTarget;
	}
	else if (8 <= op && op <= 14) {
		result.kind = MipsOperation::Compute; result.name = "integer-immediate";
		result.destinations = {rt}; result.inputs = {rs};
	}
	else if (op == 15) {
		result.kind = MipsOperation::Compute; result.name = "lui"; result.destinations = {rt};
	}
	else if (op == 32 || op == 33 || op == 35 || op == 36 || op == 37) {
		result.kind = MipsOperation::Load; result.name = "full-register-load";
		result.destinations = {rt}; result.inputs = {rs};
	}
	else if (op == 40 || op == 41 || op == 43) {
		result.kind = MipsOperation::Store; result.name = "memory-store"; result.inputs = {rs, rt};
	}
	return result;
}

RegisterFact inputFact(const RegisterState& state, const MipsOperation& operation)
{
	RegisterFact fact;
	fact.missing = false;
	for (auto reg : operation.inputs) {
		fact.definitions.insert(state[reg].definitions.begin(), state[reg].definitions.end());
		fact.formals.insert(state[reg].formals.begin(), state[reg].formals.end());
		fact.entries.insert(state[reg].entries.begin(), state[reg].entries.end());
		fact.missing |= state[reg].missing;
		fact.bad.insert(state[reg].bad.begin(), state[reg].bad.end());
	}
	return fact;
}

bool joinFact(RegisterFact& fact, const RegisterFact& incoming)
{
    auto old = fact;
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
    bool changed = false;
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
void establishIdentity(RegisterFact& output, const RegisterState& state,
    const Disposition::Instruction& row, unsigned destination)
{
    output.equalEntry.reset(); output.constant.reset(); output.equalityEvidence.clear();
    unsigned op = row.word >> 26, rs = (row.word >> 21) & 31, rt = (row.word >> 16) & 31;
    unsigned fn = row.word & 63, shift = (row.word >> 6) & 31;
    auto copy = [&](unsigned reg) {
        output.equalEntry = state[reg].equalEntry; output.constant = state[reg].constant;
        output.equalityEvidence = state[reg].equalityEvidence; output.equalityEvidence.insert(row.pc);
    };
    if (op == 3 && destination == 31) output.constant = uint32_t(row.pc + 8);
    else if (op == 15) output.constant = (row.word & 0xffff) << 16;
    else if (op == 0 && (fn == 0 || fn == 2 || fn == 3) && shift == 0) copy(rt);
    else if (op == 0 && (fn == 33 || fn == 37 || fn == 38) && state[rt].constant == std::optional<uint32_t>{0}) copy(rs);
    else if (op == 0 && (fn == 33 || fn == 37 || fn == 38) && state[rs].constant == std::optional<uint32_t>{0}) copy(rt);
    else if (op == 0 && fn == 35 && state[rt].constant == std::optional<uint32_t>{0}) copy(rs);
    else if ((op == 9 || op == 13 || op == 14) && (row.word & 0xffff) == 0) copy(rs);
    else if (state[rs].constant && (op == 9 || op == 12 || op == 13 || op == 14)) {
        auto value = *state[rs].constant;
        output.constant = op == 9 ? value + uint32_t(int32_t(int16_t(row.word & 0xffff)))
            : op == 12 ? value & (row.word & 0xffff) : op == 13 ? value | (row.word & 0xffff) : value ^ (row.word & 0xffff);
    }
    if (output.constant) output.equalityEvidence.insert(row.pc);
}

common::OriginalTransfer transferFact(unsigned reg, const RegisterState& state, bool covered)
{
    common::OriginalTransfer row; row.reg = reg;
    const auto& value = state[reg];
    row.definitions.assign(value.definitions.begin(), value.definitions.end());
    row.entries.assign(value.entries.begin(), value.entries.end());
    row.bad.assign(value.bad.begin(), value.bad.end());
    row.equalEntry = value.equalEntry; row.constant = value.constant;
    row.equalityEvidence.assign(value.equalityEvidence.begin(), value.equalityEvidence.end());
    if (reg < Disposition::GprCount) {
        row.pending = state.mayPending[reg]; row.mayNoPending = state.mayNoPending[reg];
        if (row.pending) row.pendingDefinitions.assign(state.pending[reg].definitions.begin(), state.pending[reg].definitions.end());
    }
    if (!covered) { row.proof = common::OriginalFact::partial("normal-exit-coverage-unresolved"); return row; }
    if (row.pending) { row.proof = common::OriginalFact::partial("pending-return-load-timing-unresolved"); return row; }
    if (reg == 0 || value.equalEntry == std::optional<unsigned>{reg}) row.kind = "preserved";
    else if (!value.missing && !value.definitions.empty() && value.bad.empty()) row.kind = "assigned";
    else if (!value.definitions.empty()) row.kind = "clobbered";
    else { row.proof = common::OriginalFact::partial("outgoing-register-value-unresolved"); return row; }
    row.proof = common::OriginalFact::complete();
    return row;
}

void summarizeOriginal(common::OriginalFunctionSummary& summary, const Disposition& disposition,
    const std::map<uint64_t, RegisterState>& exitStates,
    const std::map<uint64_t, RegisterFact>& sampled,
    const std::set<std::tuple<uint64_t, unsigned, std::string>>& demands,
    const std::map<uint64_t, common::OriginalMemoryAccess>& accesses, bool cyclic)
{
    const auto& evidence = disposition.evidence;
    bool covered = evidence.decodeComplete && evidence.analysisComplete && !exitStates.empty() && !cyclic;
    summary.entry = covered ? common::OriginalFact::complete() : common::OriginalFact::partial("entry-read-coverage-unresolved");
    for (const auto& use : demands) summary.demands.push_back({std::get<0>(use), std::get<1>(use), std::get<2>(use)});
    std::optional<RegisterState> joined;
    bool normal = covered;
    for (const auto& pair : exitStates) {
        auto pc = pair.first;
        common::OriginalNormalExit exit; exit.pc = pc; exit.delay = pc + 4;
        auto target = sampled.find(pc);
        if (target != sampled.end()) {
            exit.sampledDefinitions.assign(target->second.definitions.begin(), target->second.definitions.end());
            exit.sampledEntry = target->second.equalEntry; exit.sampledConstant = target->second.constant;
            exit.equalityEvidence.assign(target->second.equalityEvidence.begin(), target->second.equalityEvidence.end());
            exit.equalityEvidence.push_back(pc);
        }
        bool incoming = covered && target != sampled.end() && !target->second.missing
            && target->second.equalEntry == std::optional<unsigned>{31};
        exit.incomingLink = incoming ? common::OriginalFact::complete() : common::OriginalFact::partial("sampled-target-not-proved-equal-to-incoming-link");
        normal &= incoming;
        for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg) exit.transfers.push_back(transferFact(reg, pair.second, covered));
        summary.exits.push_back(std::move(exit));
        if (joined) joinState(*joined, pair.second); else joined = pair.second;
    }
    for (const auto& call : evidence.calls) {
        const auto* proof = call.contract ? std::get_if<common::OriginalPartialCall>(&*call.contract) : nullptr;
        normal &= call.contract && (proof ? proof->control.isComplete() : std::get<common::OriginalCompleteCall>(*call.contract).proof().control.isComplete());
    }
    summary.control = normal ? common::OriginalFact::complete() : common::OriginalFact::partial(cyclic ? "cyclic-call-component-unresolved" : "normal-control-closure-unresolved");
    if (joined) for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg) summary.transfers.push_back(transferFact(reg, *joined, covered));
    bool effects = covered && accesses.empty() && std::none_of(evidence.obligations.begin(), evidence.obligations.end(),
        [](const auto& row) { return row.domain == "memory" || row.domain == "effect"; });
    for (const auto& access : accesses) summary.accesses.push_back(access.second);
    for (const auto& call : evidence.calls) {
        if (!call.contract) { effects = false; continue; }
        auto proof = std::get_if<common::OriginalPartialCall>(&*call.contract);
        if (proof) effects &= proof->effects.isComplete();
        else effects &= std::get<common::OriginalCompleteCall>(*call.contract).proof().effects.isComplete();
    }
    summary.effects = effects ? common::OriginalFact::complete() : common::OriginalFact::partial("memory-or-call-effects-unresolved");
}

void finishOriginalDeclaration(common::OriginalFunctionSummary& summary)
{
    std::set<unsigned> parameters;
    bool supported = summary.entry.isComplete() && summary.result.isComplete();
    for (const auto& use : summary.demands) {
        if (4 <= use.reg && use.reg <= 7) parameters.insert(use.reg);
        else if (use.reg != 31 || use.role != "continuation") supported = false;
    }
    summary.parameterRegisters.assign(parameters.begin(), parameters.end());
    summary.declaration = supported ? common::OriginalFact::complete() : common::OriginalFact::partial("supported-i32-declaration-projection-unresolved");
}

template<typename Graph>
void composeOriginalCall(Disposition::Call& call, RegisterState& state, const Graph& graph,
    std::map<unsigned, Disposition::Definition>& definitions,
    std::map<std::tuple<uint64_t, unsigned, bool>, unsigned>& ids,
    std::set<std::tuple<uint64_t, unsigned, std::string>>& demands,
    Disposition::Evidence& evidence, Config& config)
{
    common::OriginalPartialCall proof;
    proof.delay = call.pc + 4; proof.continuation = call.pc + 8;
    proof.actualIncomingLink = state[31].constant;
    bool pending = false;
    for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) pending |= state.mayPending[reg];
    const common::OriginalFunctionSummary* summary = nullptr;
    const Disposition* callee = nullptr;
    if (call.target && graph.functions.count(*call.target) && !graph.unavailable.count(*call.target)) {
        auto* de = graph.functions.at(*call.target);
        auto* cf = config.getConfigFunction(de->getFunction());
        if (cf && cf->originalCallSummary && de->getReturnDisposition()) {
            summary = &*cf->originalCallSummary; callee = &*de->getReturnDisposition();
            proof.callee = summary->function;
            proof.identity = common::OriginalFact::complete();
        }
    }
    auto before = state;
    bool bindings = summary && summary->entry.isComplete() && !pending;
    if (summary) {
        std::map<unsigned, std::set<uint64_t>> uses;
        for (const auto& use : summary->demands) uses[use.reg].insert(use.pc);
        for (const auto& use : uses) {
            const auto& value = before[use.first];
            common::OriginalInputBinding binding; binding.reg = use.first; binding.missing = value.missing;
            binding.definitions.assign(value.definitions.begin(), value.definitions.end());
            binding.entries.assign(value.entries.begin(), value.entries.end());
            binding.bad.assign(value.bad.begin(), value.bad.end());
            binding.uses.assign(use.second.begin(), use.second.end());
            binding.equalEntry = value.equalEntry; binding.constant = value.constant;
            bindings &= !value.missing && value.bad.empty();
            proof.bindings.push_back(std::move(binding));
            for (auto incoming : value.entries) demands.emplace(call.pc, incoming, "call-input");
        }
        proof.inputs = bindings ? common::OriginalFact::complete() : common::OriginalFact::partial(pending ? "pending-call-boundary-load-unresolved" : "actual-live-in-binding-unresolved");
        bool control = summary->control.isComplete() && proof.actualIncomingLink == std::optional<uint32_t>{uint32_t(proof.continuation)};
        for (const auto& exit : summary->exits) proof.calleeExits.push_back(exit.pc);
        proof.control = control ? common::OriginalFact::complete() : common::OriginalFact::partial("bound-return-target-not-proved-equal-to-continuation");
        proof.result = summary->result; proof.effects = summary->effects; proof.declaration = summary->declaration;
        proof.registerTransfers = summary->transfers;
    }
    bool transfers = summary && summary->transfers.size() == Disposition::RegisterCount && proof.control.isComplete() && !pending;
    for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
        state[reg] = RegisterFact{};
        if (reg < Disposition::GprCount) {
            if (before.mayPending[reg]) state.pending[reg].bad.insert("pending-call-boundary-load-unresolved");
            state.mayPending[reg] = before.mayPending[reg]; state.mayNoPending[reg] = before.mayNoPending[reg];
        }
        const common::OriginalTransfer* transfer = summary && summary->transfers.size() == Disposition::RegisterCount ? &summary->transfers[reg] : nullptr;
        if (transfer && transfer->pending && reg < Disposition::GprCount) {
            state.mayPending[reg] = true; state.mayNoPending[reg] = transfer->mayNoPending;
            state.pending[reg] = RegisterFact{}; state.pending[reg].bad.insert("pending-return-load-boundary-unresolved");
        }
        bool usable = transfer && transfer->reg == reg && transfer->proof.isComplete() && !transfer->pending && proof.control.isComplete() && !pending;
        transfers &= usable;
        if (usable && transfer->kind == "preserved") { state[reg] = before[reg]; continue; }
        if (usable && transfer->kind == "assigned" && callee && !transfer->definitions.empty()) {
            RegisterFact output; output.missing = false;
            for (auto entry : transfer->entries) {
                output.formals.insert(before[entry].formals.begin(), before[entry].formals.end());
                output.entries.insert(before[entry].entries.begin(), before[entry].entries.end());
                output.bad.insert(before[entry].bad.begin(), before[entry].bad.end());
                output.missing |= before[entry].missing;
            }
            auto id = ids.emplace(std::make_tuple(call.pc, reg, true), ids.size() + 1).first->second;
            if (ids.size() > Disposition::RowLimit) throw std::runtime_error("call-definitions-exhausted");
            auto& definition = definitions[id]; definition.id = id; definition.pc = call.pc; definition.reg = reg;
            definition.width = 32; definition.operation = "callee-normal-exit"; definition.origin = "call";
            definition.available = proof.continuation; definition.delay = proof.delay; definition.callee = proof.callee;
            definition.calleeDefinitions = transfer->definitions; definition.substitutedEntries = transfer->entries;
            definition.formals.assign(output.formals.begin(), output.formals.end()); definition.entries.assign(output.entries.begin(), output.entries.end());
            definition.bad.assign(output.bad.begin(), output.bad.end());
            definition.inputs.clear();
            for (auto entry : transfer->entries) definition.inputs.insert(definition.inputs.end(), before[entry].definitions.begin(), before[entry].definitions.end());
            std::sort(definition.inputs.begin(), definition.inputs.end()); definition.inputs.erase(std::unique(definition.inputs.begin(), definition.inputs.end()), definition.inputs.end());
            output.definitions = {id};
            if (transfer->equalEntry) {
                output.equalEntry = before[*transfer->equalEntry].equalEntry; output.constant = before[*transfer->equalEntry].constant;
                output.equalityEvidence = before[*transfer->equalEntry].equalityEvidence;
            }
            else output.constant = transfer->constant;
            output.equalityEvidence.insert(call.pc); output.equalityEvidence.insert(proof.delay);
            definition.equalEntry = output.equalEntry; definition.constant = output.constant;
            definition.equalityEvidence.assign(output.equalityEvidence.begin(), output.equalityEvidence.end());
            state[reg] = std::move(output); continue;
        }
        state[reg].bad.insert(reg == 2 ? "unknown-call-result" : "unknown-call-clobber");
    }
    proof.transfers = transfers ? common::OriginalFact::complete() : common::OriginalFact::partial("register-or-pending-transfer-unresolved");
    if (summary && !proof.effects.isComplete() && evidence.obligations.size() < Disposition::RowLimit
        && std::none_of(evidence.obligations.begin(), evidence.obligations.end(), [&](const auto& row) { return row.pc == call.pc && row.reason == "callee-memory-effects-unresolved"; }))
        evidence.obligations.push_back({call.pc, "memory", "callee-memory-effects-unresolved"});
    proof.remaining.clear();
    for (const auto* dimension : {&proof.identity, &proof.inputs, &proof.transfers, &proof.result, &proof.control, &proof.effects, &proof.declaration})
        if (!dimension->isComplete()) proof.remaining.insert(proof.remaining.end(), dimension->remaining.begin(), dimension->remaining.end());
    std::sort(proof.remaining.begin(), proof.remaining.end()); proof.remaining.erase(std::unique(proof.remaining.begin(), proof.remaining.end()), proof.remaining.end());
    call.unresolved = proof.remaining; call.qualified = false; call.contract = std::move(proof);
}

}

void ParamReturn::qualifyReturns()
{
    OriginalContractGraph graph;
    const auto& parameters = _config->getConfig().parameters;
    const auto& scope = parameters.getOriginalCallScope();
    if (scope) {
        graph.identities.emplace(scope->root.start, scope->root);
        for (const auto& identity : scope->callees) graph.identities.emplace(identity.start, identity);
    }
    for (auto& pair : _fnc2calls) {
        auto& de = pair.second;
        auto* cf = de.getFunction() ? _config->getConfigFunction(de.getFunction()) : nullptr;
        if (!cf || !de.getReturnDisposition()) continue;
        auto start = de.getReturnDisposition()->evidence.start;
        if ((scope && graph.identities.count(start) && !de.getReturnDisposition()->evidence.instructions.empty())
            || (!scope && cf->getStart() == parameters.getEntryPoint())) {
            if (!graph.functions.emplace(start, &de).second) throw std::runtime_error("ambiguous-original-function-owner");
        }
    }
    std::map<uint64_t, unsigned> colors;
    std::vector<uint64_t> stack, ordered;
    std::function<void(uint64_t)> visit = [&](uint64_t start) {
        if (colors[start] == 2) return;
        if (colors[start] == 1) {
            auto first = std::find(stack.begin(), stack.end(), start);
            graph.unavailable.insert(first, stack.end()); return;
        }
        colors[start] = 1; stack.push_back(start);
        for (const auto& instruction : graph.functions.at(start)->getReturnDisposition()->evidence.instructions) {
            auto operation = originalOperation(instruction);
            if (operation.name == "jal" && operation.target && graph.functions.count(*operation.target)) visit(*operation.target);
        }
        stack.pop_back(); colors[start] = 2; ordered.push_back(start);
    };
    for (const auto& function : graph.functions) visit(function.first);
    for (auto start : ordered) qualifyOriginalFunction(*graph.functions.at(start), graph);
}

void ParamReturn::projectOriginalParameters()
{
    if (!_config->getConfig().parameters.getOriginalCallScope()) return;
    for (auto& pair : _fnc2calls) {
        auto& de = pair.second;
        auto* cf = de.getFunction() ? _config->getConfigFunction(de.getFunction()) : nullptr;
        if (!cf || !cf->originalCallSummary) continue;
        const auto& summary = *cf->originalCallSummary;
        if (!summary.declaration.isComplete()) throw std::runtime_error("original-only declaration projection is unknown");
        std::vector<Value*> args;
        std::vector<Type*> types;
        for (auto reg : summary.parameterRegisters) {
            auto* value = _abi->getRegister(MIPS_REG_0 + reg);
            if (!value || !value->getValueType()->isIntegerTy(32)) throw std::runtime_error("unsupported-original-argument-register");
            args.push_back(value); types.push_back(value->getValueType());
        }
        de.setArgs(std::vector<Value*>(args)); de.setArgTypes(std::move(types));
        for (auto& call : de.callEntries()) { call.setArgs(std::vector<Value*>(args)); call.setArgTypes({}); }
    }
}

void ParamReturn::retainSelectedDefinitionOnly()
{
    if (!_config->getConfig().parameters.getOriginalCallScope()) return;
    auto root = _config->getConfig().parameters.getEntryPoint();
    for (auto& function : _module->getFunctionList()) {
        auto* cf = _config->getConfigFunction(&function);
        if (cf && cf->originalCallSummary && cf->getStart() != root) function.deleteBody();
    }
}

void ParamReturn::qualifyOriginalFunction(DataFlowEntry& de, OriginalContractGraph& graph)
{
	const auto& selected = *_config->getConfig().parameters.selectedRanges.begin();
	{
		auto* function = de.getFunction();
		auto* cf = function ? _config->getConfigFunction(function) : nullptr;
		if (!cf || !de.getReturnDisposition()) return;
		const auto& scope = _config->getConfig().parameters.getOriginalCallScope();
		bool revised = bool(scope);
		common::OriginalFunctionSummary summary;
		if (revised) summary.function = graph.identities.at(cf->getStart().getValue()).key;
		Disposition disposition = *de.getReturnDisposition();
		auto& evidence = disposition.evidence;
		evidence.symbol = cf->getName();
		evidence.selection = cf->getStart() == selected.getStart() ? "selected-root" : "analysis-callee";
		evidence.edges.clear(); evidence.definitions.clear(); evidence.exits.clear(); evidence.calls.clear();
		evidence.decodeComplete = false; evidence.analysisComplete = false;
		auto obligation = [&](uint64_t pc, const std::string& domain, const std::string& reason) {
			for (const auto& row : evidence.obligations)
				if (row.pc == pc && row.domain == domain && row.reason == reason) return;
			if (evidence.obligations.size() >= Disposition::RowLimit)
				throw std::runtime_error("return-obligations-exhausted");
			evidence.obligations.push_back({pc, domain, reason});
		};
		try {
			auto extent = revised ? graph.identities.at(cf->getStart().getValue())
				: common::ReviewedOriginalFunction{"", "", "", "", selected.getStart().getValue(), selected.getEnd().getValue()};
			if (evidence.start != extent.start || evidence.end != extent.end)
				throw std::runtime_error("decode-selection-evidence-missing");
			std::map<uint64_t, const Disposition::Instruction*> instructions;
			for (const auto& row : evidence.instructions) {
				if (!instructions.emplace(row.pc, &row).second)
					throw std::runtime_error("duplicate-decode-evidence");
			}
			RegisterState entry;
            entry.mayNoPending.fill(true);
			for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg)
				entry[reg].bad.insert(reg == 2 ? "incoming-v0"
					: reg == Disposition::HiRegister ? "incoming-hi"
					: reg == Disposition::LoRegister ? "incoming-lo"
					: "unproved-entry-register-" + std::to_string(reg));
			entry[0].bad.clear(); entry[0].missing = false; entry[0].constant = 0;
			if (revised) {
				for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
					entry[reg].missing = false; entry[reg].entries = {reg}; entry[reg].equalEntry = reg;
					if ((4 <= reg && reg <= 7) || reg == 31) entry[reg].bad.clear();
					if (4 <= reg && reg <= 7) entry[reg].formals = {reg};
				}
			}
			if (!revised) for (auto* argument : de.args()) {
				auto reg = _abi->getRegisterId(argument);
				if (MIPS_REG_A0 <= reg && reg <= MIPS_REG_A3
					&& argument->getType()->isPointerTy()
					&& argument->getType()->getPointerElementType()->isIntegerTy(32)) {
					entry[reg - MIPS_REG_0].bad.clear();
					entry[reg - MIPS_REG_0].formals.insert(reg - MIPS_REG_0);
				}
			}
			using Node = std::pair<uint64_t, uint64_t>;
			std::map<Node, RegisterState> states;
			std::deque<Node> work;
			states.emplace(Node{evidence.start, 0}, entry);
			work.emplace_back(evidence.start, 0);
			std::map<unsigned, Disposition::Definition> definitions;
			std::map<std::tuple<uint64_t, unsigned, bool>, unsigned> ids;
			std::map<uint64_t, Disposition::Exit> exits;
			std::map<uint64_t, Disposition::Call> calls;
			std::map<uint64_t, RegisterState> exitStates;
			std::map<uint64_t, RegisterFact> sampledTargets;
			std::set<std::tuple<uint64_t, unsigned, std::string>> demands;
			std::map<uint64_t, common::OriginalMemoryAccess> accesses;
			std::set<std::tuple<uint64_t, uint64_t, uint64_t, std::string>> edges;
			unsigned iterations = 0;
			while (!work.empty()) {
				if (++iterations > 262144) throw std::runtime_error("return-flow-exhausted");
				auto node = work.front(); work.pop_front();
				auto pc = node.first, owner = node.second;
				auto found = instructions.find(pc);
				if (pc < evidence.start || pc >= evidence.end || found == instructions.end()) {
					obligation(pc, "architectural", "reachable-decode-gap"); continue;
				}
				const auto& row = *found->second;
				auto operation = originalOperation(row);
                if (revised && ((row.word >> 26) == 8 || ((row.word >> 26) == 0 && ((row.word & 63) == 32 || (row.word & 63) == 34))))
                    obligation(pc, "effect", "integer-overflow-exception-unresolved");
				auto state = states.at(node);
				if (!row.mapped || row.owner != evidence.symbol || row.bytes != 4 || row.pc % 4 || row.undef)
					obligation(pc, "architectural", "unsupported-pc-ir-join");
				if (operation.kind == MipsOperation::Unsupported)
					obligation(pc, "architectural", "unsupported-machine-operation");
				bool control = operation.kind == MipsOperation::Branch
					|| operation.kind == MipsOperation::Call || operation.kind == MipsOperation::Return;
				if (owner && control) {
					obligation(pc, "architectural", "control-in-delay-slot"); continue;
				}
				auto inputs = inputFact(state, operation);
                if (revised) {
                    for (std::size_t index = 0; index < operation.inputs.size(); ++index) {
                        auto reg = operation.inputs[index];
                        auto role = operation.kind == MipsOperation::Return ? "continuation"
                            : operation.kind == MipsOperation::Branch || operation.kind == MipsOperation::Call ? "control"
                            : operation.kind == MipsOperation::Load || (operation.kind == MipsOperation::Store && index == 0) ? "address"
                            : operation.kind == MipsOperation::Store ? "stored-value" : "result";
                        for (auto incoming : state[reg].entries) demands.emplace(pc, incoming, role);
                    }
                    if (operation.kind == MipsOperation::Return) sampledTargets[pc] = state[31];
                    if (operation.kind == MipsOperation::Load || operation.kind == MipsOperation::Store) {
                        auto& access = accesses[pc]; access.pc = pc;
                        access.kind = operation.kind == MipsOperation::Load ? "read" : "write";
                        unsigned opcode = row.word >> 26;
                        access.width = opcode == 32 || opcode == 36 || opcode == 40 ? 8 : opcode == 33 || opcode == 37 || opcode == 41 ? 16 : 32;
                        access.extension = access.kind == "write" || access.width == 32 ? "none" : opcode == 32 || opcode == 33 ? "sign" : "zero";
                        access.delayed = operation.kind == MipsOperation::Load;
                        auto append = [](auto& into, const auto& values) { into.insert(into.end(), values.begin(), values.end()); std::sort(into.begin(), into.end()); into.erase(std::unique(into.begin(), into.end()), into.end()); };
                        append(access.addressDefinitions, state[operation.inputs[0]].definitions);
                        append(access.addressEntries, state[operation.inputs[0]].entries);
                        if (access.kind == "write") {
                            append(access.valueDefinitions, state[operation.inputs[1]].definitions);
                            append(access.valueEntries, state[operation.inputs[1]].entries);
                        }
                    }
                }
                auto identityState = state;
                auto immediateDestination = operation.kind != MipsOperation::Load && operation.destinations.size() == 1
                    ? std::optional<unsigned>{operation.destinations.front()} : std::optional<unsigned>{};
                for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
                    if (state.mayPending[reg] && (!immediateDestination || *immediateDestination != reg)) {
                        if (state.mayNoPending[reg]) joinFact(state[reg], state.pending[reg]);
                        else state[reg] = state.pending[reg];
                    }
                    state.mayPending[reg] = false; state.mayNoPending[reg] = true;
                }

				if (row.undef) inputs.bad.insert("ir-undef");
				if (!row.mapped || operation.kind == MipsOperation::Unsupported)
					inputs.bad.insert("unsupported-operation");
				if (operation.kind == MipsOperation::Multiply
					&& (std::find(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), Disposition::HiRegister) == row.fullWidthRegisters.end()
						|| std::find(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), Disposition::LoRegister) == row.fullWidthRegisters.end())) {
					inputs.bad.insert("unmapped-hi-lo-definition");
					obligation(pc, "architectural", "unmapped-hi-lo-definition");
				}
				for (auto destination : operation.destinations) {
					if (destination == 0) continue;
					auto output = inputs;
					bool width = std::find(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), destination)
						!= row.fullWidthRegisters.end();
					if (!width) output.bad.insert("unmapped-full-width-definition");
					auto id = ids.emplace(std::make_tuple(pc, destination, false), ids.size() + 1).first->second;
					if (ids.size() > Disposition::RowLimit)
						throw std::runtime_error("return-definitions-exhausted");
					auto& definition = definitions[id];
					definition.id = id; definition.pc = pc; definition.reg = destination;
					definition.width = width ? 32 : 0; definition.operation = operation.name;
                    definition.delayed = operation.kind == MipsOperation::Load;
					auto append = [](auto& rows, const auto& values) {
						rows.insert(rows.end(), values.begin(), values.end());
						std::sort(rows.begin(), rows.end()); rows.erase(std::unique(rows.begin(), rows.end()), rows.end());
					};
					append(definition.inputs, output.definitions); append(definition.formals, output.formals);
					append(definition.entries, output.entries);
					append(definition.bad, output.bad);
					output.definitions = {id}; output.missing = false;
					if (revised) {
                        establishIdentity(output, identityState, row, destination);
                        definition.equalEntry = output.equalEntry; definition.constant = output.constant;
                        definition.equalityEvidence.assign(output.equalityEvidence.begin(), output.equalityEvidence.end());
                    }
                    if (operation.kind == MipsOperation::Load) {
                        state.pending[destination] = output;
                        state.mayPending[destination] = true; state.mayNoPending[destination] = false;
                    }
                    else state[destination] = output;
				}
				if (operation.kind == MipsOperation::Load || operation.kind == MipsOperation::Store)
					obligation(pc, "memory", "contents-object-address-alias-effect-placement-unresolved");
				if ((operation.kind == MipsOperation::Store || operation.kind == MipsOperation::Branch)
					&& !inputs.bad.empty())
					obligation(pc, "architectural", "unproved-control-or-effect-input");
				auto send = [&](uint64_t target, uint64_t delayOwner, const std::string& kind) {
					edges.emplace(pc, target, delayOwner, kind);
					if (edges.size() > Disposition::RowLimit) throw std::runtime_error("return-edges-exhausted");
					Node next{target, delayOwner};
					auto insertion = states.emplace(next, state);
					if (states.size() > Disposition::RowLimit) throw std::runtime_error("return-states-exhausted");
					if (insertion.second || joinState(insertion.first->second, state)) work.push_back(next);
				};
				if (owner) {
					auto branch = originalOperation(*instructions.at(owner));
					if (branch.kind == MipsOperation::Return) {
						exitStates[owner] = state;
						auto& exit = exits[owner]; exit.pc = owner; exit.delaySlot = pc;
                        if (state.mayPending[2]) {
                            obligation(pc, "architectural", "return-load-delay-unresolved");
                            exit.pendingDefinitions.assign(state.pending[2].definitions.begin(), state.pending[2].definitions.end());
                        }
						exit.missing = state[2].missing;
						exit.definitions.assign(state[2].definitions.begin(), state[2].definitions.end());
						exit.formals.assign(state[2].formals.begin(), state[2].formals.end());
						exit.bad.assign(state[2].bad.begin(), state[2].bad.end());
					}
					else if (branch.kind == MipsOperation::Call) {
						auto& call = calls[owner]; call.pc = owner; call.target = branch.target;
                        if (revised) composeOriginalCall(call, state, graph, definitions, ids, demands, evidence, *_config);
                        else {
                            call.unresolved = {"argument-result-effect-contract-unresolved"};
                            for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
                                state[reg] = RegisterFact{};
                                if (reg < Disposition::GprCount) { state.mayPending[reg] = false; state.mayNoPending[reg] = true; }
                                state[reg].bad.insert(reg == 2 ? "unknown-call-result" : "unknown-call-clobber");
                            }
                        }
						send(owner + 8, 0, "call-continuation");
					}
					else {
						if (branch.target) send(*branch.target, 0, "branch");
						else obligation(owner, "architectural", "unresolved-branch-target");
						if (branch.conditional) send(owner + 8, 0, "fallthrough");
					}
				}
				else if (control) send(pc + 4, pc, "delay-slot");
				else send(pc + 4, 0, "fallthrough");
			}
			std::size_t references = 0;
			for (auto& pair : definitions) {
				references += pair.second.inputs.size() + pair.second.formals.size() + pair.second.bad.size();
				if (references > Disposition::ReferenceLimit) throw std::runtime_error("return-references-exhausted");
				evidence.definitions.push_back(std::move(pair.second));
			}
			for (const auto& edge : edges) evidence.edges.push_back({std::get<0>(edge), std::get<1>(edge),
				std::get<2>(edge) ? std::optional<uint64_t>(std::get<2>(edge)) : std::nullopt, std::get<3>(edge)});
			for (auto& pair : exits) evidence.exits.push_back(std::move(pair.second));
			for (auto& pair : calls) evidence.calls.push_back(std::move(pair.second));
			evidence.decodeComplete = std::none_of(evidence.obligations.begin(), evidence.obligations.end(),
				[](const auto& row) { return row.domain == "architectural"; });
			evidence.analysisComplete = true;
			bool value = evidence.decodeComplete && !evidence.exits.empty();
			for (const auto& exit : evidence.exits)
				value &= !exit.missing && !exit.definitions.empty() && exit.bad.empty();
			if (revised) {
                summarizeOriginal(summary, disposition, exitStates, sampledTargets, demands, accesses, graph.unavailable.count(evidence.start));
            }
            auto* v0 = _abi->getRegister(MIPS_REG_V0);
			value &= v0 && v0->getValueType()->isIntegerTy(32);
			if (value) {
                if (revised) summary.result = common::OriginalFact::complete();
				disposition.kind = Disposition::Kind::Value;
				de.setRetType(v0->getValueType()); de.setRetValue(v0);
			}
			else {
				obligation(evidence.start, "architectural", "all-path-v0-definition-unresolved");
				if (revised) summary.result = common::OriginalFact::partial("all-path-v0-definition-unresolved");
			}
			if (revised) {
                finishOriginalDeclaration(summary);
                for (auto& call : evidence.calls) {
                    auto* proof = call.contract ? std::get_if<common::OriginalPartialCall>(&*call.contract) : nullptr;
                    if (proof && proof->remaining.empty()) {
                        auto complete = common::OriginalCompleteCall(*proof);
                        call.contract = std::move(complete); call.qualified = true; call.unresolved.clear();
                    }
                }
            }
		} catch (const std::exception& error) {
			disposition.kind = Disposition::Kind::Unknown;
            evidence.decodeComplete = false; evidence.analysisComplete = false;
            evidence.definitions.clear(); evidence.edges.clear(); evidence.exits.clear(); evidence.calls.clear();
            if (evidence.obligations.size() < Disposition::RowLimit)
				evidence.obligations.push_back({evidence.start, "architectural", error.what()});
		}
		if (revised) {
            if (summary.exits.empty()) summary.control = common::OriginalFact::partial("nonempty-normal-exit-closure-unresolved");
            cf->originalCallSummary = std::move(summary);
        }
		de.setReturnDisposition(std::move(disposition));
		cf->returnDisposition = de.getReturnDisposition();
	}
}

void ParamReturn::publishReturnDispositions() const
{
	for (const auto& pair : _fnc2calls) {
		const auto& de = pair.second;
		auto* cf = de.getFunction() ? _config->getConfigFunction(de.getFunction()) : nullptr;
		if (!cf || !de.getReturnDisposition()) continue;
		cf->returnDisposition = de.getReturnDisposition();
		if (de.getReturnDisposition()->kind == Disposition::Kind::Unknown) {
			cf->returnType.setLlvmIr(""); cf->returnStorage = common::Storage::undefined();
		}
		else {
			cf->returnType.setLlvmIr(llvmObjToString(de.getRetType()));
			cf->returnStorage = common::Storage::inRegister("v0", MIPS_REG_V0);
		}
	}
}

void ParamReturn::requireSelectedContracts() const
{
	const auto& p = _config->getConfig().parameters;
	auto* cf = _config->getConfigFunction(p.getEntryPoint());
	if (!cf || !cf->returnDisposition || cf->returnDisposition->kind != Disposition::Kind::Value)
		throw std::runtime_error("original-only selected return contract is unknown");
    if (p.getOriginalCallScope() && (!cf->originalCallSummary || !cf->originalCallSummary->declaration.isComplete()))
        throw std::runtime_error("original-only selected declaration contract is unknown");
	for (const auto& call : cf->returnDisposition->evidence.calls)
		if (call.required && !call.qualified)
			throw std::runtime_error("original-only required call contract is unknown");
}

/**
 * Collect possible arguments' stores for all calls we want to analyze.
 * At the moment, we analyze only indirect or declared function calls with no
 * arguments inside one basic block.
 */
void ParamReturn::collectAllCalls()
{
	for (auto& f : _module->getFunctionList())
	{
		if (f.isIntrinsic())
		{
			continue;
		}

		_fnc2calls.emplace(std::make_pair(
					&f,
					createDataFlowEntry(&f)));
	}

	for (auto& f : _module->getFunctionList())
	for (auto& b : f)
	for (auto& i : b)
	{
		auto* call = dyn_cast<CallInst>(&i);
		if (call == nullptr || call->getNumArgOperands() != 0)
		{
			continue;
		}

		auto* calledVal = call->getCalledValue();
		auto* calledFnc = call->getCalledFunction();

		if (calledFnc && calledFnc->isIntrinsic())
		{
			continue;
		}

		auto fIt = _fnc2calls.find(calledVal);
		if (fIt == _fnc2calls.end())
		{
			fIt = _fnc2calls.emplace(
				std::make_pair(
					calledVal,
					createDataFlowEntry(calledVal))).first;
		}

		addDataFromCall(&fIt->second, call);
	}
}

DataFlowEntry ParamReturn::createDataFlowEntry(Value* calledValue) const
{
	DataFlowEntry dataflow(calledValue);

	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
	{
		common::ReturnDisposition disposition;
		if (auto* cf = _config->getConfigFunction(dataflow.getFunction()))
		{
			if (cf->returnDisposition) disposition = *cf->returnDisposition;
			disposition.kind = common::ReturnDisposition::Kind::Unknown;
			disposition.evidence.symbol = cf->getName();
            if (disposition.evidence.instructions.empty()) {
                if (cf->getStart().isDefined()) disposition.evidence.start = cf->getStart().getValue();
                if (cf->getEnd().isDefined()) disposition.evidence.end = cf->getEnd().getValue();
            }
		}
		dataflow.setReturnDisposition(std::move(disposition));
	}
    _collector->collectDefArgs(&dataflow);
    _collector->collectDefRets(&dataflow);
    if (!_config->getConfig().parameters.isOriginalOnlyReturnRecovery()) collectExtraData(&dataflow);

	return dataflow;
}

common::CallingConventionID ParamReturn::toCallConv(const std::string &cc) const
{
	std::map<std::string, common::CallingConventionID> ccMap {
		{"cdecl", common::CallingConventionID::CC_CDECL},
		{"pascal", common::CallingConventionID::CC_PASCAL},
		{"thiscall", common::CallingConventionID::CC_THISCALL},
		{"stdcall", common::CallingConventionID::CC_STDCALL},
		{"fastcall", common::CallingConventionID::CC_FASTCALL},
		{"eabi", common::CallingConventionID::CC_ARM}
	};	// TODO add vectorcall and regcall

	return utils::mapGetValueOrDefault(ccMap, cc, common::CallingConventionID::CC_UNKNOWN);
}

void ParamReturn::collectExtraData(DataFlowEntry* dataflow) const
{
	auto* fnc = dataflow->getFunction();
	if (fnc == nullptr)
	{
		return;
	}

	auto& config = _config->getConfig();
	if (config.parameters.isSelectedDecodeOnly()) {
		auto rdFnc = _config->getFunctionAddress(fnc);
		auto isDecoded = config.parameters.selectedRanges.contains(rdFnc);
		dataflow->setIsFullyDecoded(isDecoded);
	}

	// LTI info.
	//
	auto* cf = _config->getConfigFunction(fnc);
	if (cf && (cf->isDynamicallyLinked() || cf->isStaticallyLinked()))
	{
		auto funcName = cf->getName();
		auto fp = _lti->getPairFunctionFree(funcName);
		if (fp.first)
		{
			std::vector<Type*> argTypes;
			std::vector<std::string> argNames;
			for (auto& a : fp.first->args())
			{
				if (!a.getType()->isSized())
				{
					continue;
				}
				argTypes.push_back(a.getType());
				argNames.push_back(a.getName());
			}
			dataflow->setArgTypes(
					std::move(argTypes),
					std::move(argNames));

			if (fp.first->isVarArg())
			{
				dataflow->setVariadic();
			}
			dataflow->setRetType(fp.first->getReturnType());

			std::string declr = fp.second->getDeclaration();
			if (!declr.empty())
			{
				cf->setDeclarationString(declr);
			}
			return;
		}

		auto demFuncPair = _demangler->getPairFunction(funcName);
		if (demFuncPair.first)
		{
			modifyWithDemangledData(*dataflow, demFuncPair);
			return;
		}
	}

	auto dbgFnc = _dbgf ? _dbgf->getFunction(
			_config->getFunctionAddress(fnc)) : nullptr;

	// Debug info.
	//
	if (dbgFnc)
	{
		std::vector<Type*> argTypes;
		std::vector<std::string> argNames;
		for (auto& a : dbgFnc->parameters)
		{
			auto* t = llvm_utils::stringToLlvmTypeDefault(
					_module, a.type.getLlvmIr());
			if (!t->isSized())
			{
				continue;
			}
			argTypes.push_back(t);
			argNames.push_back(a.getName());
		}
		dataflow->setArgTypes(
				std::move(argTypes),
				std::move(argNames));

		if (dbgFnc->isVariadic())
		{
			dataflow->setVariadic();
		}
		if (dbgFnc->returnType.isDefined())
		{
			dataflow->setRetType(
			llvm_utils::stringToLlvmTypeDefault(
				_module,
				dbgFnc->returnType.getLlvmIr()));
		}
		dataflow->setCallingConvention(dbgFnc->callingConvention.getID());

		// TODO: Maybe use demangled function name?
		// Would it be useful for names from debug info?
		return;
	}

	auto configFnc = _config->getConfigFunction(fnc);
	if (configFnc && configFnc->isUserDefined())
	{
		std::vector<Type*> argTypes;
		std::vector<std::string> argNames;
		for (auto& a : configFnc->parameters)
		{
			auto* t = llvm_utils::stringToLlvmTypeDefault(
					_module, a.type.getLlvmIr());
			if (config.architecture.isMipsOrPic32()
					&& !fnc->isDeclaration() && t->isIntegerTy()
					&& t->getIntegerBitWidth() < _abi->getDefaultType()->getBitWidth())
			{
				t = _abi->getDefaultType();
			}
			if (!t->isSized())
			{
				continue;
			}
			argTypes.push_back(t);
			argNames.push_back(a.getName());
		}
		// If no parameters are found do not call setArgType method
		// as it will consider function to be without paprameters.
		if (configFnc->parameters.size())
			dataflow->setArgTypes(
				std::move(argTypes),
				std::move(argNames));

		if (configFnc->isVariadic())
		{
			dataflow->setVariadic();
		}
		if (configFnc->returnType.isDefined())
		{
			dataflow->setRetType(
				llvm_utils::stringToLlvmTypeDefault(
					_module,
					configFnc->returnType.getLlvmIr()));
		}
		dataflow->setCallingConvention(configFnc->callingConvention.getID());

		// TODO: Maybe use demangled function name?
		// Would it be useful for names from debug info?
	}
	else if (configFnc && configFnc->isDecompilerDefined())
	{
		// As decompiler is not good source of information,
		// we should use only names and other parameters that
		// we cannot guess by any heuristic.
		std::vector<Type*> argTypes;
		std::vector<std::string> argNames;
		for (auto& a : configFnc->parameters)
		{
			argTypes.push_back(_abi->getDefaultType());
			argNames.push_back(a.getName());
		}
		if (configFnc->parameters.size())
			dataflow->setArgTypes(
				std::move(argTypes),
				std::move(argNames));

		if (configFnc->isVariadic())
		{
			dataflow->setVariadic();
		}
		dataflow->setCallingConvention(configFnc->callingConvention.getID());
	}

	// Main
	//
	if (!dataflow->argNames().size() && fnc->getName().str() == "main")
	{
		auto charPointer = PointerType::get(
			Type::getInt8Ty(_module->getContext()), 0);

		dataflow->setArgTypes(
		{
			_abi->getDefaultType(),
			PointerType::get(charPointer, 0)
		},
		{
			"argc",
			"argv"
		});

		dataflow->setRetType(_abi->getDefaultType());
		return;
	}

	// Wrappers.
	//
	if (CallInst* wrappedCall = getWrapper(fnc))
	{
		dataflow->setWrappedCall(wrappedCall);
		auto* wf = wrappedCall->getCalledFunction();
		auto* ltiFnc = _lti->getLlvmFunctionFree(wf->getName());
		if (ltiFnc)
		{
			std::vector<Type*> argTypes;
			std::vector<std::string> argNames;
			for (auto& a : ltiFnc->args())
			{
				if (!a.getType()->isSized())
				{
					continue;
				}
				argTypes.push_back(a.getType());
				argNames.push_back(a.getName());
			}
			dataflow->setArgTypes(
					std::move(argTypes),
					std::move(argNames));

			if (ltiFnc->isVarArg())
			{
				dataflow->setVariadic();
			}
			dataflow->setRetType(ltiFnc->getReturnType());

			return;
		}

		auto demFuncPair = _demangler->getPairFunction(wf->getName());
		if (demFuncPair.first)
		{
			LOG << "wrapper: " << _demangler->demangleToString(wf->getName()) << std::endl;
			modifyWithDemangledData(*dataflow, demFuncPair);

			return;
		}
	}

	// try to get calling convention and return type if name is mangled
	auto fp = _demangler->getPairFunction(fnc->getName().str());
	if (fp.first)
	{
		dataflow->setCallingConvention(toCallConv(fp.second->getCallConvention()));
		if (!fp.second->getReturnType()->isUnknown())
		{
			dataflow->setRetType(fp.first->getReturnType());
		}
	}
}

CallInst* ParamReturn::getWrapper(Function* fnc) const
{
	auto ai = AsmInstruction(fnc);
	if (ai.isInvalid())
	{
		return nullptr;
	}

	bool single = true;
	auto next = ai.getNext();
	while (next.isValid())
	{
		if (!next.empty() && !next.front()->isTerminator())
		{
			single = false;
			break;
		}
		next = next.getNext();
	}

	// Pattern
	// .text:00008A38                 LDR     R0, =aCCc       ; "C::cc()"
	// .text:00008A3C                 B       puts
	// .text:00008A40 off_8A40        DCD aCCc
	// TODO: make better wrapper detection. In wrapper, wrapped function params
	// should not be set like in this example.
	//
	if (ai && next)
	{
		if (_image->getConstantDefault(next.getEndAddress()))
		{
			auto* l = ai.getInstructionFirst<LoadInst>();
			auto* s = ai.getInstructionFirst<StoreInst>();
			auto* c = next.getInstructionFirst<CallInst>();
			if (l && s && c && isa<GlobalVariable>(l->getPointerOperand())
					&& s->getPointerOperand()->getName() == "r0")
			{
				auto gvA = _config->getGlobalAddress(cast<GlobalVariable>(l->getPointerOperand()));
				if (gvA == next.getEndAddress())
				{
					return nullptr;
				}
			}
		}
	}

	if (single)
	{
		for (auto& i : ai)
		{
			if (auto* c = dyn_cast<CallInst>(&i))
			{
				auto* cf = c->getCalledFunction();
				if (cf && !cf->isIntrinsic()) // && cf->isDeclaration())
				{
					return c;
				}
			}
		}
	}

	unsigned aiNum = 0;
	bool isSmall = true;
	next = ai;
	while (next.isValid())
	{
		++aiNum;
		next = next.getNext();
		if (aiNum > 4)
		{
			isSmall = false;
			break;
		}
	}
	auto* s = _image->getImage()->getSegmentFromAddress(ai.getAddress());
	if ((s && s->getName() == ".plt") || isSmall)
	{
		for (inst_iterator it = inst_begin(fnc), rIt = inst_end(fnc);
				it != rIt; ++it)
		{
			if (auto* l = dyn_cast<LoadInst>(&*it))
			{
				std::string n = l->getPointerOperand()->getName();
				if (n == "lr" || n == "sp")
				{
					return nullptr;
				}
			}
			else if (auto* s = dyn_cast<StoreInst>(&*it))
			{
				std::string n = s->getPointerOperand()->getName();
				if (n == "lr" || n == "sp")
				{
					return nullptr;
				}
			}
			else if (auto* c = dyn_cast<CallInst>(&*it))
			{
				auto* cf = c->getCalledFunction();
				if (cf && !cf->isIntrinsic() && cf->isDeclaration())
				{
					return c;
				}
			}
		}
	}

	return nullptr;
}

void ParamReturn::addDataFromCall(DataFlowEntry *dataflow, CallInst *call) const
{
	CallEntry* ce = dataflow->createCallEntry(call);

	_collector->collectCallArgs(ce);

	// TODO: Use info from collecting return loads.
	//
	// At this moment info return loads is not used
	// as it is not reliable source of info
	// about return value. To enable this
	// collector must have redesigned and reimplemented
	// collection algorithm.
	//
	//_collector->collectCallRets(ce);

	collectExtraData(ce);
}

void ParamReturn::collectExtraData(CallEntry* ce) const
{
}

void ParamReturn::dumpInfo() const
{
	LOG << std::endl << "_fnc2calls:" << std::endl;

	for (auto& p : _fnc2calls)
	{
		dumpInfo(p.second);
	}
}

void ParamReturn::dumpInfo(const DataFlowEntry& de) const
{
	auto called = de.getValue();
	auto fnc = de.getFunction();
	auto configFnc = _config->getConfigFunction(fnc);
	auto dbgFnc = _dbgf ? _dbgf->getFunction(
			_config->getFunctionAddress(fnc)) : nullptr;
	auto wrappedCall = de.getWrappedCall();

	LOG << "\n\t>|" << called->getName().str() << std::endl;
	LOG << "\t>|&DataFlowEntry : " << &de << std::endl;
	LOG << "\t>|fnc call : " << de.isFunction() << std::endl;
	LOG << "\t>|val call : " << de.isValue() << std::endl;
	LOG << "\t>|variadic : " << de.isVariadic() << std::endl;
	LOG << "\t>|voidarg  : " << de.isVoidarg() << std::endl;
	LOG << "\t>|call conv: " << de.getCallingConvention() << std::endl;
	LOG << "\t>|config f : " << (configFnc != nullptr) << std::endl;
	LOG << "\t>|debug f  : " << (dbgFnc != nullptr) << std::endl;
	LOG << "\t>|wrapp c  : " << llvmObjToString(wrappedCall) << std::endl;
	LOG << "\t>|calls cnt: " << de.numberOfCalls() << std::endl;
	LOG << "\t>|sto stack: " << de.storesOnRawStack(*_abi) << std::endl;
	LOG << "\t>|is decode: " << de.isFullyDecoded() << std::endl;
	LOG << "\t>|type set : " << !de.argTypes().empty() << std::endl;
	LOG << "\t>|ret type : " << llvmObjToString(de.getRetType()) << std::endl;
	LOG << "\t>|ret value: " << llvmObjToString(de.getRetValue()) << std::endl;
	LOG << "\t>|arg types:" << std::endl;
	for (auto* t : de.argTypes())
	{
		LOG << "\t\t>|" << llvmObjToString(t) << std::endl;
	}
	LOG << "\t>|arg names:" << std::endl;
	for (auto& n : de.argNames())
	{
		LOG << "\t\t>|" << n << std::endl;
	}

	LOG << "\t>|calls:" << std::endl;
	for (auto& e : de.callEntries())
	{
		dumpInfo(e);
	}

	LOG << "\t>|arg loads:" << std::endl;
	for (auto* l : de.args())
	{
		LOG << "\t\t\t>|" << llvmObjToString(l) << std::endl;
	}

	LOG << "\t>|return stores:" << std::endl;
	for (auto& e : de.retEntries())
	{
		dumpInfo(e);
	}
}

void ParamReturn::dumpInfo(const CallEntry& ce) const
{
	LOG << "\t\t>|" << llvmObjToString(ce.getCallInstruction())
		<< std::endl;
	LOG << "\t\t\tvoidarg :" << ce.isVoidarg() << std::endl;
	LOG << "\t\t\targ values:" << std::endl;
	for (auto* s : ce.args())
	{
		LOG << "\t\t\t>|" << llvmObjToString(s) << std::endl;
	}
	LOG << "\t\t\targ stores:" << std::endl;
	for (auto* s : ce.argStores())
	{
		LOG << "\t\t\t>|" << llvmObjToString(s) << std::endl;
	}
	LOG << "\t\t\tret values:" << std::endl;
	for (auto* l : ce.retValues())
	{
		LOG << "\t\t\t>|" << llvmObjToString(l) << std::endl;
	}
	LOG << "\t\t\tret loads:" << std::endl;
	for (auto* l : ce.retLoads())
	{
		LOG << "\t\t\t>|" << llvmObjToString(l) << std::endl;
	}
	LOG << "\t\t\targ types:" << std::endl;
	for (auto* t : ce.getBaseFunction()->argTypes())
	{
		LOG << "\t\t\t>|" << llvmObjToString(t);
		LOG << " (size : " << _abi->getTypeByteSize(t) << "B)" << std::endl;
	}
	for (auto* t : ce.argTypes())
	{
		LOG << "\t\t\t>|" << llvmObjToString(t);
		LOG << " (size : " << _abi->getTypeByteSize(t) << "B)" << std::endl;
	}
	LOG << "\t\t\tformat string: " << ce.getFormatString() << std::endl;
}

void ParamReturn::dumpInfo(const ReturnEntry& re) const
{
	LOG << "\t\t>|" << llvmObjToString(re.getRetInstruction())
		<< std::endl;

	LOG << "\t\t\tret stores:" << std::endl;
	for (auto* s : re.retStores())
	{
		LOG << "\t\t\t>|" << llvmObjToString(s) << std::endl;
	}

	LOG << "\t\t\tret values:" << std::endl;
	for (auto* s : re.retValues())
	{
		LOG << "\t\t\t>|" << llvmObjToString(s) << std::endl;
	}
}

void ParamReturn::filterCalls()
{
	std::map<CallingConvention::ID, Filter::Ptr> filters;

	for (auto& p : _fnc2calls)
	{
		DataFlowEntry& de = p.second;
		auto cc = de.getCallingConvention();
		if (filters.find(cc) == filters.end())
		{
			filters[cc] = FilterProvider::createFilter(_abi, cc);
		}

		if (de.hasDefinition())
		{
			filters[cc]->filterDefinition(&de);
		}

		if (de.isVariadic())
		{
			filters[cc]->filterCallsVariadic(&de, _collector.get());
		}
		else
		{
			filters[cc]->filterCalls(&de);
		}

		filters[cc]->estimateRetValue(&de);

		if (_abi->supportsCallingConvention(cc))
		{
			de.setCallingConvention(cc);
		}
		else
		{
			de.setCallingConvention(_abi->getDefaultCallingConventionID());
		}
		modifyType(de);

		if (!_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
			analyzeWithDemangler(de);
	}
}

void ParamReturn::analyzeWithDemangler(DataFlowEntry& de) const
{
	if (de.getFunction())
	{
		auto funcName = de.getFunction()->getName().str();
		auto demFuncPair = _demangler->getPairFunction(funcName);
		if (demFuncPair.first)	// demangling successful
		{
			modifyWithDemangledData(de, demFuncPair);
		}
	}
}

void ParamReturn::modifyWithDemangledData(DataFlowEntry &de, Demangler::FunctionPair &funcPair) const
{
	std::vector<Type*> argTypes;
	std::vector<std::string> argNames;

	auto detectedArgTypes = de.argTypes();
	const size_t detectedParamCount = detectedArgTypes.size();
	const size_t demanglerParamCount = funcPair.second->getParameterCount();

	if (detectedParamCount > demanglerParamCount +2) {
		return;		// param analysis was probably wrong, dont know what to do
	}

	const auto ptrSize = static_cast<unsigned>(Abi::getWordSize(_module)) * 8;
	bool retTypeSet = false;

	if (detectedParamCount == demanglerParamCount+2)
	{
		// add this param
		argTypes.emplace_back(PointerType::get(Type::getIntNTy(_module->getContext(), ptrSize), 0));
		argNames.emplace_back("this");

		// add result param
		argTypes.emplace_back(PointerType::get(Type::getIntNTy(_module->getContext(), ptrSize), 0));
		argNames.emplace_back("result");

		// set return type to result
		de.setRetType(funcPair.first->getReturnType());
		retTypeSet = true;
	}

	if (detectedParamCount == demanglerParamCount+1)
	{
		/*
		 * Adds pointer to result or this, cant be sure based on information we have.
		 * Parameter will be named "result"
		 */
		argTypes.emplace_back(PointerType::get(_abi->getDefaultType(), 0));
		argNames.emplace_back("result");
	}

	for (auto& demParam : funcPair.first->args())
	{
		if (demParam.getType()->isSized())
		{
			argTypes.push_back(demParam.getType());
			argNames.push_back(demParam.getName());
		}
	}

	de.setArgTypes(
		std::move(argTypes),
		std::move(argNames));

	if (funcPair.first->isVarArg())
	{
		de.setVariadic();
	}

	if (retTypeSet)
	{
		de.setRetType(funcPair.first->getReturnType());
	}

	auto callConv = funcPair.second->getCallConvention();
	de.setCallingConvention(toCallConv(callConv));
}

Type* ParamReturn::extractType(Value* from) const
{
	from = llvm_utils::skipCasts(from);

	if (from == nullptr)
	{
		return _abi->getDefaultType();
	}

	if (auto* p = dyn_cast<ArrayType>(from->getType()))
	{
		return p->getElementType();
	}

	if (auto* p = dyn_cast<PointerType>(from->getType()))
	{
		if (auto* a = dyn_cast<ArrayType>(p->getElementType()))
		{
			return PointerType::get(a->getElementType(), 0);
		}
	}

	return from->getType();
}

void ParamReturn::modifyType(DataFlowEntry& de) const
{
	// TODO
	// Based on large type we should do:
	//
	// If large type is encountered
	// and if cc passes large type by reference
	// just cast the reference
	//
	// else separate as much values as possible
	// and call function that will create new structure
	// and put this values in the elements of
	// the structure set this structure as parameter

	if (de.argTypes().empty())
	{
		for (auto& call : de.callEntries())
		{
			std::vector<Type*> types;
			for (auto& arg : call.args())
			{
				if (arg == nullptr)
				{
					types.push_back(_abi->getDefaultType());
					continue;
				}

				auto usage = std::find_if(
						call.argStores().begin(),
						call.argStores().end(),
						[arg](StoreInst* s)
						{
							return s->getPointerOperand()
								== arg;
						});

				if (usage == call.argStores().end())
				{

					if (auto* p = dyn_cast<PointerType>(arg->getType()))
					{
						types.push_back(p->getElementType());
					}
					else
					{
						types.push_back(arg->getType());
					}
				}
				else
				{
					types.push_back(extractType((*usage)->getValueOperand()));
				}
			}

			de.setArgTypes(std::move(types));
			break;
		}
	}

	if (de.argTypes().empty())
	{
		std::vector<Type*> types;
		std::vector<Value*> args;

		for (auto i : de.args())
		{
			if (i == nullptr)
			{
				types.push_back(_abi->getDefaultType());
			}
			else if (auto* p = dyn_cast<PointerType>(i->getType()))
			{
				types.push_back(p->getElementType());
			}
			else
			{
				types.push_back(i->getType());
			}
		}

		de.setArgTypes(std::move(types));
	}

	auto args = de.args();
	args.erase(
		std::remove_if(
			args.begin(),
			args.end(),
			[](Value* v){return v == nullptr;}),
		args.end());
	de.setArgs(std::move(args));
}

void ParamReturn::propagateWrapped() {
	for (auto& p : _fnc2calls)
	{
		propagateWrapped(p.second);
	}
}

void ParamReturn::propagateWrapped(DataFlowEntry& de) {
	auto* fnc = de.getFunction();
	auto* wrappedCall = de.getWrappedCall();
	if (fnc == nullptr || wrappedCall == nullptr)
	{
		return;
	}

	llvm::CallInst* wrappedCall2 = nullptr;
	for (inst_iterator I = inst_begin(fnc), E = inst_end(fnc); I != E; ++I)
	{
		if (auto* c = dyn_cast<CallInst>(&*I))
		{
			auto* cf = c->getCalledFunction();
			if (cf && !cf->isIntrinsic()) // && cf->isDeclaration())
			{
				wrappedCall2 = c;
				break;
			}
		}
	}

	if (wrappedCall != wrappedCall2) {
		// Something strange. Reset wrapped call and give up.
		de.setWrappedCall(nullptr);
		return;
	}
	auto* callee = wrappedCall->getCalledFunction();
	auto fIt = _fnc2calls.find(callee);
	assert (fIt != _fnc2calls.end());
	DataFlowEntry& wrapDe = fIt->second;
	// dumpInfo(de);
	// dumpInfo(wrapDe);

	if (!wrapDe.argTypes().empty()) {
		// Types have already been supplied.
		return;
	}

	wrapDe.setArgTypes(std::vector(de.argTypes()), std::vector(de.argNames()));
	wrapDe.setRetType(de.getRetType());
	// dumpInfo(wrapDe);
}

void ParamReturn::applyToIr()
{
	for (auto& p : _fnc2calls)
	{
		applyToIr(p.second);
	}

	for (auto& p : _fnc2calls)
	{

		if (!_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
			connectWrappers(p.second);
	}
}

void ParamReturn::applyToIr(DataFlowEntry& de)
{
	if (de.getReturnDisposition()
		&& de.getReturnDisposition()->kind == common::ReturnDisposition::Kind::Unknown)
		return;
	Function* fnc = de.getFunction();

	if (fnc == nullptr)
	{
		auto loadsOfCalls = fetchLoadsOfCalls(de.callEntries());

		for (auto l : loadsOfCalls)
		{
			IrModifier::modifyCallInst(l.first, de.getRetType(), l.second);
		}

		return;
	}

	if (fnc->arg_size() > 0)
	{
		return;
	}

	auto loadsOfCalls = fetchLoadsOfCalls(de.callEntries());

	std::map<ReturnInst*, Value*> rets2vals;

	if (de.getRetValue())
	{
		if (de.getRetType() == nullptr)
		{
			if (auto* p = dyn_cast<PointerType>(de.getRetValue()->getType()))
			{
				de.setRetType(p->getElementType());
			}
			else
			{
				de.setRetType(de.getRetValue()->getType());
			}
		}

		for (auto& e : de.retEntries())
		{
			auto* l = new LoadInst(de.getRetValue(), "", e.getRetInstruction());
			rets2vals[e.getRetInstruction()] = l;
		}
	}
	else
	{
		de.setRetType(Type::getVoidTy(_module->getContext()));
	}

	std::vector<llvm::Value*> definitionArgs;
	for (auto& a : de.args())
	{
		if (a != nullptr)
		{
			definitionArgs.push_back(a);
		}
	}
	std::vector<llvm::Type*> definitionArgTypes;
	for (auto& t : de.argTypes())
	{
		definitionArgTypes.push_back(t != nullptr ? t : _abi->getDefaultType());
	}
	std::vector<common::Storage> definitionArgStorages;
	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
	{
		definitionArgStorages.resize(definitionArgTypes.size());
		for (std::size_t index = 0;
			index < definitionArgs.size() && index < definitionArgTypes.size(); ++index)
		{
			auto* argument = dyn_cast<GlobalVariable>(definitionArgs[index]);
			if (!argument || !argument->getValueType()->isIntegerTy(32)
				|| !definitionArgTypes[index]->isIntegerTy(32))
				continue;
			auto reg = _abi->getRegisterId(argument);
			auto* observed = _config->getConfigRegister(argument);
			if (MIPS_REG_A0 <= reg && reg <= MIPS_REG_A3 && observed
				&& observed->getStorage().isRegister()
				&& observed->getStorage().getRegisterNumber() == reg)
				definitionArgStorages[index] = observed->getStorage();
		}
	}

	// Set used calling convention to config
	auto* cf = _config->getConfigFunction(fnc);
	if (cf)
	{
		cf->callingConvention = de.getCallingConvention();
	}

	std::vector<std::string> sourceTypes;
	if (cf) {
		for (const auto& parameter : cf->parameters)
			sourceTypes.push_back(parameter.type.getCType());
	}
	IrModifier irm(_module, _config);
	auto* newFnc = irm.modifyFunction(
			fnc,
			de.getRetType(),
			definitionArgTypes,
			de.isVariadic(),
			rets2vals,
			loadsOfCalls,
			de.getRetValue(),
			definitionArgs,
			de.argNames()).first;

	if (auto* updated = _config->getConfigFunction(newFnc)) {
		if (de.getReturnDisposition())
		{
			updated->returnDisposition = de.getReturnDisposition();
			updated->returnDisposition->evidence.symbol = updated->getName();
		}
		std::size_t index = 0;
		for (auto& parameter : updated->parameters) {
			if (index < sourceTypes.size())
				parameter.type.setCType(sourceTypes[index]);
			if (index < definitionArgStorages.size()
				&& definitionArgStorages[index].isDefined()
				&& parameter.type.getLlvmIr() == "i32")
				parameter.setStorage(definitionArgStorages[index]);
			++index;
		}
	}
	de.setCalledValue(newFnc);
}

void ParamReturn::connectWrappers(const DataFlowEntry& de)
{
	auto* fnc = de.getFunction();
	auto* wrappedCall = de.getWrappedCall();
	if (fnc == nullptr || wrappedCall == nullptr)
	{
		return;
	}

	wrappedCall = nullptr;
	for (inst_iterator I = inst_begin(fnc), E = inst_end(fnc); I != E; ++I)
	{
		if (auto* c = dyn_cast<CallInst>(&*I))
		{
			auto* cf = c->getCalledFunction();
			if (cf && !cf->isIntrinsic()) // && cf->isDeclaration())
			{
				wrappedCall = c;
				break;
			}
		}
	}

	if (wrappedCall == nullptr)
	{
		return;
	}

	if (wrappedCall->getNumArgOperands() != fnc->arg_size())
	{
		// TODO: enable assert and inspect these cases.
		return;
	}
	assert(wrappedCall->getNumArgOperands() == fnc->arg_size());

	unsigned i = 0;
	for (auto& a : fnc->args())
	{
		auto iarg = wrappedCall->getArgOperand(i);
		bool shouldSkip = false;
		if (auto* load = dyn_cast<LoadInst>(llvm_utils::skipCasts(iarg))) {
			auto oldarg = load->getPointerOperand();

			std::vector<StoreInst*> users;
			for (const auto& U : oldarg->users())
			{
				if (auto* store = dyn_cast<StoreInst>(U)) {
					if (store->getFunction() == fnc)
						users.push_back(store);
				}
			}
			for (auto store: users) {
				if (llvm_utils::skipCasts(store->getValueOperand()) == &a)
					continue;

				shouldSkip = true;
			}
		}

		if (!shouldSkip) {
			auto* conv = IrModifier::convertValueToType(&a, wrappedCall->getArgOperand(i)->getType(), wrappedCall);
			wrappedCall->setArgOperand(i, conv);
		}
		i++;
	}

	//
	//
	std::set<CallInst*> calls;
	for (auto* u : fnc->users())
	{
		if (auto* c = dyn_cast<CallInst>(u))
		{
			// inline all wrapped functions
			// TODO: only really simple fncs, or from .plt, etc.?
//			if (fnc->isVarArg())
			{
				calls.insert(c);
			}
		}
	}

	auto* wrappedFnc = wrappedCall->getCalledFunction();
	assert(wrappedFnc);
	for (auto* c : calls)
	{
		// todo: should not happen?
		if (c->getType()->isVoidTy() && !wrappedFnc->getReturnType()->isVoidTy())
		{
			continue;
		}

		std::vector<Value*> args;
		unsigned numParams = wrappedFnc->getFunctionType()->getNumParams();
		unsigned i = 0;
		for (auto& a : c->arg_operands())
		{
			if (i >= numParams) // var args fncs
			{
				assert(wrappedFnc->isVarArg());
				args.push_back(a);
			}
			else
			{
				auto* conv = IrModifier::convertValueToType(a, wrappedFnc->getFunctionType()->getParamType(i++), c);
				args.push_back(conv);
			}
		}
		auto* nc = CallInst::Create(wrappedFnc, args, "", c);
		auto* resConv = IrModifier::convertValueToTypeAfter(nc, c->getType(), nc);
		c->replaceAllUsesWith(resConv);
		c->eraseFromParent();
	}
}

std::map<CallInst*, std::vector<Value*>> ParamReturn::fetchLoadsOfCalls(
						const std::vector<CallEntry>& calls) const
{
	std::map<CallInst*, std::vector<Value*>> loadsOfCalls;

	for (auto& e : calls)
	{
		std::vector<Value*> loads;
		auto* call = e.getCallInstruction();

		auto types = e.getBaseFunction()->argTypes();
		types.insert(
			types.end(),
			e.argTypes().begin(),
			e.argTypes().end());

		auto tIt = types.begin();
		auto aIt = e.args().begin();

		while (aIt != e.args().end())
		{
			if (*aIt == nullptr)
			{
				aIt++;
				continue;
			}

			Value* l = new LoadInst(*aIt, "", call);

			if (tIt != types.end())
			{
				auto t = *tIt != nullptr ? *tIt : _abi->getDefaultType();
				l = IrModifier::convertValueToType(l, t, call);
				tIt++;
			}
			else
			{
				l = IrModifier::convertValueToType(l, _abi->getDefaultType(), call);
			}

			loads.push_back(l);
			aIt++;
		}

		loadsOfCalls[call] = std::move(loads);
	}

	return loadsOfCalls;
}

}
}
