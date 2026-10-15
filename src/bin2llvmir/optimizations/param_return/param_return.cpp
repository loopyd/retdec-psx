/**
* @file src/bin2llvmir/optimizations/param_return/param_return.cpp
* @brief Detect functions' parameters and returns.
* @copyright (c) 2019 Avast Software, licensed under the MIT license
*/

#include <algorithm>
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
#include "retdec/common/psx_memory.h"
#include "original_storage.h"
#include "retdec/bin2llvmir/optimizations/param_return/filter/filter.h"
#include "retdec/bin2llvmir/optimizations/param_return/param_return.h"
#define debug_enabled false
#include "retdec/bin2llvmir/utils/llvm.h"
#include "retdec/bin2llvmir/utils/debug.h"
#include "retdec/bin2llvmir/providers/asm_instruction.h"
#include "retdec/bin2llvmir/utils/ir_modifier.h"
#include "retdec/fileformat/file_format/file_format.h"
#include "retdec/loader/loader/image.h"
#include "retdec/loader/loader/segment.h"

using namespace retdec::utils;
using namespace llvm;

namespace retdec {
namespace bin2llvmir {

namespace {
class OriginalContractRefusal : public std::runtime_error {
public:
    using std::runtime_error::runtime_error;
};
}

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
		bool syntaxOnly = false;
		try {
			_RDA.runOnModule(*_module, _abi);
			collectAllCalls();
			qualifyReturns();
			publishReturnDispositions();
			requireSelectedContracts();
			auto* selected = _config->getConfigFunction(_config->getConfig().parameters.getEntryPoint());
			syntaxOnly = selected && selected->originalBodyCandidate
				&& !std::holds_alternative<common::OriginalEmptyVoidBody>(*selected->originalBodyCandidate);
			if (syntaxOnly && std::holds_alternative<common::OriginalEntryStackWordBody>(*selected->originalBodyCandidate))
				projectConditionalStackWordBody(std::get<common::OriginalEntryStackWordBody>(*selected->originalBodyCandidate));
			else if (syntaxOnly) projectOriginalBody();
			else {
				filterCalls();
				projectOriginalParameters();
				applyToIr();
			}
			retainSelectedDefinitionOnly();
		} catch (const OriginalContractRefusal&) {
			_RDA.clear();
			throw;
		} catch (...) {
			if (!syntaxOnly) {
				for (const auto& function : _config->getConfig().functions)
					if (function.originalCallSummary) {
						auto& summary = *const_cast<common::Function&>(function).originalCallSummary;
						summary.noMemoryWrites = common::OriginalFact::partial("native-analysis-failed");
						for (auto& access : summary.accesses)
							access.address = common::OriginalFact::partial("native-analysis-failed");
					}
				for (auto& pair : _fnc2calls) if (pair.second.getReturnDisposition()) {
					auto disposition = *pair.second.getReturnDisposition();
					for (auto& call : disposition.evidence.calls) if (call.contract) {
						auto* partial = std::get_if<common::OriginalPartialCall>(&*call.contract);
						auto& proof = partial ? *partial : std::get<common::OriginalCompleteCall>(*call.contract)._proof;
						proof.noMemoryWrites = common::OriginalFact::partial("native-analysis-failed");
					}
					pair.second.setReturnDisposition(std::move(disposition));
				}
				publishReturnDispositions();
			}
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
			const_cast<common::Function&>(cf).originalCalleeContexts.reset();
			const_cast<common::Function&>(cf).originalJumpTables.clear();
			const_cast<common::Function&>(cf).originalBodyCandidate.reset();
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

bool canProposeEmptyBody(const common::Function& function)
{
	if (!function.returnDisposition || !function.originalCallSummary) return false;
	const auto& disposition = *function.returnDisposition;
	const auto& evidence = disposition.evidence;
	const auto& summary = *function.originalCallSummary;
	if (disposition.kind != Disposition::Kind::Unknown || evidence.selection != "selected-root"
		|| !evidence.decodeComplete || !evidence.analysisComplete
		|| evidence.end != evidence.start + 8 || evidence.instructions.size() != 2
		|| !evidence.definitions.empty() || !evidence.calls.empty()
		|| evidence.edges.size() != 1 || evidence.exits.size() != 1
		|| evidence.obligations.size() != 1 || !summary.entry.isComplete()
		|| !summary.control.isComplete() || !summary.effects.isComplete()
		|| summary.result.isComplete() || summary.declaration.isComplete()
		|| !summary.accesses.empty() || !summary.parameterRegisters.empty()
		|| summary.demands.size() != 1 || summary.exits.size() != 1
		|| summary.transfers.size() != Disposition::RegisterCount) return false;
	for (unsigned i = 0; i < 2; ++i) {
		const auto& instruction = evidence.instructions[i];
		if (instruction.pc != evidence.start + 4 * i || instruction.word != (i ? 0 : 0x03e00008)
			|| instruction.owner != evidence.symbol || instruction.bytes != 4
			|| !instruction.mapped || instruction.undef || !instruction.fullWidthRegisters.empty()) return false;
	}
	const auto& edge = evidence.edges.front();
	const auto& exit = evidence.exits.front();
	const auto& obligation = evidence.obligations.front();
	const auto& demand = summary.demands.front();
	const auto& normalExit = summary.exits.front();
	if (edge.from != evidence.start || edge.to != evidence.start + 4
		|| edge.delayOwner != evidence.start || edge.kind != "delay-slot"
		|| exit.pc != evidence.start || exit.delaySlot != evidence.start + 4 || exit.missing
		|| !exit.definitions.empty() || !exit.formals.empty() || !exit.pendingDefinitions.empty()
		|| obligation.pc != evidence.start || obligation.domain != "architectural"
		|| obligation.reason != "all-path-v0-definition-unresolved"
		|| demand.pc != evidence.start || demand.reg != 31 || demand.role != "continuation"
		|| normalExit.pc != evidence.start || normalExit.delay != evidence.start + 4
		|| !normalExit.incomingLink.isComplete() || normalExit.sampledEntry != 31) return false;
	for (unsigned reg = 0; reg < Disposition::RegisterCount; ++reg) {
		const auto& transfer = summary.transfers[reg];
		if (transfer.reg != reg || transfer.kind != "preserved" || !transfer.proof.isComplete()
			|| transfer.pending || !transfer.pendingDefinitions.empty()) return false;
	}
	return true;
}



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
		if (fn == 8 && rt == 0 && rd == 0 && ((word >> 6) & 31) == 0) {
			result.kind = rs == 31 ? MipsOperation::Return : MipsOperation::Branch;
			result.name = rs == 31 ? "jr-ra" : "jr"; result.inputs = {rs};
		}
		else if (fn == 9) {
			result.kind = MipsOperation::Call; result.name = "jalr"; result.inputs = {rs};
			if (rt == 0 && ((word >> 6) & 31) == 0 && rd == 31 && rs != rd)
				result.destinations = {31};
		}
		else if (fn == 0 || fn == 2 || fn == 3) {
			result.kind = MipsOperation::Compute; result.destinations = {rd};
			result.inputs = {rt}; result.name = "shift-immediate";
		}
		else if (fn == 4 || fn == 6 || fn == 7 || (32 <= fn && fn <= 39)
			|| fn == 42 || fn == 43) {
			result.kind = MipsOperation::Compute; result.destinations = {rd};
			result.inputs = {rs, rt}; result.name = "integer-binary";
		}
		else if ((fn == 24 || fn == 25) && rd == 0 && ((word >> 6) & 31) == 0) {
			result.kind = MipsOperation::Multiply;
			result.name = fn == 24 ? "signed-multiply" : "unsigned-multiply";
			result.destinations = {Disposition::HiRegister, Disposition::LoRegister};
			result.inputs = {rs, rt};
		}
		else if ((fn == 26 || fn == 27) && rd == 0 && ((word >> 6) & 31) == 0) {
			result.kind = MipsOperation::Divide;
			result.name = fn == 26 ? "signed-divide" : "unsigned-divide";
			result.destinations = {Disposition::HiRegister, Disposition::LoRegister};
			result.inputs = {rs, rt};
		}
		else if (fn == 13) { result.kind = MipsOperation::Trap; result.name = "break"; }
		else if ((fn == 16 || fn == 18) && rs == 0 && rt == 0 && ((word >> 6) & 31) == 0) {
			result.kind = MipsOperation::Compute; result.name = fn == 16 ? "mfhi" : "mflo";
			result.destinations = {rd};
			result.inputs = {fn == 16 ? Disposition::HiRegister : Disposition::LoRegister};
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
	else if (op == 34 || op == 38) {
		result.kind = MipsOperation::Load; result.name = op == 34 ? "lwl" : "lwr";
		result.merge = op == 34 ? MipsOperation::MergeMemory::Lwl : MipsOperation::MergeMemory::Lwr;
		result.destinations = {rt}; result.inputs = {rs};
	}
	else if (op == 40 || op == 41 || op == 43) {
		result.kind = MipsOperation::Store; result.name = "memory-store"; result.inputs = {rs, rt};
	}
	else if (op == 42 || op == 46) {
		result.kind = MipsOperation::Store; result.name = op == 42 ? "swl" : "swr";
		result.merge = op == 42 ? MipsOperation::MergeMemory::Swl : MipsOperation::MergeMemory::Swr;
		result.inputs = {rs, rt};
	}
	return result;
}

std::optional<common::OriginalOrdinaryBody> ordinaryBodyLayout(const Disposition::Evidence& evidence)
{
	const auto& rows = evidence.instructions;
	if (rows.size() < 2 || rows.size() > Disposition::RowLimit
		|| evidence.end != evidence.start + 4 * rows.size()
		|| rows[rows.size() - 2].word != 0x03e00008) return {};
	const int frame = rows.front().word >> 16 == 0x27bd ? -int(int16_t(rows.front().word)) : 0;
	const bool slotRestore = frame && rows.back().word == (0x27bd0000u | unsigned(frame));
	const bool earlyRestore = frame && rows.size() >= 3 && rows.back().word == 0
		&& rows[rows.size() - 3].word == (0x27bd0000u | unsigned(frame));
	if (frame && (frame < 8 || frame > 32767 || frame % 8 || (!slotRestore && !earlyRestore))) return {};
	common::OriginalOrdinaryBody body;
	std::optional<unsigned> lastCall;
	for (unsigned i = 0; i < rows.size(); ++i)
		if (rows[i].word >> 26 == 3) lastCall = i;
	std::optional<int> savedLink;
	unsigned savedCount = 0, loadedCount = 0, callIndex = 0, branchCount = 0;
	std::optional<unsigned> pendingLoad;
	std::vector<Disposition::Edge> edges;
	MipsOperation previous;
	for (unsigned i = 0; i < rows.size(); ++i) {
		const auto& row = rows[i];
		const auto operation = originalOperation(row);
		unsigned op = row.word >> 26, rs = (row.word >> 21) & 31, rt = (row.word >> 16) & 31;
		bool call = op == 3, terminal = row.word == 0x03e00008, branch = op == 4 || op == 5;
		bool load = op == 32 || op == 35 || op == 36, store = op == 40 || op == 41 || op == 43;
		bool writesRegister = op == 9 || op == 15 || load;
		if (row.pc != evidence.start + 4 * i || row.owner != evidence.symbol || row.bytes != 4
			|| !row.mapped || row.undef || (row.word && !writesRegister && !store && !call && !terminal && !branch)
			|| (op == 15 && rs) || (terminal && i != rows.size() - 2)
			|| (op == 32 && (!lastCall || i <= *lastCall))
			|| ((previous.kind == MipsOperation::Call || previous.kind == MipsOperation::Return
				|| previous.kind == MipsOperation::Branch) && (call || terminal || branch || (load && rt)))) return {};
		if (branch && (branchCount++ || !frame || savedCount != 1 || loadedCount
			|| (lastCall && i <= *lastCall) || i + 3 >= rows.size()
			|| operation.target != row.pc + 12 || rows[i + 1].word >> 16 != 0x2402
			|| rows[i + 2].word >> 16 != 0x2402)) return {};
		std::set<unsigned> reads(operation.inputs.begin(), operation.inputs.end());
		if (pendingLoad && reads.count(*pendingLoad)) return {};
		pendingLoad = load && rt ? std::optional<unsigned>(rt) : std::nullopt;
		for (auto destination : operation.destinations)
			if (destination && std::find(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), destination)
				== row.fullWidthRegisters.end()) return {};
		bool stackAdjustment = frame && op == 9 && rs == 29 && rt == 29
			&& (i == 0 || (slotRestore && i == rows.size() - 1) || (earlyRestore && i == rows.size() - 3));
		bool linkAccess = frame && rs == 29 && rt == 31 && (op == 35 || op == 43);
		if (linkAccess) {
			int offset = int16_t(row.word);
			if (offset < 0 || offset % 4 || offset + 4 > frame) return {};
			if (op == 43) {
				if (callIndex || loadedCount || savedCount++) return {};
				savedLink = offset;
				body.erasedLink = common::OriginalOrdinaryBody::ErasedLinkAccesses{row.pc, 0, unsigned(frame), offset - frame};
			} else {
				if (!savedLink || *savedLink != offset || loadedCount++ || i >= rows.size() - 2) return {};
				body.erasedLink->restorePc = row.pc;
			}
		}
		if (!stackAdjustment && !linkAccess
			&& (reads.count(29) || (writesRegister && rt == 29)
				|| (!terminal && reads.count(31)) || (writesRegister && rt == 31))) return {};
		if (call) {
			if (loadedCount || i + 2 >= rows.size() || callIndex >= evidence.calls.size()) return {};
			const auto& observed = evidence.calls[callIndex++];
			if (observed.pc != row.pc || observed.target != operation.target) return {};
		}
		if (i + 1 < rows.size()) {
			if (previous.kind == MipsOperation::Branch) {
				edges.push_back({row.pc, row.pc + 4, std::nullopt, "fallthrough"});
				edges.push_back({row.pc, *previous.target, std::nullopt, "branch"});
			} else {
				edges.push_back({row.pc, row.pc + 4,
					(call || terminal || branch) ? std::optional<uint64_t>(row.pc) : std::nullopt,
					(call || terminal || branch) ? "delay-slot"
						: previous.kind == MipsOperation::Call ? "call-continuation" : "fallthrough"});
			}
		}
		previous = operation;
	}
	if (callIndex != evidence.calls.size() || (frame && (savedCount != 1 || loadedCount != 1))
		|| (callIndex && !frame) || evidence.edges.size() != edges.size()) return {};
	for (unsigned i = 0; i < edges.size(); ++i) {
		const auto& expected = edges[i];
		const auto& observed = evidence.edges[i];
		if (observed.from != expected.from || observed.to != expected.to
			|| observed.delayOwner != expected.delayOwner || observed.kind != expected.kind) return {};
	}
	return body;
}

std::optional<common::OriginalOrdinaryBody> canProposeOrdinaryBody(const common::Function& function)
{
	if (!function.returnDisposition || !function.originalCallSummary || !function.parameters.empty()) return {};
	const auto& disposition = *function.returnDisposition;
	const auto& evidence = disposition.evidence;
	const auto& summary = *function.originalCallSummary;
	const auto& rows = evidence.instructions;
	if (disposition.kind != Disposition::Kind::Unknown || evidence.selection != "selected-root"
		|| !evidence.analysisComplete || summary.result.isComplete() || summary.declaration.isComplete()
		|| evidence.exits.size() != 1) return {};
	auto body = ordinaryBodyLayout(evidence);
	if (!body) return {};
	if (std::any_of(evidence.obligations.begin(), evidence.obligations.end(), [](const auto& row) {
		return row.domain == "architectural" && (row.reason == "conditional-callee-preservation-unresolved"
			|| row.reason == "conditional-callee-assigned-transfer-unresolved"
            || row.reason == "conditional-symbolic-frame-restoration-unresolved");
	})) return {};
	const auto& exit = evidence.exits.front();
	if (exit.pc != evidence.end - 8 || exit.delaySlot != evidence.end - 4 || exit.missing
		|| exit.definitions.empty() || !exit.formals.empty() || !exit.pendingDefinitions.empty() || !exit.bad.empty()) return {};
	std::map<unsigned, const Disposition::Definition*> definitions;
	for (const auto& definition : evidence.definitions)
		if (!definitions.emplace(definition.id, &definition).second) return {};
	std::vector<unsigned> pending = exit.definitions;
	std::set<unsigned> visited;
	for (auto id : exit.definitions)
		if (!definitions.count(id) || definitions.at(id)->reg != 2) return {};
	while (!pending.empty()) {
		auto id = pending.back(); pending.pop_back();
		if (!visited.insert(id).second) continue;
		auto found = definitions.find(id);
		if (found == definitions.end()) return {};
		const auto& definition = *found->second;
		if (definition.width != 32 || definition.origin != "instruction" || !definition.bad.empty()
			|| !definition.entries.empty() || !definition.formals.empty()
			|| definition.pc < evidence.start || definition.pc >= evidence.end || (definition.pc - evidence.start) % 4) return {};
		const auto& instruction = rows[(definition.pc - evidence.start) / 4];
		if (std::find(instruction.fullWidthRegisters.begin(), instruction.fullWidthRegisters.end(), definition.reg) == instruction.fullWidthRegisters.end()) return {};
		for (auto input : definition.inputs) {
			if (input >= id) return {};
			pending.push_back(input);
		}
	}
	return body;
}

std::optional<uint32_t> retainedLoadMask(const MipsOperation& operation,
    const Disposition::Instruction& row, const RegisterState& before)
{
    if (operation.kind != MipsOperation::Load || !operation.merge) return {};
    const auto& base = before[operation.inputs.front()].constant;
    if (!base) return {};
    uint32_t address = *base + uint32_t(int32_t(int16_t(row.word & 0xffff)));
    unsigned byte = address & 3;
    return *operation.merge == MipsOperation::MergeMemory::Lwl
        ? ~(UINT32_MAX << (8 * (3 - byte))) : ~(UINT32_MAX >> (8 * byte));
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

void establishIdentity(RegisterFact& output, const RegisterState& state,
    const Disposition::Instruction& row, unsigned destination)
{
    output.equalEntry.reset(); output.constant.reset(); output.equalityEvidence.clear();
    output.possibleOneBits = UINT32_MAX;
    unsigned op = row.word >> 26, rs = (row.word >> 21) & 31, rt = (row.word >> 16) & 31;
    unsigned fn = row.word & 63, shift = (row.word >> 6) & 31;
    auto copy = [&](unsigned reg) {
        output.equalEntry = state[reg].equalEntry; output.constant = state[reg].constant;
        output.possibleOneBits = state[reg].possibleOnes();
        output.equalityEvidence = state[reg].equalityEvidence; output.equalityEvidence.insert(row.pc);
    };
    if (destination == 31 && (op == 3 || (op == 0 && fn == 9)))
        output.constant = uint32_t(row.pc + 8);
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
    if (op == 12) output.possibleOneBits = state[rs].possibleOnes() & (row.word & 0xffff);
    if (output.constant) output.equalityEvidence.insert(row.pc);
}

enum OriginalBranchPath { BranchTaken = 1, BranchFallthrough = 2, BothBranchPaths = 3 };

unsigned originalBranchPaths(const Disposition::Instruction& row, const RegisterState& before)
{
    unsigned opcode = row.word >> 26;
    if (opcode != 4 && opcode != 5) return BothBranchPaths;
    const auto& left = before[(row.word >> 21) & 31];
    const auto& right = before[(row.word >> 16) & 31];
    bool equal;
    if (left.constant && right.constant) equal = *left.constant == *right.constant;
    else if ((left.constant && (*left.constant & ~right.possibleOnes()))
        || (right.constant && (*right.constant & ~left.possibleOnes()))) equal = false;
    else return BothBranchPaths;
    return equal == (opcode == 4) ? BranchTaken : BranchFallthrough;
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

bool originalMemoryPrefix(const Disposition::Evidence& evidence,
    const std::map<uint64_t, const Disposition::Instruction*>& instructions,
    const std::multimap<uint64_t, const Disposition::Edge*>& outgoingEdges,
    const std::multimap<uint64_t, const Disposition::Edge*>& incomingEdges, uint64_t accessPc,
    const std::vector<uint64_t>& equalityEvidence, unsigned entryRegister = 0)
{
    std::set<unsigned> protectedRegisters{(instructions.at(accessPc)->word >> 21) & 31, entryRegister};
    for (auto pc : equalityEvidence) {
        auto operation = originalOperation(*instructions.at(pc));
        protectedRegisters.insert(operation.inputs.begin(), operation.inputs.end());
        protectedRegisters.insert(operation.destinations.begin(), operation.destinations.end());
    }
    protectedRegisters.erase(0);
    for (const auto& pair : instructions) {
        const auto& row = *pair.second;
        auto operation = originalOperation(row);
        if (operation.kind == MipsOperation::Unsupported || operation.kind == MipsOperation::Call
            || operation.kind == MipsOperation::Trap
            || (operation.kind == MipsOperation::Return && row.word != 0x03e00008)) return false;
        if (operation.kind == MipsOperation::Branch) {
            auto entersPrefix = [&](uint32_t target) { return evidence.start <= target && target <= accessPc; };
            if (!operation.target || entersPrefix(uint32_t(*operation.target))
                || (operation.conditional && entersPrefix(uint32_t(row.pc + 8)))) return false;
        }
        if (row.pc >= accessPc) continue;
        if (operation.kind == MipsOperation::Branch || operation.kind == MipsOperation::Return) return false;
        for (auto destination : operation.destinations) {
            if (operation.kind == MipsOperation::Load && protectedRegisters.count(destination)) return false;
            if (destination && std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), destination) != 1)
                return false;
        }
        unsigned outgoing = 0;
        auto edges = outgoingEdges.equal_range(row.pc);
        for (auto position = edges.first; position != edges.second; ++position) {
            const auto& edge = *position->second;
            if (edge.to != row.pc + 4 || edge.delayOwner || edge.kind != "fallthrough") return false;
            ++outgoing;
        }
        if (outgoing != 1) return false;
    }
    for (uint64_t pc = evidence.start; pc <= accessPc; pc += 4) {
        unsigned incoming = 0;
        auto edges = incomingEdges.equal_range(pc);
        for (auto position = edges.first; position != edges.second; ++position) {
            const auto& edge = *position->second;
            if (pc == evidence.start || edge.from != pc - 4 || edge.delayOwner || edge.kind != "fallthrough") return false;
            ++incoming;
        }
        if (incoming != unsigned(pc != evidence.start)) return false;
    }
    return true;
}

const Disposition::Instruction* originalMemoryLatestWriter(
    const std::map<uint64_t, const Disposition::Instruction*>& instructions,
    uint64_t before, unsigned reg)
{
    if (!reg) return nullptr;
    auto position = instructions.lower_bound(before);
    while (position != instructions.begin()) {
        --position;
        const auto& row = *position->second;
        auto operation = originalOperation(row);
        if (std::find(operation.destinations.begin(), operation.destinations.end(), reg) == operation.destinations.end()) continue;
        return &row;
    }
    return nullptr;
}

const Disposition::Definition* originalMemoryLatest(
    const std::map<uint64_t, const Disposition::Instruction*>& instructions,
    const std::map<std::pair<uint64_t, unsigned>, const Disposition::Definition*>& definitions,
    uint64_t before, unsigned reg)
{
    const auto* writer = originalMemoryLatestWriter(instructions, before, reg);
    if (!writer) return nullptr;
    auto definition = definitions.find({writer->pc, reg});
    return definition == definitions.end() ? nullptr : definition->second;
}

std::optional<common::OriginalFixedMemoryAddress> originalMemoryAddress(
    const common::OriginalMemoryAccess& access,
    const std::map<uint64_t, const Disposition::Instruction*>& instructions,
    const std::map<std::pair<uint64_t, unsigned>, const Disposition::Definition*>& definitions)
{
    const auto& instruction = *instructions.at(access.pc);
    auto operation = originalOperation(instruction);
    if (!originalMemoryAccessMatches(access, instruction, operation) || !access.addressEntries.empty()) return {};
    unsigned reg = (instruction.word >> 21) & 31;
    auto* definition = originalMemoryLatest(instructions, definitions, access.pc, reg);
    if ((reg && !definition) || access.addressDefinitions != (reg ? std::vector<unsigned>{definition->id} : std::vector<unsigned>{})) return {};
    std::vector<const Disposition::Definition*> chain;
    while (definition) {
        if (chain.size() >= 128) return {};
        auto row = instructions.find(definition->pc);
        if (row == instructions.end()) return {};
        auto word = row->second->word;
        unsigned op = word >> 26, source = (word >> 21) & 31, destination = (word >> 16) & 31;
        if ((op != 15 && op != 9 && op != 12 && op != 13 && op != 14)
            || (op == 15 && source) || !destination || definition->reg != destination
            || definition->width != 32 || definition->delayed || definition->origin != "instruction"
            || definition->operation != (op == 15 ? "lui" : "integer-immediate")
            || !definition->bad.empty() || !definition->entries.empty() || !definition->formals.empty()
            || definition->equalEntry || !definition->constant
            || std::count(row->second->fullWidthRegisters.begin(), row->second->fullWidthRegisters.end(), destination) != 1) return {};
        const auto* input = op == 15 ? nullptr : originalMemoryLatest(instructions, definitions, definition->pc, source);
        if ((source && !input) || definition->inputs != (input ? std::vector<unsigned>{input->id} : std::vector<unsigned>{})) return {};
        chain.push_back(definition);
        definition = input;
    }
    common::OriginalFixedMemoryAddress address;
    std::vector<uint64_t> storedEquality;
    for (auto position = chain.rbegin(); position != chain.rend(); ++position) {
        const auto& proof = **position;
        auto word = instructions.at(proof.pc)->word;
        unsigned op = word >> 26;
        uint32_t immediate = word & 0xffff;
        address.base = op == 15 ? immediate << 16 : op == 9 ? address.base + uint32_t(int32_t(int16_t(immediate)))
            : op == 12 ? address.base & immediate : op == 13 ? address.base | immediate : address.base ^ immediate;
        address.equalityEvidence.push_back(proof.pc);
        if (immediate || (op != 9 && op != 13 && op != 14)) storedEquality.clear();
        storedEquality.push_back(proof.pc);
        if (proof.constant != std::optional<uint32_t>{address.base} || proof.equalityEvidence != storedEquality) return {};
    }
    address.value = address.base + uint32_t(int32_t(int16_t(instruction.word & 0xffff)));
    if (address.value % (access.width / 8) == 0) address.alignment = common::OriginalFact::complete();
    return address;
}

std::optional<common::OriginalFixedMemoryAddress> originalFlowFixedMemoryAddress(
    const common::OriginalMemoryAccess& access, const OriginalIdentityFlow& flow)
{
    auto instruction = flow.instructions.find(access.pc);
    const auto* state = originalIdentityState(flow, access.pc);
    if (instruction == flow.instructions.end() || !state
        || !originalMemoryAccessMatches(access, *instruction->second, originalOperation(*instruction->second))) return {};
    unsigned reg = (instruction->second->word >> 21) & 31;
    const auto& value = (*state)[reg];
    if (!reg || value.missing || !value.constant || value.equalEntry || !value.entries.empty()
        || !value.formals.empty() || !value.bad.empty() || value.definitions.size() != 1
        || state->mayPending[reg] || !state->mayNoPending[reg] || !access.addressEntries.empty()
        || access.addressDefinitions != std::vector<unsigned>(value.definitions.begin(), value.definitions.end())) return {};
    std::vector<const Disposition::Definition*> chain;
    std::set<unsigned> visited;
    uint64_t before = access.pc;
    while (reg) {
        const auto* beforeState = originalIdentityState(flow, before);
        if (!beforeState || (*beforeState)[reg].definitions.size() != 1) return {};
        auto id = *(*beforeState)[reg].definitions.begin();
        if (!visited.insert(id).second || visited.size() > 128) return {};
        auto found = flow.definitions.find(id);
        if (found == flow.definitions.end()) return {};
        const auto& definition = found->second;
        auto row = flow.instructions.find(definition.pc);
        const auto* definitionState = originalIdentityState(flow, definition.pc);
        if (row == flow.instructions.end() || !definitionState) return {};
        auto word = row->second->word;
        unsigned op = word >> 26, source = (word >> 21) & 31, destination = (word >> 16) & 31;
        if ((op != 15 && op != 9 && op != 12 && op != 13 && op != 14) || (op == 15 && source)
            || destination != reg || definition.reg != reg || definition.id != id || definition.width != 32
            || definition.delayed || definition.origin != "instruction" || definition.equalEntry || !definition.constant
            || !definition.entries.empty() || !definition.formals.empty() || !definition.bad.empty()
            || definition.operation != (op == 15 ? "lui" : "integer-immediate")
            || !originalIdentityWriter(flow, before, reg, definition.pc)
            || definitionState->mayPending[destination] || !definitionState->mayNoPending[destination]) return {};
        const auto& input = (*definitionState)[source];
        if (input.missing || !input.constant || input.equalEntry || !input.entries.empty()
            || !input.formals.empty() || !input.bad.empty() || input.definitions.size() > 1
            || definitionState->mayPending[source] || !definitionState->mayNoPending[source]
            || definition.inputs != std::vector<unsigned>(input.definitions.begin(), input.definitions.end())
            || (source && input.definitions.size() != 1)) return {};
        chain.push_back(&definition); before = definition.pc; reg = source;
    }
    common::OriginalFixedMemoryAddress address;
    address.derivation = common::OriginalFixedMemoryAddress::Derivation::Flow;
    std::set<uint64_t> equality, storedEquality;
    for (auto position = chain.rbegin(); position != chain.rend(); ++position) {
        const auto& proof = **position;
        auto word = flow.instructions.at(proof.pc)->word;
        unsigned op = word >> 26, source = (word >> 21) & 31;
        const auto* input = originalIdentityState(flow, proof.pc);
        if ((*input)[source].constant != std::optional<uint32_t>{address.base}) return {};
        uint32_t immediate = word & 0xffff;
        address.base = op == 15 ? immediate << 16 : op == 9 ? address.base + uint32_t(int32_t(int16_t(immediate)))
            : op == 12 ? address.base & immediate : op == 13 ? address.base | immediate : address.base ^ immediate;
        equality.insert(proof.pc);
        if (immediate || (op != 9 && op != 13 && op != 14)) storedEquality.clear();
        storedEquality.insert(proof.pc);
        if (proof.constant != std::optional<uint32_t>{address.base}
            || proof.equalityEvidence != std::vector<uint64_t>(storedEquality.begin(), storedEquality.end())) return {};
    }
    if (value.constant != std::optional<uint32_t>{address.base} || value.equalityEvidence != storedEquality) return {};
    address.equalityEvidence.assign(equality.begin(), equality.end());
    address.value = address.base + uint32_t(int32_t(int16_t(instruction->second->word & 0xffff)));
    if (address.value % (access.width / 8) == 0) address.alignment = common::OriginalFact::complete();
    return address;
}

std::optional<common::OriginalEntryRelativeMemoryAddress> originalEntryRelativeMemoryAddress(
    const common::OriginalMemoryAccess& access,
    const std::map<uint64_t, const Disposition::Instruction*>& instructions,
    const std::map<std::pair<uint64_t, unsigned>, const Disposition::Definition*>& definitions)
{
    const auto& instruction = *instructions.at(access.pc);
    auto operation = originalOperation(instruction);
    if (!originalMemoryAccessMatches(access, instruction, operation)) return {};
    unsigned reg = (instruction.word >> 21) & 31;
    if (!reg) return {};
    uint64_t before = access.pc;
    std::vector<const Disposition::Definition*> chain;
    while (const auto* writer = originalMemoryLatestWriter(instructions, before, reg)) {
        if (chain.size() >= 128) return {};
        auto found = definitions.find({writer->pc, reg});
        if (found == definitions.end()) return {};
        const auto* definition = found->second;
        auto word = writer->word;
        unsigned op = word >> 26, rs = (word >> 21) & 31, rt = (word >> 16) & 31;
        bool copy = op == 0 && (word & 63) == 33 && ((word >> 6) & 31) == 0 && bool(rs) != bool(rt);
        unsigned source = op == 9 ? rs : rs ? rs : rt;
        unsigned destination = op == 9 ? rt : (word >> 11) & 31;
        if ((op != 9 && !copy) || !source || destination != reg || definition->reg != reg
            || definition->pc != writer->pc || !definition->id || definition->width != 32
            || definition->delayed || definition->origin != "instruction" || definition->constant
            || definition->operation != (op == 9 ? "integer-immediate" : "integer-binary")
            || std::count(writer->fullWidthRegisters.begin(), writer->fullWidthRegisters.end(), destination) != 1) return {};
        chain.push_back(definition);
        before = writer->pc; reg = source;
    }
    common::OriginalEntryRelativeMemoryAddress address;
    address.entryRegister = reg;
    std::vector<unsigned> entries{reg}, formals;
    if (4 <= reg && reg <= 7) formals = entries;
    std::vector<std::string> bad;
    if (reg == 2) bad = {"incoming-v0"};
    else if (reg == 1 || reg == 3 || (8 <= reg && reg <= 30))
        bad = {"unproved-entry-register-" + std::to_string(reg)};
    std::optional<unsigned> equalEntry = reg;
    std::vector<uint64_t> identityEvidence;
    const Disposition::Definition* previous = nullptr;
    for (auto position = chain.rbegin(); position != chain.rend(); ++position) {
        const auto& definition = **position;
        auto word = instructions.at(definition.pc)->word;
        if (definition.inputs != (previous ? std::vector<unsigned>{previous->id} : std::vector<unsigned>{})
            || definition.entries != entries || definition.formals != formals || definition.bad != bad) return {};
        if ((word >> 26) == 9 && (word & 0xffff)) {
            address.offset += uint32_t(int32_t(int16_t(word & 0xffff)));
            equalEntry.reset(); identityEvidence.clear();
        } else identityEvidence.push_back(definition.pc);
        if (!address.offset && definition.equalEntry == std::optional<unsigned>{reg}) {
            equalEntry = reg; identityEvidence = address.equalityEvidence;
            identityEvidence.push_back(definition.pc);
        }
        if (definition.equalEntry != equalEntry || definition.equalityEvidence != identityEvidence) return {};
        address.equalityEvidence.push_back(definition.pc);
        previous = &definition;
    }
    if (access.addressEntries != entries
        || access.addressDefinitions != (previous ? std::vector<unsigned>{previous->id} : std::vector<unsigned>{})) return {};
    address.offset += uint32_t(int32_t(int16_t(instruction.word & 0xffff)));
    return address;
}

std::map<uint64_t, common::OriginalBoundedEntryMemoryAddress> recoverOriginalStackRanges(
    const OriginalIdentityFlow& flow, const std::map<uint64_t, common::OriginalMemoryAccess>& accesses)
{
    using Edge = std::tuple<uint64_t, uint64_t, std::optional<uint64_t>, std::string>;
    std::map<uint64_t, common::OriginalBoundedEntryMemoryAddress> result;
    auto word = [&](uint64_t pc) {
        auto found = flow.instructions.find(pc);
        return found == flow.instructions.end() ? uint32_t{0xffffffff} : found->second->word;
    };
    auto ready = [&](uint64_t pc, unsigned reg) {
        const auto* state = originalIdentityState(flow, pc);
        return state && reg && reg < Disposition::GprCount && !(*state)[reg].missing
            && !state->mayPending[reg] && state->mayNoPending[reg];
    };
    auto definition = [&](uint64_t pc, unsigned reg) -> const Disposition::Definition* {
        const Disposition::Definition* found = nullptr;
        for (const auto& pair : flow.definitions) if (pair.second.pc == pc && pair.second.reg == reg) {
            if (found) return nullptr;
            found = &pair.second;
        }
        return found;
    };
    auto closed = [&](uint64_t begin, uint64_t end, const std::set<Edge>& expected) {
        std::set<Edge> observed;
        for (const auto& pair : flow.incoming) {
            const auto& edge = *pair.second;
            if ((begin <= edge.from && edge.from <= end) || (begin <= edge.to && edge.to <= end))
                if (!observed.emplace(edge.from, edge.to, edge.delayOwner, edge.kind).second) return false;
        }
        if (observed != expected || observed.size() > Disposition::ReferenceLimit) return false;
        for (uint64_t pc = begin; pc <= end; pc += 4) {
            auto found = flow.instructions.find(pc);
            if (found == flow.instructions.end()) return false;
            const auto& row = *found->second;
            auto operation = originalOperation(row);
            if (!row.mapped || row.undef || row.bytes != 4 || pc % 4 || row.owner != flow.symbol
                || operation.merge || operation.kind == MipsOperation::Call || operation.kind == MipsOperation::Trap
                || operation.kind == MipsOperation::Unsupported) return false;
            for (auto reg : operation.destinations)
                if (reg && std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), reg) != 1) return false;
        }
        return true;
    };
    auto publish = [&](uint64_t pc, unsigned pointer, uint32_t offset, uint32_t count,
        const std::set<uint64_t>& evidence, const std::set<unsigned>& expectedDefinitions) {
        auto access = accesses.find(pc);
        const auto* state = originalIdentityState(flow, pc);
        if (access == accesses.end() || !state || !ready(pc, pointer) || access->second.width != 8
            || (word(pc) & 0xffff) || ((word(pc) >> 21) & 31) != pointer
            || access->second.addressEntries != std::vector<unsigned>{29}
            || (*state)[pointer].definitions != expectedDefinitions
            || access->second.addressDefinitions != std::vector<unsigned>(expectedDefinitions.begin(), expectedDefinitions.end())
            || evidence.empty() || evidence.size() > Disposition::ReferenceLimit) return;
        common::OriginalBoundedEntryMemoryAddress address;
        address.entryRegister = 29; address.offset = offset; address.indexUpper = count - 1;
        address.boundEvidence.assign(evidence.begin(), evidence.end());
        result.emplace(pc, std::move(address));
    };
    for (const auto& pair : accesses) {
        uint64_t h = pair.first;
        uint32_t load = word(h), compare = word(h + 20), increment = word(h + 28), mask = word(h + 12);
        unsigned pointer = (load >> 21) & 31, loaded = (load >> 16) & 31;
        unsigned endpoint = (compare >> 16) & 31, comparison = (compare >> 11) & 31;
        unsigned counter = (increment >> 21) & 31, countRegister = (mask >> 16) & 31;
        std::set<unsigned> registers{pointer, loaded, endpoint, counter, countRegister};
        if (h < flow.start + 4 || pair.second.width != 8 || load >> 26 != 36 || (load & 0xffff)
            || registers.size() != 5 || registers.count(0) || comparison != loaded
            || word(h + 4) != 0 || word(h + 8) != ((4u << 26) | (loaded << 21) | 6u)
            || word(h + 16) != ((9u << 26) | (pointer << 21) | (pointer << 16) | 1u)
            || compare != ((pointer << 21) | (endpoint << 16) | (comparison << 11) | 42u)
            || word(h + 24) != ((5u << 26) | (comparison << 21) | 0xfff9u)
            || increment != ((9u << 26) | (counter << 21) | (counter << 16) | 1u)
            || mask >> 26 != 12 || ((mask >> 21) & 31) != counter || word(h + 32) != mask) continue;
        const auto* seed = originalMemoryLatestWriter(flow.instructions, h, pointer);
        const auto* counterSeed = originalMemoryLatestWriter(flow.instructions, h, counter);
        const auto* initial = seed ? definition(seed->pc, pointer) : nullptr;
        const auto* recurrence = definition(h + 16, pointer);
        const auto* counterInitial = counterSeed ? definition(counterSeed->pc, counter) : nullptr;
        const auto* endState = originalIdentityState(flow, h + 20);
        if (!initial || !recurrence || !counterInitial || !endState || !ready(h + 20, endpoint)
            || (*endState)[endpoint].definitions.size() != 1 || !ready(h - 4, pointer) || !ready(h - 4, counter)
            || !ready(counterSeed->pc, counter) || counterSeed->pc >= h - 4
            || originalIdentityState(flow, h - 4)->operator[](counter).definitions != std::set<unsigned>{counterInitial->id}
            || originalIdentityState(flow, h - 4)->operator[](counter).constant != std::optional<uint32_t>{0}
            || counterSeed->word != ((counter << 11) | 33u)
            || !originalIdentityWriter(flow, h - 4, pointer, seed->pc, true)
            || !originalIdentityWriter(flow, h - 4, counter, counterSeed->pc, true)) continue;
        auto start = originalEntryOffset(initial->id, flow);
        auto endId = *(*endState)[endpoint].definitions.begin();
        auto end = originalEntryOffset(endId, flow);
        if (!start || !end || start->entry != 29 || end->entry != 29
            || !originalIdentityWriter(flow, h + 20, endpoint, flow.definitions.at(endId).pc)) continue;
        uint32_t count = end->offset - start->offset, maskBits = mask & 0xffff;
        if (!count || count > Disposition::RowLimit || count > maskBits || (maskBits & (maskBits + 1))) continue;
        std::set<Edge> edges{
            {h - 4, h, {}, "fallthrough"}, {h, h + 4, {}, "fallthrough"},
            {h + 4, h + 8, {}, "fallthrough"}, {h + 8, h + 12, h + 8, "delay-slot"},
            {h + 12, h + 16, {}, "fallthrough"}, {h + 12, h + 36, {}, "branch"},
            {h + 16, h + 20, {}, "fallthrough"}, {h + 20, h + 24, {}, "fallthrough"},
            {h + 24, h + 28, h + 24, "delay-slot"}, {h + 28, h, {}, "branch"},
            {h + 28, h + 32, {}, "fallthrough"}, {h + 32, h + 36, {}, "fallthrough"}};
        if (!closed(h, h + 32, edges)) continue;
        std::set<uint64_t> evidence = start->evidence;
        evidence.insert(end->evidence.begin(), end->evidence.end());
        evidence.insert(counterSeed->pc); evidence.insert(h - 4);
        for (uint64_t pc = h; pc <= h + 32; pc += 4) evidence.insert(pc);
        // Endpoint equality stops the scan even when signed pointer order changes at wrap.
        publish(h, pointer, start->offset, count, evidence, {initial->id, recurrence->id});

        uint64_t guard = h + 36, body = guard + 12;
        uint32_t guardWord = word(guard), bodyLoad = word(body), bodyCompare = word(body + 24);
        unsigned index = (word(guard + 4) >> 11) & 31, bodyPointer = (bodyLoad >> 21) & 31;
        unsigned bodyValue = (bodyLoad >> 16) & 31, bodyComparison = (bodyCompare >> 11) & 31;
        std::set<unsigned> bodyRegisters{index, bodyPointer, countRegister, bodyComparison};
        if (bodyRegisters.size() != 4 || bodyRegisters.count(0) || bodyValue != bodyComparison
            || guardWord != ((6u << 26) | (countRegister << 21) | 11u)
            || word(guard + 4) != ((index << 11) | 33u)
            || bodyLoad != ((36u << 26) | (bodyPointer << 21) | (bodyValue << 16))
            || word(body + 16) != ((9u << 26) | (index << 21) | (index << 16) | 1u)
            || word(body + 20) != ((40u << 26) | (bodyPointer << 21) | (bodyValue << 16))
            || bodyCompare != ((index << 21) | (countRegister << 16) | (bodyComparison << 11) | 42u)
            || word(body + 28) != ((5u << 26) | (bodyComparison << 21) | 0xfff8u)
            || word(body + 32) != ((9u << 26) | (bodyPointer << 21) | (bodyPointer << 16) | 1u)) continue;
        const auto* bodySeed = definition(guard + 8, bodyPointer);
        const auto* bodyRecurrence = definition(body + 32, bodyPointer);
        const auto* earlyMask = definition(h + 12, countRegister);
        const auto* finalMask = definition(h + 32, countRegister);
        const auto* guardState = originalIdentityState(flow, guard);
        if (!bodySeed || !bodyRecurrence || !earlyMask || !finalMask || !guardState || !ready(guard, countRegister)
            || (*guardState)[countRegister].definitions != std::set<unsigned>{earlyMask->id, finalMask->id}) continue;
        auto bodyBase = originalEntryOffset(bodySeed->id, flow);
        if (!bodyBase || bodyBase->entry != 29 || bodyBase->offset != start->offset) continue;
        bool unmodified = true;
        for (uint64_t pc = body + 4; pc <= body + 12; pc += 4) {
            auto found = flow.instructions.find(pc);
            if (found == flow.instructions.end()) { unmodified = false; break; }
            auto operation = originalOperation(*found->second);
            if (operation.kind != MipsOperation::Load && operation.kind != MipsOperation::Store
                && operation.kind != MipsOperation::Compute) { unmodified = false; break; }
            for (auto reg : operation.destinations)
                if (reg == bodyPointer || reg == index || reg == countRegister) unmodified = false;
        }
        if (!unmodified) continue;
        std::set<Edge> bodyEdges{
            {h + 12, guard, {}, "branch"}, {h + 32, guard, {}, "fallthrough"},
            {guard, guard + 4, guard, "delay-slot"}, {guard + 4, guard + 8, {}, "fallthrough"},
            {guard + 4, body + 36, {}, "branch"}, {guard + 8, body, {}, "fallthrough"},
            {body + 28, body + 32, body + 28, "delay-slot"},
            {body + 32, body, {}, "branch"}, {body + 32, body + 36, {}, "fallthrough"}};
        for (uint64_t pc = body; pc < body + 28; pc += 4) bodyEdges.emplace(pc, pc + 4, std::nullopt, "fallthrough");
        if (!closed(guard, body + 32, bodyEdges)) continue;
        for (uint64_t pc = guard; pc <= body + 32; pc += 4) evidence.insert(pc);
        evidence.insert(bodyBase->evidence.begin(), bodyBase->evidence.end());
        std::set<unsigned> writers{bodySeed->id, bodyRecurrence->id};
        publish(body, bodyPointer, start->offset, count, evidence, writers);
        publish(body + 20, bodyPointer, start->offset, count, evidence, writers);
    }
    return result;
}

struct OriginalImageView {
    uint32_t mappingStart;
    const std::vector<uint8_t>& payload;
    bool physical;
    const common::PsxMemoryContext* context = nullptr;
    const common::PsxOriginalImage* owner = nullptr;
    bool contains(uint64_t address, uint64_t count) const {
        if (context) {
            auto span = context->resolve(address, count);
            return span && span->image == owner;
        }
        return address >= mappingStart && address <= UINT32_MAX
            && count <= (uint64_t(1) << 32) - address
            && address - mappingStart <= payload.size()
            && count <= payload.size() - (address - mappingStart);
    }
    uint32_t word(uint64_t address) const {
        if (context) {
            auto span = context->resolve(address, 4);
            return uint32_t(span->bytes[0]) | uint32_t(span->bytes[1]) << 8
                | uint32_t(span->bytes[2]) << 16 | uint32_t(span->bytes[3]) << 24;
        }
        auto offset = address - mappingStart;
        return uint32_t(payload[offset]) | uint32_t(payload[offset + 1]) << 8
            | uint32_t(payload[offset + 2]) << 16 | uint32_t(payload[offset + 3]) << 24;
    }
};

std::optional<OriginalImageView> originalImageView(const FileImage* image,
    const common::OriginalCallScope& scope, const config::Parameters& parameters,
    const Disposition::Evidence& evidence, const std::string& function,
    const common::OriginalDiscoveredFunction* discovered = nullptr)
{
    if (!image || evidence.start % 4 || evidence.end % 4 || evidence.start >= evidence.end) return {};
    if (const auto& context = parameters.getPsxMemoryContext()) {
        auto span = context->resolve(evidence.start, evidence.end - evidence.start);
        if (!span) return {};
        bool identity = false;
        auto reviewed = [&](const auto& row) {
            if (row.start == evidence.start && row.end == evidence.end && row.key == function
                && row.imageId == span->image->id) identity = true;
        };
        reviewed(scope.root); for (const auto& row : scope.callees) reviewed(row);
        if (discovered) identity = discovered->start == evidence.start && discovered->end == evidence.end
            && discovered->key == function && discovered->imageId == span->image->id
            && discovered->contextHash == context->identity();
        if (!identity) return {};
        OriginalImageView view{uint32_t(*common::psxRamAddress(span->image->loadAddress)),
            *span->image->payload, true, context.get(), span->image};
        std::set<uint64_t> pcs;
        for (const auto& row : evidence.instructions) {
            if (row.pc < evidence.start || row.pc >= evidence.end || row.pc % 4 || row.bytes != 4
                || row.owner != evidence.symbol || !row.mapped || row.undef || !pcs.insert(row.pc).second
                || !view.contains(row.pc, 4) || view.word(row.pc) != row.word) return {};
            if (discovered && (!discovered->words.count(row.pc) || discovered->words.at(row.pc) != row.word)) return {};
            auto physical = image->getImage()->getRawSegmentData(row.pc);
            auto original = context->resolve(row.pc, 4);
            if (!physical.first || physical.second < 4 || !std::equal(original->bytes, original->bytes + 4, physical.first)) return {};
        }
        return view;
    }
    unsigned identities = 0;
    auto matchIdentity = [&](const common::ReviewedOriginalFunction& row) {
        identities += row.start == evidence.start && row.end == evidence.end && row.key == function;
    };
    matchIdentity(scope.root); for (const auto& row : scope.callees) matchIdentity(row);
    auto* format = image->getFileFormat();
    auto configuredLoad = parameters.getSectionVMA();
    if (identities != 1 || !format || !format->isRawData() || format->getSha256() != scope.payloadHash
        || scope.payloadHash.size() != 64 || configuredLoad.isUndefined() || configuredLoad.getValue() > UINT32_MAX) return {};
    uint64_t load = configuredLoad.getValue();
    const auto& payload = format->getBytes();
    if (payload.empty() || payload.size() > (uint64_t(1) << 32) - load || payload != format->getLoadedBytes()
        || evidence.start < load || evidence.end - load > payload.size()) return {};
    std::set<uint64_t> pcs;
    OriginalImageView view{uint32_t(load), payload, false};
    for (const auto& row : evidence.instructions) {
        if (row.pc < evidence.start || row.pc >= evidence.end || row.pc % 4 || row.bytes != 4
            || row.owner != evidence.symbol || !row.mapped || row.undef || !pcs.insert(row.pc).second
            || !view.contains(row.pc, 4) || view.word(row.pc) != row.word) return {};
    }
    auto* loaded = image->getImage();
    const auto* segment = loaded && loaded->getNumberOfSegments() == 1 ? loaded->getSegmentFromAddress(load) : nullptr;
    view.physical = segment && segment->getAddress() == load && segment->getSize() == payload.size()
        && segment->getPhysicalSize() == payload.size();
    if (view.physical) {
        auto raw = segment->getRawData();
        view.physical = raw.first && raw.second == payload.size() && std::equal(payload.begin(), payload.end(), raw.first);
    }
    return view;
}

bool originalEntryCoveredForResult(const Disposition::Evidence& evidence,
    const common::OriginalFunctionSummary& summary, const OriginalImageView& image,
    const std::map<unsigned, Disposition::Definition>& definitions)
{
    if (!image.physical || !evidence.decodeComplete || !evidence.analysisComplete
        || !summary.entry.isComplete() || !summary.control.isComplete()
        || summary.pendingEntry != "requires-no-pending-gpr-loads"
        || evidence.start % 4 || evidence.end % 4 || evidence.start >= evidence.end
        || evidence.end > (uint64_t(1) << 32)
        || evidence.instructions.size() != (evidence.end - evidence.start) / 4
        || evidence.exits.empty() || summary.exits.size() != evidence.exits.size()
        || summary.transfers.size() != Disposition::RegisterCount) return false;
    for (size_t i = 0; i < evidence.instructions.size(); ++i) {
        const auto& row = evidence.instructions[i];
        if (row.pc != evidence.start + 4 * i || row.owner != evidence.symbol
            || !row.mapped || row.undef || row.bytes != 4
            || !image.contains(row.pc, 4) || image.word(row.pc) != row.word) return false;
    }
    auto instruction = [&](uint64_t pc) -> const Disposition::Instruction* {
        if (pc < evidence.start || pc >= evidence.end || pc % 4) return nullptr;
        return &evidence.instructions[(pc - evidence.start) / 4];
    };
    auto settled = [&](const common::OriginalTransfer& transfer) {
        if (transfer.reg != 2 || transfer.kind != "assigned" || !transfer.proof.isComplete()
            || transfer.definitions.empty() || !transfer.bad.empty() || transfer.pending
            || !transfer.mayNoPending || !transfer.pendingDefinitions.empty()) return false;
        for (auto id : transfer.definitions) {
            auto found = definitions.find(id);
            if (found == definitions.end() || found->second.id != id || found->second.reg != 2
                || found->second.width != 32 || !found->second.bad.empty()
                || !instruction(found->second.pc)) return false;
        }
        return true;
    };
    if (!settled(summary.transfers[2])) return false;
    for (size_t i = 0; i < evidence.exits.size(); ++i) {
        const auto& exit = evidence.exits[i];
        const auto& normal = summary.exits[i];
        const auto* jump = instruction(exit.pc);
        if (!jump || jump->word != 0x03e00008 || exit.delaySlot != exit.pc + 4
            || !instruction(exit.delaySlot) || exit.missing || exit.definitions.empty()
            || !exit.bad.empty() || !exit.pendingDefinitions.empty()
            || normal.pc != exit.pc || normal.delay != exit.delaySlot
            || !normal.incomingLink.isComplete() || normal.transfers.size() != Disposition::RegisterCount
            || !settled(normal.transfers[2]) || normal.transfers[2].definitions != exit.definitions
            || normal.transfers[2].pendingDefinitions != exit.pendingDefinitions) return false;
    }
    return true;
}

using OriginalCalleePreservation = std::map<uint64_t, uint32_t>;

OriginalCalleePreservation originalCalleePreservation(
    const std::optional<common::OriginalCalleeContexts>& contexts,
    const config::Parameters& parameters, const Disposition::Evidence& evidence,
    const std::map<uint64_t, const Disposition::Instruction*>& instructions,
    const std::optional<OriginalImageView>& image)
{
    const auto& scope = parameters.getOriginalCallScope();
    if (!parameters.isOriginalOnlyReturnRecovery() || !scope || !contexts || !image || !image->physical
        || evidence.selection != "selected-root" || evidence.start != scope->root.start
        || evidence.end != scope->root.end || contexts->imageId != scope->root.imageId
        || contexts->payloadHash != scope->payloadHash || contexts->mappingStart != image->mappingStart
        || contexts->mappingBytes != image->payload.size() || contexts->candidates.size() > 32) return {};
    std::size_t retained = 0;
    std::set<uint64_t> owners;
    for (const auto& context : contexts->candidates) {
        if (context.words.size() > 256 || context.callPcs.size() > instructions.size()) return {};
        retained += context.words.size();
        if (retained > 4096) return {};
        for (auto pc : context.callPcs) if (!owners.insert(pc).second) return {};
    }
    OriginalCalleePreservation result;
    for (const auto& context : contexts->candidates) {
        if (!context.mayWriteGprs || (*context.mayWriteGprs & ((uint32_t(1) << 31) | 1))
            || context.entry % 4 || context.entry > UINT32_MAX - 1024
            || !context.words.count(context.entry) || context.normalReturnPcs.empty()) continue;
        bool valid = true;
        for (const auto& word : context.words) {
            auto overlaps = [&](const auto& member) { return member.start <= word.first && word.first < member.end; };
            valid &= word.first % 4 == 0 && word.first >= context.entry
                && uint64_t(word.first) - context.entry < 1024 && image->contains(word.first, 4)
                && image->word(word.first) == word.second && !overlaps(scope->root)
                && std::none_of(scope->callees.begin(), scope->callees.end(), overlaps);
        }
        std::set<uint32_t> returns;
        for (auto pc : context.normalReturnPcs) {
            auto ret = context.words.find(pc), delay = context.words.find(pc + 4);
            if (!returns.insert(pc).second || ret == context.words.end() || ret->second != 0x03e00008
                || delay == context.words.end()) { valid = false; continue; }
            Disposition::Instruction row; row.pc = pc + 4; row.word = delay->second;
            valid &= originalOperation(row).kind == MipsOperation::Compute;
        }
        if (!valid) continue;
        auto trusted = [&](const Disposition::Instruction* row) {
            return row && row->mapped && !row->undef && row->bytes == 4 && row->owner == evidence.symbol
                && row->pc % 4 == 0 && row->pc >= evidence.start && row->pc < evidence.end;
        };
        for (auto pc : context.callPcs) {
            auto call = instructions.find(pc), delay = instructions.find(pc + 4);
            if (call == instructions.end() || delay == instructions.end()
                || !trusted(call->second) || !trusted(delay->second) || call->second->word >> 26 != 3
                || originalOperation(*call->second).target != std::optional<uint64_t>{context.entry}) continue;
            auto operation = originalOperation(*delay->second);
            if (operation.kind != MipsOperation::Compute && operation.kind != MipsOperation::Multiply
                && operation.kind != MipsOperation::Divide && operation.kind != MipsOperation::Load
                && operation.kind != MipsOperation::Store) continue;
            bool width = true;
            for (auto reg : operation.destinations)
                width &= !reg || std::count(delay->second->fullWidthRegisters.begin(),
                    delay->second->fullWidthRegisters.end(), reg) == 1;
            if (width) result.emplace(pc, *context.mayWriteGprs);
        }
    }
    return result;
}

struct OriginalDispatchSite {
    uint64_t jumpPc;
    const Disposition::Evidence& evidence;
    const std::map<uint64_t, const Disposition::Instruction*>& instructions;
    const std::map<unsigned, Disposition::Definition>& definitions;
    const OriginalImageView& image;
    const std::string& imageId;
    const std::string& payloadHash;
};

class OriginalSnapshotDispatch {
    common::OriginalJumpTableContext _report;
    explicit OriginalSnapshotDispatch(common::OriginalJumpTableContext report) : _report(std::move(report)) {}
    friend std::optional<OriginalSnapshotDispatch> sampleOriginalJumpTable(const OriginalDispatchSite&, const RegisterState&);
public:
    std::set<uint32_t> distinctTargets() const { return {_report.indexedTargets.begin(), _report.indexedTargets.end()}; }
    const common::OriginalJumpTableContext& report() const { return _report; }
};

bool jumpTablePrefixCompute(const Disposition::Instruction& row)
{
    auto word = row.word;
    unsigned op = word >> 26, rs = (word >> 21) & 31, fn = word & 63, shift = (word >> 6) & 31;
    bool supported = op == 9 || op == 12 || op == 13 || op == 14 || (op == 15 && !rs)
        || (!op && (((fn == 0 || fn == 2 || fn == 3) && !rs)
            || ((fn == 33 || fn == 35 || (36 <= fn && fn <= 39)) && !shift)));
    if (!supported) return false;
    for (auto reg : originalOperation(row).destinations)
        if (reg && std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), reg) != 1) return false;
    return true;
}

std::optional<OriginalSnapshotDispatch> sampleOriginalJumpTable(
    const OriginalDispatchSite& site, const RegisterState& before)
{
    const auto& evidence = site.evidence;
    const auto& instructions = site.instructions;
    auto instruction = [&](uint64_t pc) -> const Disposition::Instruction* {
        auto found = instructions.find(pc); return found == instructions.end() ? nullptr : found->second;
    };
    auto* jump = instruction(site.jumpPc);
    if (!site.image.physical || !jump || site.jumpPc < evidence.start + 20
        || evidence.instructions.size() > Disposition::RowLimit) return {};
    auto operation = originalOperation(*jump);
    if (operation.kind != MipsOperation::Branch || operation.target || operation.name != "jr") return {};
    auto* shift = instruction(site.jumpPc - 20);
    auto* high = instruction(site.jumpPc - 16);
    auto* add = instruction(site.jumpPc - 12);
    auto* load = instruction(site.jumpPc - 8);
    auto* loadDelay = instruction(site.jumpPc - 4);
    auto* jumpDelay = instruction(site.jumpPc + 4);
    if (!shift || !high || !add || !load || !loadDelay || !jumpDelay) return {};
    unsigned selector = (shift->word >> 16) & 31, scaled = (shift->word >> 11) & 31;
    unsigned base = (high->word >> 16) & 31, target = (jump->word >> 21) & 31;
    if (!selector || !scaled || !base || !target || selector == scaled || selector == base || scaled == base
        || jump->word != ((target << 21) | 8)
        || shift->word != ((selector << 16) | (scaled << 11) | (2 << 6))
        || high->word >> 21 != (15 << 5)
        || (add->word != ((base << 21) | (scaled << 16) | (base << 11) | 33)
            && add->word != ((scaled << 21) | (base << 16) | (base << 11) | 33))
        || load->word >> 16 != ((35 << 10) | (base << 5) | target)
        || loadDelay->word != 0 || !jumpTablePrefixCompute(*jumpDelay)) return {};
    for (const auto* row : {shift, high, add, load})
        for (auto reg : originalOperation(*row).destinations)
            if (!reg || std::count(row->fullWidthRegisters.begin(), row->fullWidthRegisters.end(), reg) != 1) return {};
    const auto& visible = before[target];
    if (visible.missing || visible.constant || visible.equalEntry || visible.definitions.size() != 1
        || before.mayPending[target] || !before.mayNoPending[target]) return {};
    auto definition = site.definitions.find(*visible.definitions.begin());
    if (definition == site.definitions.end() || definition->second.pc != load->pc
        || definition->second.reg != target || definition->second.width != 32
        || !definition->second.delayed || definition->second.origin != "instruction") return {};

    const Disposition::Instruction* compare = nullptr;
    const Disposition::Instruction* guard = nullptr;
    uint64_t defaultPc = 0;
    uint32_t count = 0;
    for (const auto& pair : instructions) {
        const auto& row = *pair.second;
        if (row.pc < evidence.start || row.pc + 8 > shift->pc || row.word >> 26 != 11
            || ((row.word >> 21) & 31) != selector) continue;
        auto* candidate = instruction(row.pc + 4);
        if (!candidate) continue;
        unsigned comparison = (row.word >> 16) & 31, opcode = candidate->word >> 26;
        auto branch = originalOperation(*candidate);
        unsigned rs = (candidate->word >> 21) & 31, rt = (candidate->word >> 16) & 31;
        if (!comparison || comparison == selector || (opcode != 4 && opcode != 5)
            || !branch.target || !((rs == comparison && !rt) || (rt == comparison && !rs))) continue;
        if ((opcode == 4 && candidate->pc + 8 != shift->pc)
            || (opcode == 5 && *branch.target != shift->pc)) continue;
        auto bound = uint32_t(int32_t(int16_t(row.word)));
        if (!bound || bound > Disposition::RowLimit || compare) return {};
        compare = &row; guard = candidate; count = bound;
        defaultPc = opcode == 4 ? *branch.target : candidate->pc + 8;
    }
    if (!compare || !guard || std::count(compare->fullWidthRegisters.begin(), compare->fullWidthRegisters.end(),
        (compare->word >> 16) & 31) != 1 || !instruction(defaultPc)) return {};
    bool memoryPrefix = false;
    auto prefixStep = [&](const Disposition::Instruction& row) {
        if (jumpTablePrefixCompute(row)) return true;
        auto step = originalOperation(row);
        if (step.merge || (step.kind != MipsOperation::Load && step.kind != MipsOperation::Store)) return false;
        for (auto reg : step.destinations)
            if (reg && (reg >= Disposition::GprCount
                || std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), reg) != 1)) return false;
        memoryPrefix = true;
        return true;
    };
    std::set<uint64_t> prefix;
    for (uint64_t pc = evidence.start; pc < compare->pc; pc += 4) {
        auto* row = instruction(pc);
        if (!row || !prefixStep(*row)) return {};
        auto step = originalOperation(*row);
        if (pc + 4 == compare->pc && step.kind == MipsOperation::Load
            && std::find(step.destinations.begin(), step.destinations.end(), selector) != step.destinations.end()) return {};
        prefix.insert(pc);
    }
    auto* guardDelay = instruction(guard->pc + 4);
    if (!guardDelay || !prefixStep(*guardDelay)) return {};
    for (auto reg : originalOperation(*guardDelay).destinations) if (reg == selector) return {};
    prefix.insert(compare->pc); prefix.insert(guard->pc); prefix.insert(guardDelay->pc);
    for (uint64_t pc = shift->pc; pc <= jumpDelay->pc; pc += 4) prefix.insert(pc);
    if (prefix.count(defaultPc)) return {};
    for (const auto& pair : instructions) {
        auto candidate = originalOperation(*pair.second);
        if (candidate.target && prefix.count(*candidate.target)
            && !(pair.first == guard->pc && pair.second->word >> 26 == 5 && *candidate.target == shift->pc)) return {};
        if (!prefix.count(pair.first) && !candidate.target
            && (candidate.kind == MipsOperation::Branch || candidate.kind == MipsOperation::Call)) return {};
        if (prefix.count(pair.first) && pair.first != guard->pc && pair.first != jump->pc
            && (candidate.kind == MipsOperation::Branch || candidate.kind == MipsOperation::Call
                || candidate.kind == MipsOperation::Return || candidate.kind == MipsOperation::Trap)) return {};
        if (!prefix.count(pair.first) && prefix.count(pair.first + 4)) {
            bool endsNormalPath = candidate.kind == MipsOperation::Trap;
            auto previous = pair.first >= 4 ? instruction(pair.first - 4) : nullptr;
            if (previous) {
                auto branch = originalOperation(*previous);
                endsNormalPath |= branch.kind == MipsOperation::Return
                    || (branch.kind == MipsOperation::Branch && !branch.conditional);
            }
            if (!endsNormalPath) return {};
        }
    }
    uint32_t address = uint32_t((high->word & 0xffff) << 16)
        + uint32_t(int32_t(int16_t(load->word)));
    uint64_t bytes = uint64_t(count) * 4;
    if (address % 4 || !site.image.contains(address, bytes)
        || count + prefix.size() > Disposition::ReferenceLimit) return {};
    common::OriginalJumpTableContext report;
    report.jumpPc = jump->pc; report.loadPc = load->pc; report.comparePc = compare->pc;
    report.guardPc = guard->pc; report.defaultPc = defaultPc; report.selectorRegister = selector;
    report.tableAddress = address; report.imageId = site.imageId; report.payloadHash = site.payloadHash;
    report.tableBytes.mappingStart = site.image.mappingStart; report.tableBytes.mappingBytes = site.image.payload.size();
    if (site.image.context) {
        auto span = site.image.context->resolve(address, bytes);
        if (!span || span->image != site.image.owner) return {};
        report.tableBytes.payloadOffset = span->payloadOffset;
    } else report.tableBytes.payloadOffset = uint64_t(address) - site.image.mappingStart;
    report.tableBytes.bytes.assign(site.image.payload.begin() + report.tableBytes.payloadOffset,
        site.image.payload.begin() + report.tableBytes.payloadOffset + bytes);
    for (uint32_t index = 0; index < count; ++index) {
        auto destination = site.image.word(uint64_t(address) + 4 * index);
        if (destination % 4 || destination < evidence.start || destination >= evidence.end
            || !instruction(destination) || prefix.count(destination)) return {};
        report.indexedTargets.push_back(destination);
    }
    report.instructionEvidence.assign(prefix.begin(), prefix.end());
    report.conditions = {"this-image-supplies-executed-instructions", "entry-at-reviewed-function-start",
        "no-pending-entry-gpr-loads", "active-table-binding-matches-this-image",
        "loaded-table-words-equal-file-backed-initial-bytes", "instruction-fetches-and-loads-complete-normally",
        "mips-i-load-and-branch-delays"};
    if (memoryPrefix) report.conditions.push_back("memory-accesses-complete-normally");
    return OriginalSnapshotDispatch(std::move(report));
}

void recoverOriginalMemory(common::OriginalFunctionSummary& summary, const Disposition& disposition,
    const FileImage* image, const std::optional<OriginalImageView>& view,
    const std::map<uint64_t, common::OriginalMemoryAccess>& flowAccesses)
{
    summary.noMemoryWrites = common::OriginalFact::partial("memory-write-absence-unresolved");
    for (auto& access : summary.accesses) {
        const auto* flow = std::get_if<common::OriginalEntryRelativeMemoryAddress>(&access.address);
        const auto* fixed = std::get_if<common::OriginalFixedMemoryAddress>(&access.address);
        if ((!flow || (flow->derivation != common::OriginalEntryRelativeMemoryAddress::Derivation::Flow
            && flow->derivation != common::OriginalEntryRelativeMemoryAddress::Derivation::EntryFirstUse))
            && (!fixed || fixed->derivation != common::OriginalFixedMemoryAddress::Derivation::Flow))
            access.address = common::OriginalFact::partial("original-address-proof-unresolved");
    }
    const auto& evidence = disposition.evidence;
    auto selectOriginalMemory = [&] {
        if (!evidence.analysisComplete || !evidence.decodeComplete || !summary.control.isComplete()
            || summary.exits.empty() || !evidence.calls.empty() || summary.pendingEntry != "requires-no-pending-gpr-loads"
            || evidence.start % 4 || evidence.end % 4 || evidence.start >= evidence.end
            || evidence.instructions.size() != (evidence.end - evidence.start) / 4 || !image) return;
        if (!view) return;
        std::map<uint64_t, const Disposition::Instruction*> instructions;
        std::set<uint64_t> returns;
        for (const auto& row : evidence.instructions) {
            instructions.emplace(row.pc, &row);
            if (originalOperation(row).kind == MipsOperation::Return) returns.insert(row.pc);
        }
        if (returns.size() != summary.exits.size() || returns.size() != evidence.exits.size()) return;
        std::set<uint64_t> observedExits;
        for (const auto& exit : evidence.exits)
            if (!returns.count(exit.pc) || !observedExits.insert(exit.pc).second || exit.delaySlot != exit.pc + 4) return;
        for (const auto& exit : summary.exits)
            if (!returns.erase(exit.pc) || !exit.incomingLink.isComplete() || exit.sampledEntry != std::optional<unsigned>{31}
                || exit.delay != exit.pc + 4 || !instructions.count(exit.delay)
                || std::count(exit.equalityEvidence.begin(), exit.equalityEvidence.end(), exit.pc) != 1) return;
        std::map<std::pair<uint64_t, unsigned>, const Disposition::Definition*> definitions;
        std::set<unsigned> ids;
        for (const auto& definition : evidence.definitions)
            if (!definition.id || !ids.insert(definition.id).second
                || !definitions.emplace(std::make_pair(definition.pc, definition.reg), &definition).second) return;
        std::multimap<uint64_t, const Disposition::Edge*> outgoing, incoming;
        for (const auto& edge : evidence.edges) {
            outgoing.emplace(edge.from, &edge); incoming.emplace(edge.to, &edge);
        }
        for (auto& access : summary.accesses) {
            if (!instructions.count(access.pc)) continue;
            auto address = originalMemoryAddress(access, instructions, definitions);
            if (address && !originalMemoryPrefix(evidence, instructions, outgoing, incoming, access.pc, address->equalityEvidence))
                address.reset();
            if (!address) {
                auto relative = originalEntryRelativeMemoryAddress(access, instructions, definitions);
                if (relative && originalMemoryPrefix(evidence, instructions, outgoing, incoming, access.pc,
                        relative->equalityEvidence, relative->entryRegister)) {
                    access.address = std::move(*relative); continue;
                }
                auto candidate = flowAccesses.find(access.pc);
                if (candidate != flowAccesses.end()) {
                    const auto* flow = std::get_if<common::OriginalEntryRelativeMemoryAddress>(&candidate->second.address);
                    if (flow && (flow->derivation == common::OriginalEntryRelativeMemoryAddress::Derivation::Flow
                        || flow->derivation == common::OriginalEntryRelativeMemoryAddress::Derivation::EntryFirstUse))
                        access.address = *flow;
                    else if (const auto* bounded = std::get_if<common::OriginalBoundedEntryMemoryAddress>(&candidate->second.address))
                        access.address = *bounded;
                    else if (const auto* fixed = std::get_if<common::OriginalFixedMemoryAddress>(&candidate->second.address))
                        if (fixed->derivation == common::OriginalFixedMemoryAddress::Derivation::Flow) address = *fixed;
                }
                if (!address) continue;
            }
            access.address = std::move(*address);
        }
    };
    selectOriginalMemory();
    if (!evidence.analysisComplete || !evidence.decodeComplete
        || summary.pendingEntry != "requires-no-pending-gpr-loads"
        || evidence.start % 4 || evidence.end % 4 || evidence.start >= evidence.end
        || evidence.instructions.size() != (evidence.end - evidence.start) / 4 || !image || !view) return;
    uint64_t load = view->mappingStart;
    const auto& payload = view->payload;
    auto* loaded = image->getImage();
    for (auto& access : summary.accesses) {
        auto* address = std::get_if<common::OriginalFixedMemoryAddress>(&access.address);
        if (!address) continue;
        uint64_t count = access.width / 8, value = address->value;
        if (view->context && address->alignment.isComplete() && value + count <= (uint64_t(1) << 32)) {
            auto span = view->context->resolve(value, count);
            auto canonical = common::psxRamAddress(value);
            if (span && canonical) {
                auto mapping = common::psxRamAddress(span->image->loadAddress);
                if (mapping) {
                    common::OriginalFileBytes bytes;
                    bytes.mappingStart = uint32_t(*mapping); bytes.mappingBytes = span->image->payload->size();
                    bytes.payloadOffset = span->payloadOffset;
                    bytes.bytes.assign(span->bytes, span->bytes + span->size);
                    std::vector<uint8_t> physical;
                    if (loaded->getXBytes(*canonical, count, physical) && physical == bytes.bytes)
                        address->fileBytes = std::move(bytes);
                }
            }
        } else if (!view->context && view->physical && address->alignment.isComplete() && value >= load
            && value + count <= (uint64_t(1) << 32) && value - load <= payload.size()
            && count <= payload.size() - (value - load)) {
            common::OriginalFileBytes bytes;
            bytes.mappingStart = uint32_t(load); bytes.mappingBytes = payload.size(); bytes.payloadOffset = value - load;
            if (loaded->getXBytes(value, count, bytes.bytes) && bytes.bytes.size() == count
                && std::equal(bytes.bytes.begin(), bytes.bytes.end(), payload.begin() + bytes.payloadOffset))
                address->fileBytes = std::move(bytes);
        }
    }
}

template<typename Graph>
void composeOriginalCall(Disposition::Call& call, RegisterState& state, const Graph& graph,
    std::map<unsigned, Disposition::Definition>& definitions,
    std::map<std::tuple<uint64_t, unsigned, bool>, unsigned>& ids,
    std::set<std::tuple<uint64_t, unsigned, std::string>>& demands,
    Disposition::Evidence& evidence, Config& config, const OriginalCalleePreservation& preservation,
    std::map<uint64_t, OriginalFrameContract>& frameUses, bool allowFrames)
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
    auto preserved = preservation.find(call.pc);
    bool conditionalPreservation = !summary && preserved != preservation.end() && !pending
        && proof.actualIncomingLink == std::optional<uint32_t>{uint32_t(proof.continuation)};
    bool bindings = summary && summary->entry.isComplete() && !pending;
    if (summary) {
        std::map<unsigned, std::set<uint64_t>> uses;
        for (const auto& use : summary->demands) uses[use.reg].insert(use.pc);
        for (const auto& transfer : summary->transfers)
            if (transfer.kind == "assigned" && transfer.proof.isComplete() && !transfer.pending)
                for (auto entry : transfer.entries) uses.try_emplace(entry);
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
            if (!use.second.empty())
                for (auto incoming : value.entries) demands.emplace(call.pc, incoming, "call-input");
        }
        proof.inputs = bindings ? common::OriginalFact::complete() : common::OriginalFact::partial(pending ? "pending-call-boundary-load-unresolved" : "actual-live-in-binding-unresolved");
        bool control = summary->control.isComplete() && proof.actualIncomingLink == std::optional<uint32_t>{uint32_t(proof.continuation)};
        for (const auto& exit : summary->exits) proof.calleeExits.push_back(exit.pc);
        proof.control = control ? common::OriginalFact::complete() : common::OriginalFact::partial("bound-return-target-not-proved-equal-to-continuation");
        proof.result = summary->result; proof.effects = summary->effects; proof.declaration = summary->declaration;
        proof.registerTransfers = summary->transfers;
    }
    auto scoped = summary ? ScopedCallTransfer::bind(call, proof, *summary, before) : std::nullopt;
    auto frame = summary && allowFrames ? OriginalFrameContract::bind(call, proof, *summary, before) : std::nullopt;
    if (frame) frameUses.insert_or_assign(call.pc, *frame);
    else frameUses.erase(call.pc);
    bool conditionalAssigned = false;
    bool transfers = summary && summary->transfers.size() == Disposition::RegisterCount && proof.control.isComplete() && !pending;
    for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
        state[reg] = RegisterFact{};
        if (reg < Disposition::GprCount) {
            if (before.mayPending[reg]) state.pending[reg].bad.insert("pending-call-boundary-load-unresolved");
            state.mayPending[reg] = before.mayPending[reg]; state.mayNoPending[reg] = before.mayNoPending[reg];
        }
        if (conditionalPreservation && reg < Disposition::GprCount
            && !(preserved->second & (uint32_t(1) << reg))) { state[reg] = before[reg]; continue; }
        const common::OriginalTransfer* transfer = summary && summary->transfers.size() == Disposition::RegisterCount ? &summary->transfers[reg] : nullptr;
        if (transfer && transfer->pending && reg < Disposition::GprCount) {
            state.mayPending[reg] = true; state.mayNoPending[reg] = transfer->mayNoPending;
            state.pending[reg] = RegisterFact{}; state.pending[reg].bad.insert("pending-return-load-boundary-unresolved");
        }
        bool usable = transfer && transfer->reg == reg && transfer->proof.isComplete() && !transfer->pending && proof.control.isComplete() && !pending;
        transfers &= usable;
        if (usable && transfer->kind == "preserved") { state[reg] = before[reg]; continue; }
        if (!usable && frame && frame->preserves(reg)) { state[reg] = before[reg]; continue; }
        bool scopedAssigned = !usable && ((scoped && transfer == &scoped->transfer())
            || (frame && transfer == frame->assignedResult(before)));
        if ((usable || scopedAssigned) && transfer->kind == "assigned" && callee && !transfer->definitions.empty()) {
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
                output.possibleOneBits = before[*transfer->equalEntry].possibleOnes();
                output.equalityEvidence = before[*transfer->equalEntry].equalityEvidence;
            }
            else output.constant = transfer->constant;
            output.equalityEvidence.insert(call.pc); output.equalityEvidence.insert(proof.delay);
            definition.equalEntry = output.equalEntry; definition.constant = output.constant;
            definition.equalityEvidence.assign(output.equalityEvidence.begin(), output.equalityEvidence.end());
            state[reg] = std::move(output); conditionalAssigned |= scopedAssigned; continue;
        }
        state[reg].bad.insert(reg == 2 ? "unknown-call-result" : "unknown-call-clobber");
    }
    proof.transfers = transfers ? common::OriginalFact::complete() : common::OriginalFact::partial("register-or-pending-transfer-unresolved");
    if (summary && !proof.effects.isComplete() && evidence.obligations.size() < Disposition::RowLimit
        && std::none_of(evidence.obligations.begin(), evidence.obligations.end(), [&](const auto& row) { return row.pc == call.pc && row.reason == "callee-memory-effects-unresolved"; }))
        evidence.obligations.push_back({call.pc, "memory", "callee-memory-effects-unresolved"});
    if (conditionalPreservation || conditionalAssigned || frame) {
        state.conditionalCallees.insert(call.pc);
        if (state.conditionalCallees.size() > Disposition::ReferenceLimit)
            throw std::runtime_error("conditional-callee-references-exhausted");
        const std::string reason = frame ? "conditional-symbolic-frame-restoration-unresolved"
            : conditionalAssigned ? "conditional-callee-assigned-transfer-unresolved" : "conditional-callee-preservation-unresolved";
        if (std::none_of(evidence.obligations.begin(), evidence.obligations.end(), [&](const auto& row) {
            return row.pc == call.pc && row.domain == "architectural" && row.reason == reason;
        })) {
            if (evidence.obligations.size() >= Disposition::RowLimit)
                throw std::runtime_error("return-obligations-exhausted");
            evidence.obligations.push_back({call.pc, "architectural", reason});
        }
    }
    for (auto jumpPc : state.conditionalTables) {
        auto condition = "conditional-jump-table-" + std::to_string(jumpPc);
        proof.inputs.kind = common::OriginalFact::Kind::Partial;
        proof.inputs.remaining.push_back(std::move(condition));
    }
    for (auto callPc : state.conditionalCallees) {
        auto condition = "conditional-callee-preservation-" + std::to_string(callPc);
        proof.inputs.kind = common::OriginalFact::Kind::Partial;
        proof.transfers.kind = common::OriginalFact::Kind::Partial;
        proof.inputs.remaining.push_back(condition); proof.transfers.remaining.push_back(std::move(condition));
    }
    std::sort(proof.inputs.remaining.begin(), proof.inputs.remaining.end());
    proof.inputs.remaining.erase(std::unique(proof.inputs.remaining.begin(), proof.inputs.remaining.end()), proof.inputs.remaining.end());
    std::sort(proof.transfers.remaining.begin(), proof.transfers.remaining.end());
    proof.transfers.remaining.erase(std::unique(proof.transfers.remaining.begin(), proof.transfers.remaining.end()), proof.transfers.remaining.end());
    if (summary && summary->noMemoryWrites.isComplete() && proof.identity.isComplete()
        && proof.inputs.isComplete() && proof.control.isComplete() && !pending)
        proof.noMemoryWrites = common::OriginalFact::complete();
    proof.remaining.clear();
    for (const auto* dimension : {&proof.identity, &proof.inputs, &proof.transfers, &proof.result, &proof.control, &proof.effects, &proof.declaration})
        if (!dimension->isComplete()) proof.remaining.insert(proof.remaining.end(), dimension->remaining.begin(), dimension->remaining.end());
    std::sort(proof.remaining.begin(), proof.remaining.end()); proof.remaining.erase(std::unique(proof.remaining.begin(), proof.remaining.end()), proof.remaining.end());
    call.unresolved = proof.remaining; call.qualified = false; call.contract = std::move(proof);
}

}

namespace {
bool stackWordResultSupported(const Disposition& disposition,
	const common::OriginalFunctionSummary& summary)
{
	if (disposition.kind == Disposition::Kind::Unknown) {
		if (summary.result.kind != common::OriginalFact::Kind::Partial) return false;
	} else if (disposition.kind != Disposition::Kind::Value || !summary.result.isComplete()) return false;
	return std::all_of(disposition.evidence.obligations.begin(), disposition.evidence.obligations.end(),
		[&](const auto& obligation) {
			return obligation.domain != "architectural" || (disposition.kind == Disposition::Kind::Unknown
				&& obligation.pc == disposition.evidence.start
				&& obligation.reason == "all-path-v0-definition-unresolved");
		});
}

std::optional<common::OriginalEntryStackWordBody> proposeIncomingStackWordBody(
	const Disposition& disposition, const common::OriginalFunctionSummary& summary,
	const std::map<std::pair<uint64_t, uint64_t>, RegisterState>& states)
{
	const auto& evidence = disposition.evidence;
	if (!stackWordResultSupported(disposition, summary) || evidence.selection != "selected-root"
		|| !evidence.decodeComplete || !evidence.analysisComplete || !evidence.calls.empty()
		|| !summary.entry.isComplete() || !summary.control.isComplete()
		|| summary.declaration.kind != common::OriginalFact::Kind::Partial
		|| summary.effects.kind != common::OriginalFact::Kind::Partial
		|| summary.pendingEntry != "requires-no-pending-gpr-loads"
		|| evidence.exits.size() != 1 || summary.exits.size() != 1
		|| evidence.instructions.size() < 3 || evidence.instructions.size() > Disposition::RowLimit
		|| evidence.end != evidence.start + 4 * evidence.instructions.size()) return {};
	const auto& exit = evidence.exits.front();
	const auto& normal = summary.exits.front();
	if (exit.missing || exit.definitions.empty() || !exit.bad.empty() || !exit.pendingDefinitions.empty()
		|| normal.pc != exit.pc || normal.delay != exit.delaySlot
		|| !normal.incomingLink.isComplete() || normal.sampledEntry != 31) return {};
	std::map<uint64_t, const Disposition::Instruction*> instructions;
	std::multimap<uint64_t, const Disposition::Edge*> incoming, outgoing;
	std::optional<uint64_t> loadPc;
	unsigned returns = 0;
	bool prefix = true;
	for (unsigned index = 0; index < evidence.instructions.size(); ++index) {
		const auto& row = evidence.instructions[index];
		auto operation = originalOperation(row);
		if (row.pc != evidence.start + 4 * index || row.bytes != 4 || row.pc % 4
			|| row.owner != evidence.symbol || !row.mapped || row.undef || operation.merge
			|| operation.kind == MipsOperation::Unsupported || operation.kind == MipsOperation::Call
			|| operation.kind == MipsOperation::Trap) return {};
		instructions.emplace(row.pc, &row);
		for (auto reg : operation.destinations)
			if (reg == 29 || reg == 31 || (reg && std::count(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end(), reg) != 1)) return {};
		for (auto reg : operation.inputs) if (reg == 29) {
			if (loadPc || !prefix || row.word >> 26 != 35 || uint16_t(row.word) != 16
				|| !((row.word >> 16) & 31)) return {};
			loadPc = row.pc;
		}
		if (operation.kind == MipsOperation::Return) {
			if (row.word != 0x03e00008 || row.pc != exit.pc || exit.delaySlot != row.pc + 4) return {};
			++returns;
		}
		if (operation.kind == MipsOperation::Branch && (!operation.target
			|| *operation.target < evidence.start || *operation.target >= evidence.end)) return {};
		if (operation.kind == MipsOperation::Branch || operation.kind == MipsOperation::Store
			|| operation.kind == MipsOperation::Return) prefix = false;
	}
	if (!loadPc || returns != 1) return {};
	for (const auto& edge : evidence.edges) {
		if (!instructions.count(edge.from) || !instructions.count(edge.to)
			|| (edge.delayOwner && !instructions.count(*edge.delayOwner))) return {};
		incoming.emplace(edge.to, &edge); outgoing.emplace(edge.from, &edge);
	}
	if (!originalMemoryPrefix(evidence, instructions, outgoing, incoming, *loadPc, {}, 29)) return {};
	std::map<unsigned, const Disposition::Definition*> definitions;
	std::optional<unsigned> loadDefinition;
	for (const auto& definition : evidence.definitions) {
		if (!definitions.emplace(definition.id, &definition).second || definition.width != 32
			|| definition.origin != "instruction" || !instructions.count(definition.pc)) return {};
		if (definition.pc == *loadPc) {
			if (loadDefinition || definition.reg != ((instructions.at(*loadPc)->word >> 16) & 31)
				|| !definition.delayed || definition.operation != "full-register-load"
				|| !definition.inputs.empty() || !definition.formals.empty()
				|| definition.entries != std::vector<unsigned>{29}
				|| definition.bad != std::vector<std::string>{"unproved-entry-register-29"}) return {};
			loadDefinition = definition.id;
		}
	}
	if (!loadDefinition) return {};
	auto derivesFromLoad = [&](unsigned reference) {
		std::vector<unsigned> pending{reference};
		std::set<unsigned> visited;
		bool found = false;
		while (!pending.empty()) {
			auto id = pending.back(); pending.pop_back();
			if (!visited.insert(id).second) continue;
			if (visited.size() > Disposition::RowLimit || !definitions.count(id)) return false;
			found |= id == *loadDefinition;
			const auto& definition = *definitions.at(id);
			pending.insert(pending.end(), definition.inputs.begin(), definition.inputs.end());
		}
		return found;
	};
	for (const auto& pair : definitions) {
		const auto& definition = *pair.second;
		if (!definition.bad.empty() && (definition.bad != std::vector<std::string>{"unproved-entry-register-29"}
			|| !derivesFromLoad(definition.id))) return {};
	}
	for (auto reference : exit.definitions)
		if (!definitions.count(reference) || definitions.at(reference)->reg != 2 || !definitions.at(reference)->bad.empty()) return {};
	std::set<uint64_t> taintedUses;
	for (const auto& point : states) {
		if (!instructions.count(point.first.first) || !point.second.conditionalTables.empty()
			|| !point.second.conditionalCallees.empty()) return {};
		auto inputs = inputFact(point.second, originalOperation(*instructions.at(point.first.first)));
		if (inputs.bad.empty()) continue;
		if (inputs.bad != std::set<std::string>{"unproved-entry-register-29"} || inputs.missing) return {};
		if (point.first.first != *loadPc && (inputs.definitions.empty()
			|| std::none_of(inputs.definitions.begin(), inputs.definitions.end(), derivesFromLoad))) return {};
		taintedUses.insert(point.first.first);
	}
	for (const auto& demand : summary.demands)
		if (!((4 <= demand.reg && demand.reg <= 7) || (demand.reg == 31 && demand.role == "continuation")
			|| (demand.reg == 29 && taintedUses.count(demand.pc)))) return {};
	bool entryObligation = false;
	for (const auto& obligation : evidence.obligations) {
		if (obligation.domain == "entry") {
			if (obligation.reason != "unproved-control-or-effect-input" || !taintedUses.count(obligation.pc)) return {};
			entryObligation = true;
		}
	}
	if (!entryObligation) return {};
	return common::OriginalEntryStackWordBody{*loadPc, *loadDefinition};
}
}

void ParamReturn::qualifyReturns()
{
    OriginalContractGraph graph;
    const auto& parameters = _config->getConfig().parameters;
    const auto& scope = parameters.getOriginalCallScope();
    if (scope) {
        auto add = [&](const auto& identity) {
            graph.identities.emplace(identity.start, OriginalContractGraph::Identity{
                identity.key, identity.imageId, identity.start, identity.end});
        };
        add(scope->root); for (const auto& identity : scope->callees) add(identity);
        for (const auto& function : _config->getConfig().functions) {
            if (!function.originalDiscovered) continue;
            const auto& identity = *function.originalDiscovered;
            const auto& context = parameters.getPsxMemoryContext();
            if (!context || identity.contextHash != context->identity()) continue;
            auto span = context->resolve(identity.start, identity.end - identity.start);
            if (span && span->image->id == identity.imageId) add(identity);
        }
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
        if (cf->originalBodyCandidate) continue;
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
		cf->originalJumpTables.clear();
		std::optional<common::OriginalEntryStackWordBody> stackWordBody;
		auto obligation = [&](uint64_t pc, const std::string& domain, const std::string& reason) {
			for (const auto& row : evidence.obligations)
				if (row.pc == pc && row.domain == domain && row.reason == reason) return;
			if (evidence.obligations.size() >= Disposition::RowLimit)
				throw std::runtime_error("return-obligations-exhausted");
			evidence.obligations.push_back({pc, domain, reason});
		};
		try {
			auto extent = revised ? graph.identities.at(cf->getStart().getValue())
				: OriginalContractGraph::Identity{"", "", selected.getStart().getValue(), selected.getEnd().getValue()};
			if (evidence.start != extent.start || evidence.end != extent.end)
				throw std::runtime_error("decode-selection-evidence-missing");
			std::map<uint64_t, const Disposition::Instruction*> instructions;
			for (const auto& row : evidence.instructions) {
				if (!instructions.emplace(row.pc, &row).second)
					throw std::runtime_error("duplicate-decode-evidence");
			}
			auto imageView = revised ? originalImageView(_image, *scope, _config->getConfig().parameters,
				evidence, summary.function, cf->originalDiscovered ? &*cf->originalDiscovered : nullptr) : std::optional<OriginalImageView>{};
            const auto calleePreservation = originalCalleePreservation(cf->originalCalleeContexts,
                _config->getConfig().parameters, evidence, instructions, imageView);
			RegisterState entry;
            const auto& observation = _config->getConfig().parameters.getOriginalEntryObservation();
            if (observation && observation->function == summary.function && observation->pc == extent.start
                && observation->imageId == extent.imageId && imageView && imageView->owner
                && observation->imageHash == imageView->owner->fileHash) {
                summary.entryContext = common::OriginalObservedEntryContext{
                    observation->identity, observation->stateHash, observation->pc, observation->cpu};
                if (observation->cpu.inIsr)
                    obligation(extent.start, "architectural", "observed-isr-context-preservation-unresolved");
            }
            std::map<uint64_t, OriginalFrameContract> frameUses;
            entry.storage = OriginalMemoryState::bind(observation ? &*observation : nullptr,
                summary.function, extent.imageId, imageView && imageView->owner ? imageView->owner->fileHash : "", evidence);
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
			std::map<uint64_t, RegisterFact> sampledBranchTargets;
			std::set<std::tuple<uint64_t, unsigned, std::string>> demands;
			std::map<uint64_t, common::OriginalMemoryAccess> accesses;
			std::set<std::tuple<uint64_t, uint64_t, uint64_t, std::string>> edges;
			std::map<uint64_t, unsigned> branchPaths;
			std::map<uint64_t, OriginalSnapshotDispatch> sampledDispatches;
			std::set<uint64_t> rejectedDispatches;
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
				bool trustedInstruction = row.mapped && row.owner == evidence.symbol
					&& row.bytes == 4 && row.pc % 4 == 0 && !row.undef;
				if (!trustedInstruction)
					obligation(pc, "architectural", "unsupported-pc-ir-join");
				if (operation.kind == MipsOperation::Unsupported)
					obligation(pc, "architectural", "unsupported-machine-operation");
                if (revised && (!trustedInstruction || operation.kind == MipsOperation::Unsupported)) {
                    for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
                        state[reg].constant.reset(); state[reg].possibleOneBits = UINT32_MAX;
                        if (reg < Disposition::GprCount) {
                            state.pending[reg].constant.reset(); state.pending[reg].possibleOneBits = UINT32_MAX;
                        }
                    }
                }
				if (operation.kind == MipsOperation::Trap) {
					obligation(pc, "architectural", "break-exception-control-unresolved");
					obligation(pc, "effect", "break-exception-effects-unresolved");
					continue;
				}
				bool control = operation.kind == MipsOperation::Branch
					|| operation.kind == MipsOperation::Call || operation.kind == MipsOperation::Return;
				if (owner && control) {
					obligation(pc, "architectural", "control-in-delay-slot"); continue;
				}
                bool branchPathsChanged = false;
                if (revised && operation.conditional) {
                    auto& paths = branchPaths[pc];
                    unsigned widened = paths | (trustedInstruction ? originalBranchPaths(row, state) : BothBranchPaths);
                    branchPathsChanged = widened != paths; paths = widened;
                }
                bool dispatchChanged = false;
                bool branchTargetChanged = false;
                if (revised && !owner && operation.kind == MipsOperation::Branch
                    && !operation.target && operation.name == "jr") {
                    auto target = state[operation.inputs.front()];
                    if (!trustedInstruction) target.bad.insert("unsupported-pc-ir-join");
                    auto sampled = sampledBranchTargets.emplace(pc, target);
                    branchTargetChanged = sampled.second || joinFact(sampled.first->second, target);
                    std::optional<OriginalSnapshotDispatch> dispatch;
                    if (imageView && !rejectedDispatches.count(pc))
                        dispatch = sampleOriginalJumpTable({pc, evidence, instructions, definitions,
                            *imageView, extent.imageId, imageView->owner ? imageView->owner->payloadHash : scope->payloadHash}, state);
                    if (dispatch) {
                        dispatchChanged = sampledDispatches.emplace(pc, std::move(*dispatch)).second;
                    } else {
                        dispatchChanged = sampledDispatches.erase(pc) != 0;
                        rejectedDispatches.insert(pc);
                    }
                }
				auto inputs = inputFact(state, operation);
                auto retainedMask = revised ? retainedLoadMask(operation, row, state) : std::optional<uint32_t>{};
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
                if (operation.kind == MipsOperation::Call && !operation.destinations.empty()) {
                    inputs = RegisterFact{}; inputs.missing = false;
                }
                auto identityState = state;
                state.storage.step(row, operation, state);
                auto immediateDestination = operation.kind != MipsOperation::Load && operation.destinations.size() == 1
                    ? std::optional<unsigned>{operation.destinations.front()} : std::optional<unsigned>{};
                for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
                    if (state.mayPending[reg] && (!immediateDestination || *immediateDestination != reg)) {
                        if (state.mayNoPending[reg]) joinFact(state[reg], state.pending[reg]);
                        else state[reg] = state.pending[reg];
                    }
                    state.mayPending[reg] = false; state.mayNoPending[reg] = true;
                }
                if (operation.kind == MipsOperation::Load && operation.merge && (!retainedMask || *retainedMask)) {
                    const auto& retained = state[operation.destinations.front()];
                    joinFact(inputs, retained);
                    if (retained.missing) inputs.bad.insert("merge-load-retained-value-unresolved");
                    if (revised) for (auto incoming : retained.entries) demands.emplace(pc, incoming, "result");
                }

				if (row.undef) inputs.bad.insert("ir-undef");
				if (!row.mapped || operation.kind == MipsOperation::Unsupported)
					inputs.bad.insert("unsupported-operation");
				if ((operation.kind == MipsOperation::Multiply || operation.kind == MipsOperation::Divide)
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
                        if (trustedInstruction && width) establishIdentity(output, identityState, row, destination);
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
				if ((operation.kind == MipsOperation::Store || (operation.kind == MipsOperation::Branch
                    && (!revised || !operation.conditional || branchPaths.at(pc) == BothBranchPaths)))
					&& !inputs.bad.empty()) {
					bool entryInput = revised && !inputs.missing
						&& std::all_of(inputs.bad.begin(), inputs.bad.end(), [&](const auto& reason) {
							return std::any_of(inputs.entries.begin(), inputs.entries.end(), [&](unsigned reg) {
								return (reg == 1 || reg == 3 || (8 <= reg && reg <= 30))
									&& reason == "unproved-entry-register-" + std::to_string(reg);
							});
						});
					obligation(pc, entryInput ? "entry" : "architectural", "unproved-control-or-effect-input");
				}
				auto recordEdge = [&](uint64_t target, uint64_t delayOwner, const std::string& kind) {
					edges.emplace(pc, target, delayOwner, kind);
					if (edges.size() > Disposition::RowLimit) throw std::runtime_error("return-edges-exhausted");
				};
				auto send = [&](uint64_t target, uint64_t delayOwner, const std::string& kind, bool forceQueue = false) {
					recordEdge(target, delayOwner, kind);
					Node next{target, delayOwner};
					auto insertion = states.emplace(next, state);
					if (states.size() > Disposition::RowLimit) throw std::runtime_error("return-states-exhausted");
					if (insertion.second || joinState(insertion.first->second, state) || forceQueue) work.push_back(next);
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
                        if (revised) composeOriginalCall(call, state, graph, definitions, ids, demands, evidence, *_config, calleePreservation, frameUses, !observation);
                        else {
                            call.unresolved = {"argument-result-effect-contract-unresolved"};
                            for (unsigned reg = 1; reg < Disposition::RegisterCount; ++reg) {
                                state[reg] = RegisterFact{};
                                if (reg < Disposition::GprCount) { state.mayPending[reg] = false; state.mayNoPending[reg] = true; }
                                state[reg].bad.insert(reg == 2 ? "unknown-call-result" : "unknown-call-clobber");
                            }
                        }
						state.storage.call(owner, call.contract ? &*call.contract : nullptr);
						send(owner + 8, 0, "call-continuation");
					}
					else {
                        unsigned paths = revised && branch.conditional ? branchPaths.at(owner) : BothBranchPaths;
                        if (paths & BranchTaken) {
                            if (branch.target) send(*branch.target, 0, "branch");
                            else {
                                auto sampled = sampledBranchTargets.find(owner);
                                if (sampled != sampledBranchTargets.end() && !sampled->second.missing
                                    && sampled->second.bad.empty() && sampled->second.constant.has_value()
                                    && *sampled->second.constant % 4 == 0) {
                                    auto target = *sampled->second.constant;
                                    if (target >= evidence.start && target < evidence.end)
                                        send(target, 0, "branch");
                                    else {
                                        recordEdge(target, 0, "branch");
                                        obligation(owner, "architectural", "external-tail-transfer-contract-unresolved");
                                        const auto& context = _config->getConfig().parameters.getPsxMemoryContext();
                                        bool owned = context ? bool(context->resolve(target, 4))
                                            : imageView && imageView->contains(target, 4);
                                        if (!owned)
                                            obligation(owner, "architectural", "external-tail-transfer-owner-unresolved");
                                    }
                                } else {
                                    obligation(owner, "architectural", "unresolved-branch-target");
                                    auto dispatch = sampledDispatches.find(owner);
                                    if (dispatch != sampledDispatches.end()) {
                                        state.conditionalTables.insert(owner);
                                        for (auto target : dispatch->second.distinctTargets())
                                            send(target, 0, "conditional-table-branch");
                                    }
                                }
                            }
                        }
						if (branch.conditional && (paths & BranchFallthrough)) send(owner + 8, 0, "fallthrough");
					}
				}
				else if (control) send(pc + 4, pc, "delay-slot", branchPathsChanged || dispatchChanged || branchTargetChanged);
				else send(pc + 4, 0, "fallthrough");
			}
			for (const auto& edge : edges) evidence.edges.push_back({std::get<0>(edge), std::get<1>(edge),
				std::get<2>(edge) ? std::optional<uint64_t>(std::get<2>(edge)) : std::nullopt, std::get<3>(edge)});
            if (revised && std::none_of(evidence.obligations.begin(), evidence.obligations.end(),
                [](const auto& row) { return row.domain == "architectural"
                    && row.reason != "conditional-symbolic-frame-restoration-unresolved"; })) {
                std::multimap<uint64_t, const Disposition::Edge*> incoming;
                for (const auto& edge : evidence.edges) incoming.emplace(edge.to, &edge);
                OriginalIdentityFlow flow{evidence.start, evidence.symbol, instructions, definitions, states, incoming, calls, originalOperation, &frameUses};
                for (auto& pair : definitions) {
                    auto& definition = pair.second;
                    if (definition.equalEntry) continue;
                    auto identity = originalEntryOffset(pair.first, flow);
                    if (!identity || identity->offset || !identity->adjusted) continue;
                    definition.equalEntry = identity->entry;
                    definition.equalityEvidence.assign(identity->evidence.begin(), identity->evidence.end());
                }
                for (auto& exit : exitStates) for (unsigned reg = 1; reg < Disposition::GprCount; ++reg) {
                    auto& value = exit.second[reg];
                    if (value.equalEntry || value.missing || value.definitions.size() != 1
                        || exit.second.mayPending[reg] || !exit.second.mayNoPending[reg]) continue;
                    auto id = *value.definitions.begin();
                    auto identity = originalEntryOffset(id, flow);
                    if (!identity || identity->offset || !identity->adjusted
                        || !originalIdentityWriter(flow, exit.first + 4, reg, definitions.at(id).pc, true)) continue;
                    value.equalEntry = identity->entry; value.equalityEvidence = identity->evidence;
                }
                for (auto& pair : accesses) {
                    auto fixed = originalFlowFixedMemoryAddress(pair.second, flow);
                    if (fixed) { pair.second.address = std::move(*fixed); continue; }
                    auto address = originalFlowMemoryAddress(pair.second, flow);
                    if (address) pair.second.address = std::move(*address);
                }
                for (auto& pair : recoverOriginalStackRanges(flow, accesses))
                    if (std::holds_alternative<common::OriginalFact>(accesses.at(pair.first).address))
                        accesses.at(pair.first).address = std::move(pair.second);
            }
			std::size_t references = 0;
			for (const auto& pair : sampledDispatches) {
				const auto& table = pair.second.report();
				references += table.indexedTargets.size() + table.instructionEvidence.size();
				if (references > Disposition::ReferenceLimit) throw std::runtime_error("return-references-exhausted");
				cf->originalJumpTables.push_back(table);
			}
			for (auto& pair : definitions) {
				references += pair.second.inputs.size() + pair.second.formals.size() + pair.second.bad.size();
				if (references > Disposition::ReferenceLimit) throw std::runtime_error("return-references-exhausted");
				if (observation) evidence.definitions.push_back(std::move(pair.second));
                else evidence.definitions.push_back(pair.second);
			}
			for (auto& pair : exits) evidence.exits.push_back(std::move(pair.second));
			for (auto& pair : calls) {
                if (observation) evidence.calls.push_back(std::move(pair.second));
                else evidence.calls.push_back(pair.second);
            }
			evidence.decodeComplete = std::none_of(evidence.obligations.begin(), evidence.obligations.end(),
				[](const auto& row) { return row.domain == "architectural"; });
			evidence.analysisComplete = true;
			bool value = evidence.decodeComplete && !evidence.exits.empty();
			bool entryCovered = std::none_of(evidence.obligations.begin(), evidence.obligations.end(),
				[](const auto& row) { return row.domain == "entry"; });
			for (const auto& exit : evidence.exits)
				value &= !exit.missing && !exit.definitions.empty() && exit.bad.empty();
			if (revised) {
                bool flowComplete = imageView && evidence.analysisComplete
                    && (evidence.decodeComplete || std::none_of(evidence.obligations.begin(), evidence.obligations.end(),
                        [](const auto& row) { return row.domain == "architectural"
                            && row.reason != "conditional-symbolic-frame-restoration-unresolved"; }))
                    && summary.pendingEntry == "requires-no-pending-gpr-loads"
                    && evidence.start % 4 == 0 && evidence.end % 4 == 0 && evidence.start < evidence.end
                    && instructions.size() == (evidence.end - evidence.start) / 4
                    && std::all_of(branchPaths.begin(), branchPaths.end(),
                        [](const auto& branch) { return branch.second == BothBranchPaths; });
                if (!flowComplete) for (auto& pair : accesses) {
                    const auto* flow = std::get_if<common::OriginalEntryRelativeMemoryAddress>(&pair.second.address);
                    const auto* fixed = std::get_if<common::OriginalFixedMemoryAddress>(&pair.second.address);
                    if ((flow && flow->derivation == common::OriginalEntryRelativeMemoryAddress::Derivation::Flow)
                        || (fixed && fixed->derivation == common::OriginalFixedMemoryAddress::Derivation::Flow))
                        pair.second.address = common::OriginalFact::partial("original-address-proof-unresolved");
                }
                if (imageView && !observation && summary.pendingEntry == "requires-no-pending-gpr-loads") {
                    std::multimap<uint64_t, const Disposition::Edge*> incoming;
                    for (const auto& edge : evidence.edges) incoming.emplace(edge.to, &edge);
                    OriginalIdentityFlow flow{evidence.start, evidence.symbol, instructions, definitions, states,
                        incoming, calls, originalOperation, &frameUses};
                    for (auto& pair : accesses) {
                        if (!std::holds_alternative<common::OriginalFact>(pair.second.address)) continue;
                        auto address = OriginalEntryAddressRegion::recover(flow, evidence, pair.second);
                        if (address) pair.second.address = std::move(*address);
                    }
                }
                summarizeOriginal(summary, disposition, exitStates, sampledTargets, demands, accesses, graph.unavailable.count(evidence.start));
                if (flowComplete && summary.entry.isComplete()) {
                    OriginalMemoryState::summarize(summary, exitStates);
                    if (!observation) {
                        std::multimap<uint64_t, const Disposition::Edge*> incoming;
                        for (const auto& edge : evidence.edges) incoming.emplace(edge.to, &edge);
                        OriginalIdentityFlow flow{evidence.start, evidence.symbol, instructions, definitions, states, incoming, calls, originalOperation, &frameUses};
                        summary.symbolicFrame = OriginalFrameContract::recover(flow, evidence, summary, exitStates, sampledTargets);
                    }
                }
            }
            entryCovered |= revised && !observation && imageView
                && originalEntryCoveredForResult(evidence, summary, *imageView, definitions);
            value &= entryCovered;
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
                recoverOriginalMemory(summary, disposition, _image, imageView, accesses);
                bool noWrites = imageView && evidence.decodeComplete && evidence.analysisComplete
                    && summary.entry.isComplete() && summary.control.isComplete() && !summary.exits.empty()
                    && summary.pendingEntry == "requires-no-pending-gpr-loads"
                    && evidence.start % 4 == 0 && evidence.end % 4 == 0 && evidence.start < evidence.end
                    && evidence.end <= (uint64_t(1) << 32)
                    && evidence.instructions.size() == (evidence.end - evidence.start) / 4;
                size_t readCount = 0, callCount = 0;
                for (size_t i = 0; noWrites && i < evidence.instructions.size(); ++i) {
                    const auto& row = evidence.instructions[i];
                    auto operation = originalOperation(row);
                    noWrites = row.pc == evidence.start + 4 * i && row.mapped && row.owner == evidence.symbol
                        && row.bytes == 4 && !row.undef && !operation.merge
                        && operation.kind != MipsOperation::Store && operation.kind != MipsOperation::Trap
                        && operation.kind != MipsOperation::Unsupported;
                    if (operation.kind == MipsOperation::Load) {
                        ++readCount;
                        auto access = std::find_if(summary.accesses.begin(), summary.accesses.end(),
                            [&](const auto& value) { return value.pc == row.pc; });
                        if (access == summary.accesses.end()) { noWrites = false; continue; }
                        const auto* address = std::get_if<common::OriginalFixedMemoryAddress>(&access->address);
                        unsigned opcode = row.word >> 26;
                        unsigned width = opcode == 32 || opcode == 36 ? 8 : opcode == 33 || opcode == 37 ? 16 : 32;
                        uint64_t count = width / 8;
                        const auto* bytes = address ? std::get_if<common::OriginalFileBytes>(&address->fileBytes) : nullptr;
                        auto start = address ? common::psxRamAddress(address->value) : std::nullopt;
                        auto end = address ? common::psxRamAddress(uint64_t(address->value) + count - 1) : std::nullopt;
                        noWrites &= access->kind == "read" && access->delayed && access->width == width
                            && std::count_if(summary.accesses.begin(), summary.accesses.end(),
                                [&](const auto& value) { return value.pc == row.pc; }) == 1
                            && address && address->alignment.isComplete() && address->value % count == 0
                            && start && end && *end == *start + count - 1 && bytes && bytes->bytes.size() == count;
                    }
                    if (operation.kind == MipsOperation::Call) {
                        ++callCount;
                        auto call = std::find_if(evidence.calls.begin(), evidence.calls.end(),
                            [&](const auto& value) { return value.pc == row.pc; });
                        if (call == evidence.calls.end() || !call->contract) { noWrites = false; continue; }
                        const auto* partial = std::get_if<common::OriginalPartialCall>(&*call->contract);
                        const auto& proof = partial ? *partial : std::get<common::OriginalCompleteCall>(*call->contract).proof();
                        noWrites &= proof.noMemoryWrites.isComplete();
                    }
                }
                if (noWrites && readCount == summary.accesses.size() && callCount == evidence.calls.size())
                    summary.noMemoryWrites = common::OriginalFact::complete();
				if (imageView && cf->parameters.empty())
					stackWordBody = proposeIncomingStackWordBody(disposition, summary, states);
            }
		} catch (const std::exception& error) {
			disposition.kind = Disposition::Kind::Unknown;
            evidence.decodeComplete = false; evidence.analysisComplete = false;
            evidence.definitions.clear(); evidence.edges.clear(); evidence.exits.clear(); evidence.calls.clear();
            cf->originalJumpTables.clear();
            summary.scopedRestoration.reset();
            summary.symbolicFrame.reset();
            summary.noMemoryWrites = common::OriginalFact::partial("native-analysis-failed");
            for (auto& access : summary.accesses) access.address = common::OriginalFact::partial("native-analysis-failed");
            if (evidence.obligations.size() < Disposition::RowLimit)
				evidence.obligations.push_back({evidence.start, "architectural", error.what()});
		}
		if (revised) {
            if (summary.exits.empty()) summary.control = common::OriginalFact::partial("nonempty-normal-exit-closure-unresolved");
            cf->originalCallSummary = std::move(summary);
        }
		de.setReturnDisposition(std::move(disposition));
		cf->returnDisposition = de.getReturnDisposition();
		cf->originalBodyCandidate.reset();
		if (revised && canProposeEmptyBody(*cf))
			cf->originalBodyCandidate = common::OriginalEmptyVoidBody{};
		else if (auto body = revised ? canProposeOrdinaryBody(*cf) : std::nullopt)
			cf->originalBodyCandidate = std::move(*body);
		else if (revised && stackWordBody)
			cf->originalBodyCandidate = *stackWordBody;
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
	if (cf && cf->originalBodyCandidate
		&& ((std::holds_alternative<common::OriginalEmptyVoidBody>(*cf->originalBodyCandidate) && canProposeEmptyBody(*cf))
			|| (std::holds_alternative<common::OriginalOrdinaryBody>(*cf->originalBodyCandidate) && canProposeOrdinaryBody(*cf))
			|| std::holds_alternative<common::OriginalEntryStackWordBody>(*cf->originalBodyCandidate))) return;
	if (!cf || !cf->returnDisposition || cf->returnDisposition->kind != Disposition::Kind::Value)
		throw OriginalContractRefusal("original-only selected return contract is unknown");
    if (p.getOriginalCallScope() && (!cf->originalCallSummary || !cf->originalCallSummary->declaration.isComplete()))
        throw OriginalContractRefusal("original-only selected declaration contract is unknown");
	for (const auto& call : cf->returnDisposition->evidence.calls)
		if (call.required && !call.qualified)
			throw OriginalContractRefusal("original-only required call contract is unknown");
}

void ParamReturn::projectConditionalStackWordBody(const common::OriginalEntryStackWordBody& body)
{
	auto& functions = _config->getConfig().functions;
	const auto original = functions;
	auto* selected = original.getFunctionByStartAddress(_config->getConfig().parameters.getEntryPoint());
	if (!selected || !selected->originalBodyCandidate
		|| !std::holds_alternative<common::OriginalEntryStackWordBody>(*selected->originalBodyCandidate)
		|| !selected->returnDisposition || !selected->originalCallSummary
		|| !stackWordResultSupported(*selected->returnDisposition, *selected->originalCallSummary))
		throw std::runtime_error("conditional-stack-word-proposal-scope-differs");
	auto* function = _module->getFunction(selected->getName());
	if (!function || function->isDeclaration() || function->arg_size() || function->isVarArg())
		throw std::runtime_error("conditional-stack-word-proposal-already-projected");
	auto* slot = _config->getLlvmStackVariable(function, 16);
	auto* v0 = _abi->getRegister(MIPS_REG_V0);
	if (!slot || !slot->getAllocatedType()->isIntegerTy(32) || !v0 || !v0->getValueType()->isIntegerTy(32))
		throw std::runtime_error("conditional-stack-word-carrier-unresolved");
	unsigned loads = 0;
	for (auto* user : slot->users()) {
		auto* load = dyn_cast<LoadInst>(user);
		if (!load || load->getPointerOperand() != slot || !load->getType()->isIntegerTy(32)
			|| load->isVolatile() || load->isAtomic() || AsmInstruction(load).getAddress() != body.pc)
			throw std::runtime_error("conditional-stack-word-slot-use-differs");
		++loads;
	}
	if (loads != 1) throw std::runtime_error("conditional-stack-word-slot-load-unresolved");
	std::vector<Value*> carriers;
	std::vector<Type*> types;
	std::vector<common::Storage> storages;
	for (unsigned reg = MIPS_REG_A0; reg <= MIPS_REG_A3; ++reg) {
		auto* value = _abi->getRegister(reg);
		auto* observed = value ? _config->getConfigRegister(value) : nullptr;
		if (!value || !value->getValueType()->isIntegerTy(32) || !observed
			|| !observed->getStorage().isRegister() || observed->getStorage().getRegisterNumber() != reg)
			throw std::runtime_error("conditional-stack-word-register-carrier-unresolved");
		carriers.push_back(value); types.push_back(value->getValueType()); storages.push_back(observed->getStorage());
	}
	carriers.push_back(slot); types.push_back(slot->getAllocatedType()); storages.push_back(common::Storage::onStack(16));
	std::vector<ReturnInst*> returns;
	const auto& exit = selected->returnDisposition->evidence.exits.front();
	for (auto& instruction : instructions(function)) if (auto* ret = dyn_cast<ReturnInst>(&instruction)) {
		auto address = AsmInstruction(ret).getAddress();
		if (!address.isDefined() || (address != exit.pc && address != exit.delaySlot))
			throw std::runtime_error("conditional-stack-word-return-owner-differs");
		returns.push_back(ret);
	}
	if (returns.size() != 1) throw std::runtime_error("conditional-stack-word-return-inventory-differs");
	try {
		std::map<ReturnInst*, Value*> values{{returns.front(), new LoadInst(v0, "", returns.front())}};
		IrModifier modifier(_module, _config);
		auto* projected = modifier.modifyFunction(function, v0->getValueType(), types, false,
			values, {}, v0, carriers, {}).first;
		auto* updated = _config->getConfigFunction(projected);
		if (!updated || updated->getName() != selected->getName() || updated->parameters.size() != storages.size())
			throw std::runtime_error("conditional-stack-word-projected-inventory-differs");
		auto parameters = updated->parameters;
		for (unsigned index = 0; index < parameters.size(); ++index) {
			if (parameters[index].type.getLlvmIr() != "i32")
				throw std::runtime_error("conditional-stack-word-projected-type-differs");
			parameters[index].setStorage(storages[index]);
		}
		functions = original;
		auto* restored = _config->getConfigFunction(projected);
		if (!restored) throw std::runtime_error("conditional-stack-word-restored-identity-differs");
		restored->parameters = std::move(parameters);
		restored->returnType.setLlvmIr("i32");
		restored->returnStorage = common::Storage::inRegister("v0", MIPS_REG_V0);
		_fnc2calls.clear();
	} catch (...) {
		functions = original;
		_fnc2calls.clear();
		throw;
	}
}

void ParamReturn::projectOriginalBody()
{
	auto& functions = _config->getConfig().functions;
	const auto original = functions;
	std::map<uint64_t, const common::Function*> identities;
	for (const auto& function : original)
		if (!function.getStart().isDefined() || !identities.emplace(function.getStart().getValue(), &function).second)
			throw std::runtime_error("original-body-proposal-function-identity-unresolved");
	auto* selected = original.getFunctionByStartAddress(_config->getConfig().parameters.getEntryPoint());
	if (!selected || !canProposeOrdinaryBody(*selected)) throw std::runtime_error("original-body-proposal-scope-differs");
	std::map<uint64_t, unsigned> arguments;
	std::map<uint64_t, uint64_t> targets;
	unsigned count = 0;
	const auto& evidence = selected->returnDisposition->evidence;
	const auto& instructions = evidence.instructions;
	for (unsigned i = 0; i < instructions.size(); ++i) {
		auto word = instructions[i].word;
		unsigned op = word >> 26, rt = (word >> 16) & 31;
		if ((op == 9 || op == 15 || op == 35 || op == 36) && rt >= 4 && rt <= 7) count = std::max(count, rt - 3);
		if (op == 3) {
			auto slot = instructions[i + 1].word;
			unsigned slotOp = slot >> 26, slotRt = (slot >> 16) & 31;
			if ((slotOp == 9 || slotOp == 15 || slotOp == 35 || slotOp == 36) && slotRt >= 4 && slotRt <= 7)
				count = std::max(count, slotRt - 3);
			arguments.emplace(instructions[i].pc, count);
			targets.emplace(instructions[i].pc, ((instructions[i].pc + 4) & 0xf0000000u) | ((word & 0x03ffffffu) << 2));
			count = 0; ++i;
		}
	}
	try {
		collectAllCalls(false);
		filterCalls();
		std::set<uint64_t> observed;
		for (const auto& entry : _fnc2calls)
			for (const auto& call : entry.second.callEntries()) {
				auto* instruction = call.getCallInstruction();
				if (_config->getFunctionAddress(instruction->getFunction()) != selected->getStart()) continue;
				auto address = AsmInstruction(instruction).getAddress();
				if (!address.isDefined()) throw std::runtime_error("original-body-proposal-call-owner-unresolved");
				auto pc = address.getValue();
				if (!arguments.count(pc)) {
					auto owner = std::find_if(evidence.edges.begin(), evidence.edges.end(), [&](const auto& edge) {
						return edge.to == pc && edge.from + 4 == pc && edge.kind == "delay-slot"
							&& edge.delayOwner == edge.from && arguments.count(edge.from);
					});
					if (owner != evidence.edges.end()) pc = owner->from;
				}
				auto* callee = instruction->getCalledFunction();
				if (!callee || !targets.count(pc) || _config->getFunctionAddress(callee) != targets.at(pc))
					throw std::runtime_error("original-body-proposal-call-target-differs");
				if (!arguments.count(pc)
					|| !observed.insert(pc).second || call.args().size() < arguments.at(pc)
					|| std::find(call.args().begin(), call.args().end(), nullptr) != call.args().end())
					throw std::runtime_error("original-body-proposal-call-arguments-unresolved");
			}
		if (observed.size() != arguments.size()) throw std::runtime_error("original-body-proposal-calls-unresolved");
		applyToIr();
		common::FunctionContainer restored;
		for (const auto& function : functions) {
			auto found = function.getStart().isDefined() ? identities.find(function.getStart().getValue()) : identities.end();
			if (found == identities.end() || function.getName() != found->second->getName()
				|| !restored.insert(*found->second).second)
				throw std::runtime_error("original-body-proposal-function-identity-differs");
		}
		if (restored.size() != original.size()) throw std::runtime_error("original-body-proposal-function-inventory-differs");
		functions = std::move(restored);
		_fnc2calls.clear();
	} catch (...) {
		functions = original;
		_fnc2calls.clear();
		throw;
	}
}

/**
 * Collect possible arguments' stores for all calls we want to analyze.
 * At the moment, we analyze only indirect or declared function calls with no
 * arguments inside one basic block.
 */
void ParamReturn::collectAllCalls(bool attachOriginalEvidence)
{
	_fnc2calls.clear();
	for (auto& f : _module->getFunctionList())
	{
		if (f.isIntrinsic())
		{
			continue;
		}

		_fnc2calls.emplace(std::make_pair(
					&f,
					createDataFlowEntry(&f, attachOriginalEvidence)));
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
					createDataFlowEntry(calledVal, attachOriginalEvidence))).first;
		}

		addDataFromCall(&fIt->second, call);
	}
}

DataFlowEntry ParamReturn::createDataFlowEntry(Value* calledValue, bool attachOriginalEvidence) const
{
	DataFlowEntry dataflow(calledValue);

	if (attachOriginalEvidence && _config->getConfig().parameters.isOriginalOnlyReturnRecovery())
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
	if (!attachOriginalEvidence && _config->getConfig().parameters.isOriginalOnlyReturnRecovery()) {
		bool decoded = false;
		auto* cf = _config->getConfigFunction(dataflow.getFunction());
		if (cf && cf->returnDisposition && cf->getStart().isDefined() && cf->getEnd().isDefined()) {
			const auto& evidence = cf->returnDisposition->evidence;
			decoded = !evidence.instructions.empty() && evidence.instructions.size() <= Disposition::RowLimit
				&& evidence.symbol == cf->getName() && evidence.start == cf->getStart().getValue()
				&& evidence.end == cf->getEnd().getValue() && evidence.end >= evidence.start
				&& evidence.end - evidence.start == 4 * evidence.instructions.size();
			for (unsigned i = 0; decoded && i < evidence.instructions.size(); ++i) {
				const auto& instruction = evidence.instructions[i];
				decoded = instruction.pc == evidence.start + 4 * i && instruction.owner == evidence.symbol
					&& instruction.bytes == 4 && instruction.mapped && !instruction.undef;
			}
		}
		dataflow.setIsFullyDecoded(decoded);
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
