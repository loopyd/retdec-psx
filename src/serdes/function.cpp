/**
 * @file src/serdes/function.cpp
 * @brief Function (de)serialization.
 * @copyright (c) 2019 Avast Software, licensed under the MIT license
 */

#include <algorithm>
#include <stdexcept>
#include <rapidjson/prettywriter.h>
#include <rapidjson/stringbuffer.h>

#include "retdec/common/function.h"
#include "retdec/serdes/address.h"
#include "retdec/serdes/basic_block.h"
#include "retdec/serdes/calling_convention.h"
#include "retdec/serdes/function.h"
#include "retdec/serdes/object.h"
#include "retdec/serdes/storage.h"
#include "retdec/serdes/type.h"
#include "retdec/serdes/std.h"

#include "retdec/serdes/std.h"

namespace {

const std::string JSON_name          = "name";
const std::string JSON_realName      = "realName";
const std::string JSON_demangledName = "demangledName";
const std::string JSON_comment       = "comment";
const std::string JSON_decStr        = "declarationStr";
const std::string JSON_startAddr     = "startAddr";
const std::string JSON_endAddr       = "endAddr";
const std::string JSON_fncType       = "fncType";
const std::string JSON_cc            = "callingConvention";
const std::string JSON_returnStorage = "returnStorage";
const std::string JSON_fbStorage     = "frameBaseStorage";
const std::string JSON_returnType    = "returnType";
const std::string JSON_parameters    = "parameters";
const std::string JSON_locals        = "locals";
const std::string JSON_srcFileName   = "srcFileName";
const std::string JSON_startLine     = "startLine";
const std::string JSON_endLine       = "endLine";
const std::string JSON_fromDebug     = "isFromDebug";
const std::string JSON_wrappedName   = "wrappedFunctionName";
const std::string JSON_isConstructor = "isConstructor";
const std::string JSON_isDestructor  = "isDestructor";
const std::string JSON_isVirtual     = "isVirtual";
const std::string JSON_isExported    = "isExported";
const std::string JSON_isVariadic    = "isVariadic";
const std::string JSON_isThumb       = "isThumb";
const std::string JSON_usedCrypto    = "usedCryptoConstants";
const std::string JSON_basicBlocks   = "basicBlocks";

std::vector<std::string> fncTypes =
{
	"decompilerDefined",
	"userDefined",
	"staticallyLinked",
	"dynamicallyLinked",
	"syscall",
	"idiom"
};

using Disposition = retdec::common::ReturnDisposition;

template<typename Writer, typename T>
void numbers(Writer& writer, const char* key, const std::vector<T>& values)
{
	writer.Key(key); writer.StartArray();
	for (auto value : values) writer.Uint64(value);
	writer.EndArray();
}

template<typename Writer>
void strings(Writer& writer, const char* key, const std::vector<std::string>& values)
{
	writer.Key(key); writer.StartArray();
	for (const auto& value : values) writer.String(value);
	writer.EndArray();
}

template<typename Writer>
void fact(Writer& writer, const char* key, const retdec::common::OriginalFact& value)
{
    if ((value.kind == retdec::common::OriginalFact::Kind::Complete) != value.remaining.empty())
        throw std::runtime_error("invalid-original-fact-state");
    writer.Key(key); writer.StartObject(); writer.Key("kind");
    writer.String(value.kind == retdec::common::OriginalFact::Kind::Complete ? "complete"
        : value.kind == retdec::common::OriginalFact::Kind::Partial ? "partial" : "unknown");
    strings(writer, "remaining", value.remaining); writer.EndObject();
}

template<typename Writer, typename T>
void optional(Writer& writer, const char* key, const std::optional<T>& value)
{
    writer.Key(key); if (value) writer.Uint64(*value); else writer.Null();
}

template<typename Writer>
void transfer(Writer& writer, const retdec::common::OriginalTransfer& row)
{
    writer.StartObject(); writer.Key("register"); writer.Uint(row.reg);
    writer.Key("kind"); writer.String(row.kind); fact(writer, "proof", row.proof);
    numbers(writer, "definitions", row.definitions); numbers(writer, "entries", row.entries);
    strings(writer, "bad", row.bad); optional(writer, "equalEntry", row.equalEntry); optional(writer, "constant", row.constant);
    numbers(writer, "equalityEvidence", row.equalityEvidence);
    writer.Key("pending"); writer.Bool(row.pending); writer.Key("mayNoPending"); writer.Bool(row.mayNoPending);
    numbers(writer, "pendingDefinitions", row.pendingDefinitions); writer.EndObject();
}

template<typename Writer>
void transfers(Writer& writer, const char* key, const std::vector<retdec::common::OriginalTransfer>& rows)
{
    writer.Key(key); writer.StartArray(); for (const auto& row : rows) transfer(writer, row); writer.EndArray();
}

template<typename Writer>
void contract(Writer& writer, const retdec::common::OriginalCallContract& value)
{
    auto* partial = std::get_if<retdec::common::OriginalPartialCall>(&value);
    const auto& proof = partial ? *partial : std::get<retdec::common::OriginalCompleteCall>(value).proof();
    writer.Key("contract"); writer.StartObject(); writer.Key("kind"); writer.String(partial ? "partial" : "complete");
    writer.Key("callee"); writer.String(proof.callee); writer.Key("delay"); writer.Uint64(proof.delay);
    writer.Key("continuation"); writer.Uint64(proof.continuation); optional(writer, "actualIncomingLink", proof.actualIncomingLink);
    fact(writer, "identity", proof.identity); fact(writer, "inputs", proof.inputs); fact(writer, "transfers", proof.transfers);
    fact(writer, "result", proof.result); fact(writer, "control", proof.control); fact(writer, "effects", proof.effects);
    fact(writer, "noMemoryWrites", proof.noMemoryWrites);
    fact(writer, "declaration", proof.declaration); strings(writer, "remaining", proof.remaining);
    numbers(writer, "calleeExits", proof.calleeExits); transfers(writer, "registerTransfers", proof.registerTransfers);
    writer.Key("bindings"); writer.StartArray();
    for (const auto& row : proof.bindings) {
        writer.StartObject(); writer.Key("register"); writer.Uint(row.reg); writer.Key("missing"); writer.Bool(row.missing);
        numbers(writer, "definitions", row.definitions); numbers(writer, "entries", row.entries); numbers(writer, "uses", row.uses);
        strings(writer, "bad", row.bad); optional(writer, "equalEntry", row.equalEntry); optional(writer, "constant", row.constant);
        writer.EndObject();
    }
    writer.EndArray(); writer.EndObject();
}

template<typename Writer>
void memoryAddress(Writer& writer, const retdec::common::OriginalMemoryAccess& access)
{
    if (auto* partial = std::get_if<retdec::common::OriginalFact>(&access.address)) {
        if (partial->isComplete()) throw std::runtime_error("invalid-complete-memory-address-fact");
        fact(writer, "address", *partial); return;
    }
    if (const auto* address = std::get_if<retdec::common::OriginalEntryRelativeMemoryAddress>(&access.address)) {
        if (!address->entryRegister || address->entryRegister > 31)
            throw std::runtime_error("invalid-entry-relative-memory-register");
        bool firstUse = address->derivation == retdec::common::OriginalEntryRelativeMemoryAddress::Derivation::EntryFirstUse;
        if (firstUse != bool(address->firstUse)) throw std::runtime_error("invalid-first-use-memory-domain");
        if (firstUse) {
            const auto& domain = *address->firstUse;
            if (domain.entryPc > UINT32_MAX || domain.usePc > UINT32_MAX || domain.entryPc % 4
                || domain.usePc % 4 || domain.usePc != access.pc
                || domain.callPcs.size() > retdec::common::ReturnDisposition::ReferenceLimit
                || !std::is_sorted(domain.callPcs.begin(), domain.callPcs.end())
                || std::adjacent_find(domain.callPcs.begin(), domain.callPcs.end()) != domain.callPcs.end()
                || std::any_of(domain.callPcs.begin(), domain.callPcs.end(),
                    [](uint64_t pc) { return pc > UINT32_MAX - 8 || pc % 4; }))
                throw std::runtime_error("invalid-first-use-memory-domain");
        }
        writer.Key("address"); writer.StartObject(); writer.Key("kind");
        writer.String(firstUse ? "entry-register-relative-first-use/v1"
            : address->derivation == retdec::common::OriginalEntryRelativeMemoryAddress::Derivation::Flow
            ? "entry-register-relative-flow/v1" : "entry-register-relative-prefix/v1");
        writer.Key("entryRegister"); writer.Uint(address->entryRegister); writer.Key("offset"); writer.Uint(address->offset);
        numbers(writer, "equalityEvidence", address->equalityEvidence);
        if (firstUse) {
            writer.Key("entryPc"); writer.Uint64(address->firstUse->entryPc);
            writer.Key("usePc"); writer.Uint64(address->firstUse->usePc);
            writer.Key("operandPhase"); writer.String("before-instruction");
            numbers(writer, "callPcs", address->firstUse->callPcs);
            strings(writer, "conditions", std::vector<std::string>{"first-reach-from-original-entry-before-unproved-control-crossing"});
        }
        writer.EndObject(); return;
    }
    if (const auto* address = std::get_if<retdec::common::OriginalBoundedEntryMemoryAddress>(&access.address)) {
        if (address->entryRegister != 29 || address->indexLower > address->indexUpper
            || address->boundEvidence.empty() || address->boundEvidence.size() > retdec::common::ReturnDisposition::ReferenceLimit
            || !std::is_sorted(address->boundEvidence.begin(), address->boundEvidence.end())
            || std::adjacent_find(address->boundEvidence.begin(), address->boundEvidence.end()) != address->boundEvidence.end())
            throw std::runtime_error("invalid-bounded-entry-memory-address");
        writer.Key("address"); writer.StartObject(); writer.Key("kind"); writer.String("entry-register-bounded-flow/v1");
        writer.Key("entryRegister"); writer.Uint(address->entryRegister); writer.Key("offset"); writer.Uint(address->offset);
        writer.Key("indexLower"); writer.Uint(address->indexLower); writer.Key("indexUpper"); writer.Uint(address->indexUpper);
        numbers(writer, "boundEvidence", address->boundEvidence); writer.EndObject(); return;
    }
    const auto& address = std::get<retdec::common::OriginalFixedMemoryAddress>(access.address);
    writer.Key("address"); writer.StartObject(); writer.Key("kind");
    writer.String(address.derivation == retdec::common::OriginalFixedMemoryAddress::Derivation::Flow
        ? "instruction-fixed-flow/v1" : "entry-fallthrough-prefix/v1");
    writer.Key("base"); writer.Uint(address.base); writer.Key("value"); writer.Uint(address.value);
    numbers(writer, "equalityEvidence", address.equalityEvidence); fact(writer, "alignment", address.alignment);
    if (auto* partial = std::get_if<retdec::common::OriginalFact>(&address.fileBytes)) {
        if (partial->isComplete()) throw std::runtime_error("invalid-complete-file-bytes-fact");
        fact(writer, "fileBytes", *partial);
    } else {
        const auto& bytes = std::get<retdec::common::OriginalFileBytes>(address.fileBytes);
        writer.Key("fileBytes"); writer.StartObject(); writer.Key("kind"); writer.String("file-backed-initial-bytes");
        writer.Key("mappingStart"); writer.Uint(bytes.mappingStart); writer.Key("mappingBytes"); writer.Uint64(bytes.mappingBytes);
        writer.Key("payloadOffset"); writer.Uint64(bytes.payloadOffset); numbers(writer, "bytes", bytes.bytes); writer.EndObject();
    }
    writer.EndObject();
}

template<typename Writer>
void summary(Writer& writer, const retdec::common::OriginalFunctionSummary& value)
{
    writer.Key("originalCallSummary"); writer.StartObject(); writer.Key("function"); writer.String(value.function);
    writer.Key("pendingEntry"); writer.String(value.pendingEntry);
    fact(writer, "entry", value.entry); fact(writer, "result", value.result); fact(writer, "control", value.control);
    fact(writer, "effects", value.effects); fact(writer, "declaration", value.declaration);
    fact(writer, "noMemoryWrites", value.noMemoryWrites);
    if (value.entryContext) {
        const auto& context = *value.entryContext;
        writer.Key("entryContext"); writer.StartObject();
        writer.Key("kind"); writer.String("psx-observed-entry-context/v1");
        writer.Key("observation"); writer.String(context.observation);
        writer.Key("stateHash"); writer.String(context.stateHash);
        writer.Key("entryPc"); writer.Uint(context.entryPc);
        writer.Key("cpu"); writer.StartObject();
        writer.Key("inIsr"); writer.Bool(context.cpu.inIsr);
        writer.Key("status"); writer.Uint(context.cpu.status);
        writer.Key("cause"); writer.Uint(context.cpu.cause);
        writer.Key("epc"); writer.Uint(context.cpu.epc);
        writer.EndObject(); writer.EndObject();
    }
    if (value.scopedRestoration) {
        const auto& scoped = *value.scopedRestoration;
        writer.Key("scopedRestoration"); writer.StartObject();
        writer.Key("kind"); writer.String("mips-observed-frame-restoration/v1");
        writer.Key("observation"); writer.String(scoped.observation);
        writer.Key("stateHash"); writer.String(scoped.stateHash);
        writer.Key("entryPc"); writer.Uint(scoped.entryPc);
        writer.Key("entrySp"); writer.Uint(scoped.entrySp);
        writer.Key("frameBytes"); writer.Uint(scoped.frameBytes);
        strings(writer, "conditions", std::vector<std::string>{"captured-entry-sp-and-settled-load-state",
            "ordinary-ram-mapping-and-cache-mode-remain-active", "original-instructions-remain-active",
            "accesses-and-instruction-fetches-complete-normally",
            "no-asynchronous-or-external-state-interference", "mips-i-load-and-branch-delays"});
        writer.Key("registers"); writer.StartArray();
        for (const auto& restored : scoped.registers) {
            writer.StartObject(); writer.Key("register"); writer.Uint(restored.reg);
            writer.Key("entrySpOffset"); writer.Int(restored.offset);
            writer.Key("physicalWord"); writer.Uint(restored.physicalWord);
            writer.Key("storePc"); writer.Uint64(restored.storePc);
            numbers(writer, "loadPcs", restored.loadPcs); numbers(writer, "callPcs", restored.callPcs);
            numbers(writer, "exitPcs", restored.exitPcs); writer.EndObject();
        }
        writer.EndArray(); writer.EndObject();
    }
    if (value.symbolicFrame) {
        const auto& frame = *value.symbolicFrame;
        writer.Key("symbolicFrame"); writer.StartObject();
        writer.Key("kind"); writer.String("mips-symbolic-frame-restoration/v1");
        writer.Key("entryPc"); writer.Uint(frame.entryPc);
        writer.Key("frameBytes"); writer.Uint(frame.frameBytes);
        strings(writer, "conditions", std::vector<std::string>{"settled-entry-loads-and-mips-i-delays",
            "aligned-whole-frame-in-ordinary-ram", "frame-writes-disjoint-from-fetched-code",
            "ordinary-ram-mapping-and-cache-mode-remain-active", "original-instructions-and-call-bindings-remain-active",
            "accesses-and-instruction-fetches-complete-normally", "no-asynchronous-or-external-state-interference"});
        writer.Key("registers"); writer.StartArray();
        for (const auto& restored : frame.registers) {
            writer.StartObject(); writer.Key("register"); writer.Uint(restored.reg);
            writer.Key("entrySpOffset"); writer.Int(restored.offset);
            writer.Key("storePc"); writer.Uint64(restored.storePc);
            numbers(writer, "loadPcs", restored.loadPcs); numbers(writer, "callPcs", restored.callPcs);
            numbers(writer, "exitPcs", restored.exitPcs); writer.EndObject();
        }
        writer.EndArray(); writer.EndObject();
    }
    numbers(writer, "parameterRegisters", value.parameterRegisters);
    writer.Key("demands"); writer.StartArray();
    for (const auto& row : value.demands) {
        writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc); writer.Key("register"); writer.Uint(row.reg);
        writer.Key("role"); writer.String(row.role); writer.EndObject();
    }
    writer.EndArray(); transfers(writer, "transfers", value.transfers);
    writer.Key("exits"); writer.StartArray();
    for (const auto& row : value.exits) {
        writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc); writer.Key("delay"); writer.Uint64(row.delay);
        fact(writer, "incomingLink", row.incomingLink); optional(writer, "sampledEntry", row.sampledEntry);
        optional(writer, "sampledConstant", row.sampledConstant); numbers(writer, "sampledDefinitions", row.sampledDefinitions); numbers(writer, "equalityEvidence", row.equalityEvidence);
        transfers(writer, "transfers", row.transfers); writer.EndObject();
    }
    writer.EndArray(); writer.Key("accesses"); writer.StartArray();
    for (const auto& row : value.accesses) {
        writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc); writer.Key("kind"); writer.String(row.kind);
        writer.Key("extension"); writer.String(row.extension); writer.Key("width"); writer.Uint(row.width);
        writer.Key("delayed"); writer.Bool(row.delayed);
        numbers(writer, "addressDefinitions", row.addressDefinitions); numbers(writer, "addressEntries", row.addressEntries);
        numbers(writer, "valueDefinitions", row.valueDefinitions); numbers(writer, "valueEntries", row.valueEntries);
        fact(writer, "obligation", row.obligation); memoryAddress(writer, row);
        fact(writer, "objectExtent", row.objectExtent); fact(writer, "initializedObject", row.initializedObject);
        fact(writer, "zeroInitializedObject", row.zeroInitializedObject); fact(writer, "constQualification", row.constQualification);
        fact(writer, "volatileQualification", row.volatileQualification); fact(writer, "restrictQualification", row.restrictQualification);
        fact(writer, "currentContents", row.currentContents); fact(writer, "aliasEffects", row.aliasEffects);
        fact(writer, "placement", row.placement); writer.EndObject();
    }
    writer.EndArray(); writer.EndObject();
}

template<typename Writer>
void entryPath(Writer& writer, const Disposition::EntryPath& path)
{
    writer.Key("entryPath"); writer.StartObject(); writer.Key("kind"); writer.String("mips-bound-call-path/v1");
    writer.Key("callee"); writer.String(path.callee); writer.Key("contextHash"); writer.String(path.contextHash);
    writer.Key("bindings"); writer.StartArray();
    for (const auto& binding : path.bindings) {
        writer.StartObject(); writer.Key("register"); writer.Uint(binding.reg);
        writer.Key("constant"); writer.Uint(binding.constant); numbers(writer, "definitions", binding.definitions);
        numbers(writer, "equalityEvidence", binding.equalityEvidence); writer.EndObject();
    }
    writer.EndArray(); writer.Key("instructions"); writer.StartArray();
    for (const auto& row : path.instructions) {
        writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc); writer.Key("word"); writer.Uint(row.word); writer.EndObject();
    }
    writer.EndArray(); writer.Key("edges"); writer.StartArray();
    for (const auto& edge : path.edges) {
        writer.StartObject(); writer.Key("from"); writer.Uint64(edge.from); writer.Key("to"); writer.Uint64(edge.to);
        writer.Key("delayOwner"); if (edge.delayOwner) writer.Uint64(*edge.delayOwner); else writer.Null();
        writer.Key("kind"); writer.String(edge.kind); writer.EndObject();
    }
    writer.EndArray(); writer.Key("branches"); writer.StartArray();
    for (const auto& branch : path.branches) {
        writer.StartObject(); writer.Key("pc"); writer.Uint64(branch.pc); writer.Key("taken"); writer.Bool(branch.taken);
        writer.Key("operands"); writer.StartArray();
        for (const auto& operand : branch.operands) {
            writer.StartObject(); writer.Key("register"); writer.Uint(operand.reg);
            writer.Key("constant"); writer.Uint(operand.constant); writer.EndObject();
        }
        writer.EndArray(); writer.EndObject();
    }
    writer.EndArray(); writer.Key("terminalPc"); writer.Uint64(path.terminalPc);
    strings(writer, "remaining", std::vector<std::string>{"conditional-entry-state-unresolved", "declaration-unresolved",
        "normal-return-target-unresolved", "original-memory-effects-unresolved", "stack-alias-restoration-unresolved"});
    writer.EndObject();
}

template<typename Writer>
void disposition(Writer& writer, const Disposition& value)
{
	writer.Key("returnDisposition"); writer.StartObject();
	writer.Key("rule"); writer.String(value.contractGraph ? "mips-all-normal-exits/v2" : "mips-all-normal-exits/v1");
	writer.Key("mode"); writer.String("original-only-mips32");
	writer.Key("kind"); writer.String(value.kind == Disposition::Kind::Value ? "value" : "unknown");
	writer.Key("origin"); writer.String(value.kind == Disposition::Kind::Value ? "native-must-definition" : "none");
	writer.Key("evidence"); writer.StartObject();
	const auto& e = value.evidence;
	writer.Key("symbol"); writer.String(e.symbol);
	writer.Key("start"); writer.Uint64(e.start); writer.Key("end"); writer.Uint64(e.end);
	writer.Key("selection"); writer.String(e.selection);
	writer.Key("decodeComplete"); writer.Bool(e.decodeComplete);
	writer.Key("analysisComplete"); writer.Bool(e.analysisComplete);
	writer.Key("instructions"); writer.StartArray();
	for (const auto& row : e.instructions) {
		writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc);
		writer.Key("word"); writer.Uint(row.word); writer.Key("owner"); writer.String(row.owner); writer.Key("bytes"); writer.Uint(row.bytes);
		writer.Key("mapped"); writer.Bool(row.mapped); writer.Key("undef"); writer.Bool(row.undef);
		numbers(writer, "fullWidthRegisters", row.fullWidthRegisters); writer.EndObject();
	}
	writer.EndArray(); writer.Key("edges"); writer.StartArray();
	for (const auto& row : e.edges) {
		writer.StartObject(); writer.Key("from"); writer.Uint64(row.from); writer.Key("to"); writer.Uint64(row.to);
		writer.Key("delayOwner"); if (row.delayOwner) writer.Uint64(*row.delayOwner); else writer.Null();
		writer.Key("kind"); writer.String(row.kind); writer.EndObject();
	}
	writer.EndArray(); writer.Key("definitions"); writer.StartArray();
	for (const auto& row : e.definitions) {
		writer.StartObject(); writer.Key("id"); writer.Uint(row.id); writer.Key("pc"); writer.Uint64(row.pc);
		writer.Key("register"); writer.Uint(row.reg); writer.Key("width"); writer.Uint(row.width);
		writer.Key("operation"); writer.String(row.operation); writer.Key("delayed"); writer.Bool(row.delayed);
		numbers(writer, "inputs", row.inputs); numbers(writer, "formals", row.formals);
		strings(writer, "bad", row.bad);
        if (value.contractGraph) {
            numbers(writer, "entries", row.entries); optional(writer, "equalEntry", row.equalEntry);
            optional(writer, "constant", row.constant); numbers(writer, "equalityEvidence", row.equalityEvidence); writer.Key("origin"); writer.StartObject();
            writer.Key("kind"); writer.String(row.origin);
            if (row.origin == "call") {
                writer.Key("callee"); writer.String(row.callee); writer.Key("available"); writer.Uint64(row.available);
                writer.Key("delay"); writer.Uint64(row.delay); numbers(writer, "calleeDefinitions", row.calleeDefinitions);
                numbers(writer, "substitutedEntries", row.substitutedEntries);
            }
            writer.EndObject();
        }
        writer.EndObject();
	}
	writer.EndArray(); writer.Key("exits"); writer.StartArray();
	for (const auto& row : e.exits) {
		writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc); writer.Key("delaySlot"); writer.Uint64(row.delaySlot);
		writer.Key("missing"); writer.Bool(row.missing); numbers(writer, "definitions", row.definitions);
		numbers(writer, "formals", row.formals); numbers(writer, "pendingDefinitions", row.pendingDefinitions);
		strings(writer, "bad", row.bad); writer.EndObject();
	}
	writer.EndArray(); writer.Key("calls"); writer.StartArray();
	for (const auto& row : e.calls) {
		writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc); writer.Key("target");
		if (row.target) writer.Uint64(*row.target); else writer.Null();
		writer.Key("required"); writer.Bool(row.required); writer.Key("qualified"); writer.Bool(row.qualified);
		strings(writer, "unresolved", row.unresolved);
        if (value.contractGraph) {
            if (!row.contract) throw std::runtime_error("missing-original-call-contract");
            contract(writer, *row.contract);
        }
        if (row.entryPath) entryPath(writer, *row.entryPath);
        writer.EndObject();
	}
	writer.EndArray(); writer.Key("obligations"); writer.StartArray();
	for (const auto& row : e.obligations) {
		writer.StartObject(); writer.Key("pc"); writer.Uint64(row.pc);
		writer.Key("domain"); writer.String(row.domain); writer.Key("reason"); writer.String(row.reason); writer.EndObject();
	}
	writer.EndArray(); writer.EndObject(); writer.EndObject();
}

const rapidjson::Value& field(const rapidjson::Value& object, const char* key)
{
	if (!object.IsObject() || !object.HasMember(key)) throw std::runtime_error("invalid return evidence field");
	return object[key];
}

void shape(const rapidjson::Value& object, std::initializer_list<const char*> keys)
{
	if (!object.IsObject() || object.MemberCount() != keys.size()) throw std::runtime_error("invalid return evidence shape");
	for (auto key : keys) field(object, key);
}

uint64_t number(const rapidjson::Value& object, const char* key, uint64_t maximum = (uint64_t(1) << 32))
{
	const auto& value = field(object, key);
	if (!value.IsUint64() || value.GetUint64() > maximum) throw std::runtime_error("invalid return evidence number");
	return value.GetUint64();
}

bool boolean(const rapidjson::Value& object, const char* key)
{
	const auto& value = field(object, key);
	if (!value.IsBool()) throw std::runtime_error("invalid return evidence Boolean");
	return value.GetBool();
}

std::string text(const rapidjson::Value& object, const char* key)
{
	const auto& value = field(object, key);
	if (!value.IsString() || value.GetStringLength() > 4096) throw std::runtime_error("invalid return evidence text");
	return std::string(value.GetString(), value.GetStringLength());
}

const rapidjson::Value& array(const rapidjson::Value& object, const char* key)
{
	const auto& value = field(object, key);
	if (!value.IsArray() || value.Size() > Disposition::RowLimit) throw std::runtime_error("return evidence array exhausted");
	return value;
}

std::vector<unsigned> numbers(const rapidjson::Value& object, const char* key, unsigned maximum)
{
	std::vector<unsigned> result;
	for (const auto& value : array(object, key).GetArray()) {
		if (!value.IsUint() || value.GetUint() > maximum) throw std::runtime_error("invalid return evidence reference");
		result.push_back(value.GetUint());
	}
	return result;
}

std::vector<std::string> strings(const rapidjson::Value& object, const char* key)
{
	std::vector<std::string> result;
	for (const auto& value : array(object, key).GetArray()) {
		if (!value.IsString() || value.GetStringLength() > 128) throw std::runtime_error("invalid return evidence reason");
		result.emplace_back(value.GetString(), value.GetStringLength());
	}
	return result;
}

std::optional<uint64_t> optionalNumber(const rapidjson::Value& object, const char* key)
{
	return field(object, key).IsNull() ? std::nullopt : std::optional<uint64_t>(number(object, key));
}

Disposition disposition(const rapidjson::Value& value)
{
	shape(value, {"rule", "mode", "kind", "origin", "evidence"});
	Disposition result;
	auto kind = text(value, "kind");
	if (text(value, "rule") != "mips-all-normal-exits/v1" || text(value, "mode") != "original-only-mips32"
		|| (kind != "unknown" && kind != "value") || text(value, "origin") != (kind == "value" ? "native-must-definition" : "none"))
		throw std::runtime_error("invalid native return disposition");
	result.kind = kind == "value" ? Disposition::Kind::Value : Disposition::Kind::Unknown;
	const auto& e = field(value, "evidence");
	shape(e, {"symbol", "start", "end", "selection", "decodeComplete", "analysisComplete", "instructions", "edges", "definitions", "exits", "calls", "obligations"});
	auto& out = result.evidence;
	out.symbol = text(e, "symbol"); out.start = number(e, "start"); out.end = number(e, "end");
	out.selection = text(e, "selection"); out.decodeComplete = boolean(e, "decodeComplete"); out.analysisComplete = boolean(e, "analysisComplete");
	for (const auto& row : array(e, "instructions").GetArray()) {
		shape(row, {"pc", "word", "owner", "bytes", "mapped", "undef", "fullWidthRegisters"});
		out.instructions.push_back({number(row, "pc"), uint32_t(number(row, "word", 0xffffffff)), text(row, "owner"), unsigned(number(row, "bytes", 16)),
			boolean(row, "mapped"), boolean(row, "undef"), numbers(row, "fullWidthRegisters", Disposition::RegisterCount - 1)});
	}
	for (const auto& row : array(e, "edges").GetArray()) {
		shape(row, {"from", "to", "delayOwner", "kind"});
		out.edges.push_back({number(row, "from"), number(row, "to"), optionalNumber(row, "delayOwner"), text(row, "kind")});
	}
	for (const auto& row : array(e, "definitions").GetArray()) {
		shape(row, {"id", "pc", "register", "width", "operation", "delayed", "inputs", "formals", "bad"});
		Disposition::Definition def;
		def.id = number(row, "id", Disposition::RowLimit); def.pc = number(row, "pc");
		def.reg = number(row, "register", Disposition::RegisterCount - 1); def.width = number(row, "width", 32);
		def.operation = text(row, "operation"); def.delayed = boolean(row, "delayed");
		def.inputs = numbers(row, "inputs", Disposition::RowLimit); def.formals = numbers(row, "formals", 31); def.bad = strings(row, "bad");
		out.definitions.push_back(std::move(def));
	}
	for (const auto& row : array(e, "exits").GetArray()) {
		shape(row, {"pc", "delaySlot", "missing", "definitions", "formals", "pendingDefinitions", "bad"});
		Disposition::Exit exit;
		exit.pc = number(row, "pc"); exit.delaySlot = number(row, "delaySlot"); exit.missing = boolean(row, "missing");
		exit.definitions = numbers(row, "definitions", Disposition::RowLimit); exit.formals = numbers(row, "formals", 31);
		exit.pendingDefinitions = numbers(row, "pendingDefinitions", Disposition::RowLimit); exit.bad = strings(row, "bad");
		out.exits.push_back(std::move(exit));
	}
	for (const auto& row : array(e, "calls").GetArray()) {
		shape(row, {"pc", "target", "required", "qualified", "unresolved"});
		out.calls.push_back({number(row, "pc"), optionalNumber(row, "target"), boolean(row, "required"), boolean(row, "qualified"), strings(row, "unresolved")});
	}
	for (const auto& row : array(e, "obligations").GetArray()) {
		shape(row, {"pc", "domain", "reason"});
		out.obligations.push_back({number(row, "pc"), text(row, "domain"), text(row, "reason")});
	}
	return result;
}

} // anonymous namespace

namespace retdec {
namespace serdes {

template <typename Writer>
void serialize(Writer& writer, const common::Function& f)
{
	writer.StartObject();

	serializeString(writer, JSON_name, f.getName());
	serialize(writer, JSON_cc, f.callingConvention);
	serializeString(
			writer,
			JSON_fncType,
			fncTypes[static_cast<size_t>(f.getLinkType())]
	);

	serializeString(writer, JSON_realName, f.getRealName());
	serializeString(writer, JSON_demangledName, f.getDemangledName());
	serializeString(writer, JSON_comment, f.getComment());
	serializeString(writer, JSON_decStr, f.getDeclarationString());
	serializeString(writer, JSON_wrappedName, f.getWrappedFunctionName());
	serializeString(writer, JSON_srcFileName, f.getSourceFileName());
	serialize(writer, JSON_startAddr, f.getStart(), f.getStart().isDefined());
	serialize(writer, JSON_endAddr, f.getEnd(), f.getEnd().isDefined());
	serialize(writer, JSON_startLine, f.getStartLine(), f.getStartLine().isDefined());
	serialize(writer, JSON_endLine, f.getEndLine(), f.getEndLine().isDefined());

	serializeBool(writer, JSON_fromDebug, f.isFromDebug(), false);
	serializeBool(writer, JSON_isConstructor, f.isConstructor(), false);
	serializeBool(writer, JSON_isDestructor, f.isDestructor(), false);
	serializeBool(writer, JSON_isVirtual, f.isVirtual(), false);
	serializeBool(writer, JSON_isExported, f.isExported(), false);
	serializeBool(writer, JSON_isVariadic, f.isVariadic(), false);
	serializeBool(writer, JSON_isThumb, f.isThumb(), false);

    bool concreteReturn = !f.returnDisposition || f.returnDisposition->kind == common::ReturnDisposition::Kind::Value
        || (f.originalBodyCandidate
            && std::holds_alternative<common::OriginalEntryStackWordBody>(*f.originalBodyCandidate));
    if (f.returnDisposition) disposition(writer, *f.returnDisposition);
    if (f.originalCallSummary) summary(writer, *f.originalCallSummary);
	if (f.sharedOriginalAddressViews) {
		if (f.sharedOriginalAddressViews->empty() || f.sharedOriginalAddressViews->size() > common::ReturnDisposition::RowLimit)
			throw std::runtime_error("invalid-original-address-view-count");
		auto kind = f.sharedOriginalAddressViews->front().kind;
		writer.Key("originalAddressViews"); writer.StartArray();
		for (const auto& view : *f.sharedOriginalAddressViews) {
			if (view.kind != kind || (kind != common::OriginalAddressSpanView::Kind::Scalar
					&& kind != common::OriginalAddressSpanView::Kind::IndependentByteWrite)
					|| (kind == common::OriginalAddressSpanView::Kind::IndependentByteWrite
						&& (view.width != 8 || view.accessPcs.size() != 1))
					|| view.symbol.empty() || (view.width != 8 && view.width != 16 && view.width != 32)
					|| view.accessPcs.empty() || view.accessPcs.size() > common::ReturnDisposition::ReferenceLimit
					|| !std::is_sorted(view.accessPcs.begin(), view.accessPcs.end())
					|| std::adjacent_find(view.accessPcs.begin(), view.accessPcs.end()) != view.accessPcs.end())
				throw std::runtime_error("invalid-original-address-view");
			writer.StartObject(); writer.Key("kind");
			writer.String(kind == common::OriginalAddressSpanView::Kind::IndependentByteWrite
				? "conditional-byte-write-address-view/v1" : "conditional-scalar-address-view/v1");
			writer.Key("symbol"); writer.String(view.symbol); writer.Key("start"); writer.Uint(view.start);
			writer.Key("width"); writer.Uint(view.width); numbers(writer, "accessPcs", view.accessPcs);
			writer.EndObject();
		}
		writer.EndArray();
	}
	if (f.originalDiscovered) {
		const auto& node = *f.originalDiscovered;
		writer.Key("originalDiscovered"); writer.StartObject();
		writer.Key("kind"); writer.String("native-bounded-callee/v1");
		writer.Key("key"); writer.String(node.key); writer.Key("target"); writer.String(node.target);
		writer.Key("imageId"); writer.String(node.imageId); writer.Key("contextHash"); writer.String(node.contextHash);
		writer.Key("start"); writer.Uint64(node.start); writer.Key("end"); writer.Uint64(node.end);
		writer.Key("words"); writer.StartArray();
		for (const auto& word : node.words) {
			writer.StartObject(); writer.Key("pc"); writer.Uint64(word.first); writer.Key("word"); writer.Uint(word.second); writer.EndObject();
		}
		writer.EndArray(); strings(writer, "remaining", node.remaining); writer.EndObject();
	}
	if (!f.originalJumpTables.empty()) {
		writer.Key("originalJumpTables"); writer.StartArray();
		for (const auto& table : f.originalJumpTables) {
			writer.StartObject(); writer.Key("rule"); writer.String("mips-guarded-snapshot-jump-table/v1");
			writer.Key("jumpPc"); writer.Uint64(table.jumpPc); writer.Key("loadPc"); writer.Uint64(table.loadPc);
			writer.Key("comparePc"); writer.Uint64(table.comparePc); writer.Key("guardPc"); writer.Uint64(table.guardPc);
			writer.Key("defaultPc"); writer.Uint64(table.defaultPc); writer.Key("selectorRegister"); writer.Uint(table.selectorRegister);
			writer.Key("tableAddress"); writer.Uint(table.tableAddress);
			writer.Key("imageId"); writer.String(table.imageId); writer.Key("payloadHash"); writer.String(table.payloadHash);
			writer.Key("tableBytes"); writer.StartObject(); writer.Key("kind"); writer.String("file-backed-initial-bytes");
			writer.Key("mappingStart"); writer.Uint(table.tableBytes.mappingStart);
			writer.Key("mappingBytes"); writer.Uint64(table.tableBytes.mappingBytes);
			writer.Key("payloadOffset"); writer.Uint64(table.tableBytes.payloadOffset);
			numbers(writer, "bytes", table.tableBytes.bytes); writer.EndObject();
			numbers(writer, "indexedTargets", table.indexedTargets); numbers(writer, "instructionEvidence", table.instructionEvidence);
			fact(writer, "runtimeBinding", table.runtimeBinding); fact(writer, "currentContents", table.currentContents);
			strings(writer, "conditions", table.conditions); writer.EndObject();
		}
		writer.EndArray();
	}
	if (f.originalCalleeContexts) {
		const auto& contexts = *f.originalCalleeContexts;
		writer.Key("originalCalleeContexts"); writer.StartObject();
		writer.Key("rule"); writer.String("mips-same-image-leaf-context/v1");
		writer.Key("imageId"); writer.String(contexts.imageId);
		writer.Key("payloadHash"); writer.String(contexts.payloadHash);
		writer.Key("mappingStart"); writer.Uint(contexts.mappingStart);
		writer.Key("mappingBytes"); writer.Uint64(contexts.mappingBytes);
		strings(writer, "conditions", std::vector<std::string>{"this-image-supplies-executed-instructions",
			"no-pending-entry-gpr-loads", "instruction-fetches-and-loads-complete-normally", "mips-i-load-and-branch-delays"});
		strings(writer, "remaining", contexts.remaining);
		writer.Key("candidates"); writer.StartArray();
		for (const auto& context : contexts.candidates) {
			writer.StartObject(); writer.Key("entry"); writer.Uint(context.entry);
			numbers(writer, "callPcs", context.callPcs);
			writer.Key("localExploration"); writer.String(context.mayWriteGprs ? "closed-normal-paths" : "unresolved");
			optional(writer, "mayWriteGprs", context.mayWriteGprs);
			numbers(writer, "normalReturnPcs", context.normalReturnPcs);
			writer.Key("words"); writer.StartArray();
			for (const auto& word : context.words) {
				writer.StartObject(); writer.Key("pc"); writer.Uint(word.first);
				writer.Key("word"); writer.Uint(word.second); writer.EndObject();
			}
			writer.EndArray();
			strings(writer, "remaining", std::vector<std::string>{"candidate-extent-not-reviewed",
				"call-execution-and-residency-unresolved", "memory-effects-and-exceptions-unresolved",
				"result-and-pending-load-transfers-not-analyzed", "callee-declaration-unresolved"});
			writer.EndObject();
		}
		writer.EndArray(); writer.EndObject();
	}
	if (f.originalBodyCandidate) {
		writer.Key("originalBodyCandidate");
		if (std::holds_alternative<common::OriginalEmptyVoidBody>(*f.originalBodyCandidate))
			writer.String("mips-empty-body/v1");
		else if (std::holds_alternative<common::OriginalOrdinaryBody>(*f.originalBodyCandidate))
			writer.String("mips-ordinary-body/v1");
		else {
			const auto& body = std::get<common::OriginalEntryStackWordBody>(*f.originalBodyCandidate);
			writer.StartObject(); writer.Key("kind"); writer.String("mips-entry-stack-word-body/v1");
			writer.Key("input"); writer.StartObject();
			writer.Key("pc"); writer.Uint64(body.pc);
			writer.Key("definition"); writer.Uint(body.definition); writer.EndObject();
			writer.Key("condition"); writer.String("o32-entry-sp16-word-stable-until-load");
			writer.EndObject();
		}
	}
	if (!f.originalSourceExpressions.empty()) {
		writer.Key("originalSourceExpressions"); writer.StartArray();
		for (const auto& expression : f.originalSourceExpressions) {
			writer.StartObject(); writer.Key("relation"); writer.String("sign-extend-low-bits");
			writer.Key("machineWidth"); writer.Uint(32);
			writer.Key("viewWidth"); writer.Uint(expression.viewWidth);
			writer.Key("entryRegister"); writer.Uint(expression.entryRegister);
			numbers(writer, "pcs", std::vector<uint64_t>{expression.leftPc, expression.rightPc});
			numbers(writer, "definitions", std::vector<unsigned>{expression.leftDefinition, expression.rightDefinition});
			writer.EndObject();
		}
		writer.EndArray();
	}
	if (f.originalSourceForms) {
		bool unresolved = !f.originalSourceFormFailures.empty();
		for (const auto& application : *f.originalSourceForms)
			unresolved |= std::holds_alternative<common::SourceFormUnresolved>(application.outcome);
		writer.Key("originalSourceForms"); writer.StartObject();
		writer.Key("status"); writer.String(unresolved ? "unresolved"
			: f.originalSourceForms->empty() ? "no-bound-sites" : "census");
		writer.Key("remaining"); writer.StartArray();
		for (const auto& reason : f.originalSourceFormFailures) writer.String(reason);
		writer.EndArray();
		writer.Key("applications"); writer.StartArray();
		for (const auto& application : *f.originalSourceForms) {
			if (application.witnessIndex >= f.originalSourceExpressions.size())
				throw std::runtime_error("original-source-form-witness-index-unresolved");
			writer.StartObject(); writer.Key("witnessIndex"); writer.Uint(application.witnessIndex);
			if (auto ready = std::get_if<common::SourceFormReady>(&application.outcome)) {
				if (!ready->occurrences || ready->occurrences > common::ReturnDisposition::ReferenceLimit)
					throw std::runtime_error("original-source-form-occurrence-count-unresolved");
				writer.Key("status"); writer.String("ready");
				writer.Key("occurrences"); writer.Uint(ready->occurrences);
			} else {
				writer.Key("status"); writer.String("unresolved");
				writer.Key("reason"); writer.String(std::get<common::SourceFormUnresolved>(application.outcome).reason);
			}
			writer.EndObject();
		}
		writer.EndArray(); writer.EndObject();
	}
	serialize(writer, JSON_returnStorage, f.returnStorage, concreteReturn && f.returnStorage.isDefined());
	serialize(writer, JSON_fbStorage, f.frameBaseStorage, f.frameBaseStorage.isDefined());
	serialize(writer, JSON_returnType, f.returnType, concreteReturn && f.returnType.isDefined());

	serializeContainer(writer, JSON_locals, f.locals);
	serializeContainer(writer, JSON_parameters, f.parameters);
	serializeContainer(writer, JSON_basicBlocks, f.basicBlocks);
	serializeContainer(writer, JSON_usedCrypto, f.usedCryptoConstants);

	writer.EndObject();
}
SERIALIZE_EXPLICIT_INSTANTIATION(common::Function)

void deserialize(const rapidjson::Value& val, common::Function& f)
{
	f.sharedOriginalAddressViews.reset();
	if (val.IsObject() && val.HasMember("originalAddressViews"))
		throw std::runtime_error("original-address-views-is-invocation-output-only");
	if (val.IsNull() || !val.IsObject())
	{
		return;
	}

	f.setName( deserializeString(val, JSON_name) );
	f.setRealName( deserializeString(val, JSON_realName) );
	f.setDemangledName( deserializeString(val, JSON_demangledName) );
	f.setComment( deserializeString(val, JSON_comment) );
	f.setDeclarationString( deserializeString(val, JSON_decStr) );
	f.setWrappedFunctionName( deserializeString(val, JSON_wrappedName) );
	f.setSourceFileName( deserializeString(val, JSON_srcFileName) );
	f.setIsFromDebug( deserializeBool(val, JSON_fromDebug) );
	f.setIsConstructor( deserializeBool(val, JSON_isConstructor) );
	f.setIsDestructor( deserializeBool(val, JSON_isDestructor) );
	f.setIsVirtual( deserializeBool(val, JSON_isVirtual) );
	f.setIsExported( deserializeBool(val, JSON_isExported) );
	f.setIsVariadic( deserializeBool(val, JSON_isVariadic) );
	f.setIsThumb( deserializeBool(val, JSON_isThumb) );

	common::Address s;
	deserialize(val, JSON_startAddr, s);
	f.setStart(s);

	common::Address e;
	deserialize(val, JSON_endAddr, e);
	f.setEnd(e);

	common::Address sl;
	deserialize(val, JSON_startLine, sl);
	f.setStartLine(sl);

	common::Address el;
	deserialize(val, JSON_endLine, el);
	f.setEndLine(el);

	deserialize(val, JSON_cc, f.callingConvention);
	deserialize(val, JSON_returnStorage, f.returnStorage);
	deserialize(val, JSON_fbStorage, f.frameBaseStorage);
	deserialize(val, JSON_returnType, f.returnType);
    f.originalCallSummary.reset();
    if (val.HasMember("originalCallSummary")) throw std::runtime_error("original-call-summary-is-invocation-output-only");
	f.originalCalleeContexts.reset();
	f.originalDiscovered.reset();
	if (val.HasMember("originalDiscovered")) throw std::runtime_error("original-discovered-function-is-invocation-output-only");
	if (val.HasMember("originalCalleeContexts")) throw std::runtime_error("original-callee-context-is-invocation-output-only");
	f.originalJumpTables.clear();
	if (val.HasMember("originalJumpTables")) throw std::runtime_error("original-jump-tables-is-invocation-output-only");
	f.originalBodyCandidate.reset();
	if (val.HasMember("originalBodyCandidate")) throw std::runtime_error("original-body-candidate-is-invocation-output-only");
	f.originalSourceExpressions.clear();
	f.originalSourceForms.reset();
	f.originalSourceFormFailures.clear();
	if (val.HasMember("originalSourceForms")) throw std::runtime_error("original-source-forms-is-invocation-output-only");
	if (val.HasMember("originalSourceExpressions")) throw std::runtime_error("original-source-expressions-is-invocation-output-only");
    f.returnDisposition.reset();
    auto nativeReturn = val.FindMember("returnDisposition");
    if (nativeReturn != val.MemberEnd()) {
        f.returnDisposition = disposition(nativeReturn->value);
        if (f.returnDisposition->kind == common::ReturnDisposition::Kind::Unknown) {
            if (val.HasMember(JSON_returnType) || val.HasMember(JSON_returnStorage))
                throw std::runtime_error("unknown native return has concrete fields");
            f.returnType.setLlvmIr(""); f.returnStorage = common::Storage::undefined();
        }
    }

	deserializeContainer(val, JSON_locals, f.locals);
	deserializeContainer(val, JSON_parameters, f.parameters);
	deserializeContainer(val, JSON_usedCrypto, f.usedCryptoConstants);
	deserializeContainer(val, JSON_basicBlocks, f.basicBlocks);

	std::string enumStr = deserializeString(val, JSON_fncType);
	auto it = std::find(fncTypes.begin(), fncTypes.end(), enumStr);
	if (it != fncTypes.end())
	{
		f.setLinkType(static_cast<common::Function::eLinkType>(
				std::distance(fncTypes.begin(), it)));
	}
}

} // namespace serdes
} // namespace retdec
