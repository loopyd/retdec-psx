#ifndef RETDEC_BIN2LLVMIR_ORIGINAL_STORAGE_H
#define RETDEC_BIN2LLVMIR_ORIGINAL_STORAGE_H

#include <array>
#include <map>
#include <optional>
#include <set>
#include "retdec/common/function.h"

namespace retdec { namespace bin2llvmir {
using Disposition = common::ReturnDisposition;
struct RegisterState;
struct MipsOperation;
class OriginalMemoryState {
    struct Word {
        unsigned entry = 0;
        int32_t offset = 0;
        uint64_t store = 0;
        std::set<uint64_t> loads, calls;
        bool sameValue(const Word& other) const;
        bool operator==(const Word& other) const;
    };
    const common::OriginalEntryObservation* _observation = nullptr;
    bool _eligible = true;
    std::optional<uint32_t> _frame;
    std::array<std::optional<int32_t>, Disposition::RegisterCount> _offsets;
    std::map<uint32_t, Word> _words;
    std::array<std::optional<Word>, Disposition::RegisterCount> _relations;
    std::array<std::optional<Word>, Disposition::GprCount> _pending;
    std::array<bool, Disposition::GprCount> _hasPending{};
    std::optional<Word> _sampledLink;
    void invalidate();
    std::optional<uint32_t> physical(int32_t offset, unsigned bytes) const;
public:
    static OriginalMemoryState bind(const common::OriginalEntryObservation* observation,
        const std::string& function, const std::string& imageId, const std::string& imageHash,
        const Disposition::Evidence& evidence);
    bool join(const OriginalMemoryState& incoming);
    void step(const Disposition::Instruction& row, const MipsOperation& operation, const RegisterState& state);
    void call(uint64_t pc, const common::OriginalCallContract* contract);
    static void summarize(common::OriginalFunctionSummary& summary,
        const std::map<uint64_t, RegisterState>& exits);
};
struct RegisterFact {
	bool missing = true;
	std::set<unsigned> definitions, formals, entries;
	std::optional<unsigned> equalEntry;
	std::optional<uint32_t> constant;
	uint32_t possibleOneBits = UINT32_MAX;
	std::set<uint64_t> equalityEvidence;
	std::set<std::string> bad;
	uint32_t possibleOnes() const { return constant.value_or(possibleOneBits); }
	bool operator==(const RegisterFact& other) const {
		return missing == other.missing && definitions == other.definitions
			&& formals == other.formals && entries == other.entries && bad == other.bad
			&& equalEntry == other.equalEntry && constant == other.constant
			&& possibleOneBits == other.possibleOneBits
			&& equalityEvidence == other.equalityEvidence;
	}
};
struct RegisterState {
    std::array<RegisterFact, Disposition::RegisterCount> registers;
    std::array<RegisterFact, Disposition::GprCount> pending;
    std::array<bool, Disposition::GprCount> mayPending{}, mayNoPending{};
    std::set<uint64_t> conditionalTables;
    std::set<uint64_t> conditionalCallees;
    OriginalMemoryState storage;
    RegisterFact& operator[](unsigned reg) { return registers[reg]; }
    const RegisterFact& operator[](unsigned reg) const { return registers[reg]; }
};
class ScopedCallTransfer {
    const common::OriginalTransfer* _transfer;
    explicit ScopedCallTransfer(const common::OriginalTransfer& transfer) : _transfer(&transfer) {}
public:
    static std::optional<ScopedCallTransfer> bind(const Disposition::Call& call,
        const common::OriginalPartialCall& proof, const common::OriginalFunctionSummary& summary,
        const RegisterState& before);
    const common::OriginalTransfer& transfer() const { return *_transfer; }
};
struct MipsOperation {
	enum Kind { Compute, Multiply, Divide, Load, Store, Branch, Return, Call, Trap, Unsupported } kind = Unsupported;
	enum class MergeMemory { Lwl, Lwr, Swl, Swr };
	std::vector<unsigned> destinations;
	std::vector<unsigned> inputs;
	std::optional<uint64_t> target;
	std::optional<MergeMemory> merge;
	bool conditional = false;
	std::string name = "unsupported";
};
struct OriginalEntryOffset {
    unsigned entry;
    uint32_t offset = 0;
    std::set<uint64_t> evidence;
    bool adjusted = false;
};
struct OriginalIdentityFlow;
class OriginalFrameContract {
    const common::OriginalFunctionSummary* _summary;
    OriginalFrameContract(const common::OriginalFunctionSummary& summary)
        : _summary(&summary) {}
public:
    static std::optional<common::OriginalSymbolicFrame> recover(const OriginalIdentityFlow& flow,
        const Disposition::Evidence& evidence, const common::OriginalFunctionSummary& summary,
        const std::map<uint64_t, RegisterState>& exits, const std::map<uint64_t, RegisterFact>& sampled);
    static std::optional<OriginalFrameContract> bind(const Disposition::Call& call,
        const common::OriginalPartialCall& proof, const common::OriginalFunctionSummary& summary,
        const RegisterState& before);
    bool preserves(unsigned reg) const;
    const common::OriginalTransfer* assignedResult(const RegisterState& before) const;
};
struct OriginalIdentityFlow {
    uint64_t start;
    const std::string& symbol;
    const std::map<uint64_t, const Disposition::Instruction*>& instructions;
    const std::map<unsigned, Disposition::Definition>& definitions;
    const std::map<std::pair<uint64_t, uint64_t>, RegisterState>& states;
    const std::multimap<uint64_t, const Disposition::Edge*>& incoming;
    const std::map<uint64_t, Disposition::Call>& calls;
    MipsOperation (*operation)(const Disposition::Instruction&);
    const std::map<uint64_t, OriginalFrameContract>* frameUses = nullptr;
    const std::set<uint64_t>* firstUseCalls = nullptr;
};
class OriginalEntryAddressRegion {
public:
    static std::optional<common::OriginalEntryRelativeMemoryAddress> recover(
        const OriginalIdentityFlow& flow, const Disposition::Evidence& evidence,
        const common::OriginalMemoryAccess& access);
};
bool originalMemoryAccessMatches(const common::OriginalMemoryAccess& access,
    const Disposition::Instruction& instruction, const MipsOperation& operation);
std::optional<common::OriginalEntryRelativeMemoryAddress> originalFlowMemoryAddress(
    const common::OriginalMemoryAccess& access, const OriginalIdentityFlow& flow);
const RegisterState* originalIdentityState(const OriginalIdentityFlow& flow, uint64_t pc);
bool originalIdentityCall(const OriginalIdentityFlow& flow, uint64_t pc, unsigned reg);
bool originalIdentityWriter(const OriginalIdentityFlow& flow, uint64_t pc, unsigned reg,
    std::optional<uint64_t> expected, bool after = false);
std::optional<OriginalEntryOffset> originalEntryOffset(unsigned id, const OriginalIdentityFlow& flow);
bool joinFact(RegisterFact& fact, const RegisterFact& incoming);
bool joinState(RegisterState& destination, const RegisterState& incoming);
} }
#endif
