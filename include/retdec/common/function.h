/**
 * @file include/retdec/common/function.h
 * @brief Common function representation.
 * @copyright (c) 2019 Avast Software, licensed under the MIT license
 */

#ifndef RETDEC_COMMON_FUNCTION_H
#define RETDEC_COMMON_FUNCTION_H

#include <cstdint>
#include <optional>
#include <map>
#include <utility>
#include <variant>
#include <stdexcept>
#include <vector>
#include <set>
#include <string>

#include "retdec/common/calling_convention.h"
#include "retdec/common/basic_block.h"
#include "retdec/common/object.h"
#include "retdec/common/storage.h"
#include "retdec/common/type.h"

namespace retdec {
namespace bin2llvmir { class ParamReturn; }
namespace common {

using LineNumber = retdec::common::Address;

struct ReviewedOriginalFunction {
	std::string key, target, imageId, rangeHash;
	uint64_t start = 0, end = 0;
};
struct OriginalCallScope {
	std::string requestHash, configurationHash, payloadHash, problemHash;
	ReviewedOriginalFunction root;
	std::vector<ReviewedOriginalFunction> callees;
};
struct OriginalFact {
	enum class Kind { Unknown, Partial, Complete };
	Kind kind = Kind::Unknown;
	std::vector<std::string> remaining{"not-analyzed"};
	static OriginalFact complete() { return {Kind::Complete, {}}; }
	static OriginalFact partial(const std::string& reason) {
		if (reason.empty()) throw std::runtime_error("empty-original-proof-reason");
		return {Kind::Partial, {reason}};
	}
	bool isComplete() const { return kind == Kind::Complete && remaining.empty(); }
};
struct OriginalEntryUse {
	uint64_t pc = 0;
	unsigned reg = 0;
	std::string role;
};
struct OriginalTransfer {
	unsigned reg = 0;
	std::string kind = "unknown";
	OriginalFact proof;
	std::vector<unsigned> definitions, entries;
	std::vector<std::string> bad;
	std::optional<unsigned> equalEntry;
	std::optional<uint32_t> constant;
	std::vector<uint64_t> equalityEvidence;
	bool pending = false, mayNoPending = true;
	std::vector<unsigned> pendingDefinitions;
};
struct OriginalNormalExit {
	uint64_t pc = 0, delay = 0;
	OriginalFact incomingLink;
	std::optional<unsigned> sampledEntry;
	std::optional<uint32_t> sampledConstant;
	std::vector<unsigned> sampledDefinitions;
	std::vector<uint64_t> equalityEvidence;
	std::vector<OriginalTransfer> transfers;
};
struct OriginalMemoryAccess {
	uint64_t pc = 0;
	std::string kind, extension;
	unsigned width = 0;
	bool delayed = false;
	std::vector<unsigned> addressDefinitions, addressEntries, valueDefinitions, valueEntries;
	OriginalFact obligation = OriginalFact::partial("contents-object-address-alias-effect-placement-unresolved");
};
struct OriginalFunctionSummary {
	std::string function;
	OriginalFact entry, result, control, effects, declaration;
	std::vector<OriginalEntryUse> demands;
	std::vector<OriginalTransfer> transfers;
	std::vector<OriginalNormalExit> exits;
	std::vector<OriginalMemoryAccess> accesses;
	std::vector<unsigned> parameterRegisters;
	std::string pendingEntry = "requires-no-pending-gpr-loads";
};
struct OriginalInputBinding {
	unsigned reg = 0;
	bool missing = true;
	std::vector<unsigned> definitions, entries;
	std::vector<uint64_t> uses;
	std::vector<std::string> bad;
	std::optional<unsigned> equalEntry;
	std::optional<uint32_t> constant;
};
struct OriginalPartialCall {
	std::string callee;
	uint64_t delay = 0, continuation = 0;
	OriginalFact identity, inputs, transfers, result, control, effects, declaration;
	std::vector<OriginalInputBinding> bindings;
	std::vector<uint64_t> calleeExits;
	std::optional<uint32_t> actualIncomingLink;
	std::vector<OriginalTransfer> registerTransfers;
	std::vector<std::string> remaining{"callee-not-analyzed"};
};
class OriginalCompleteCall {
	OriginalPartialCall _proof;
	explicit OriginalCompleteCall(OriginalPartialCall proof) : _proof(std::move(proof)) {
		if (!_proof.identity.isComplete() || !_proof.inputs.isComplete()
			|| !_proof.transfers.isComplete() || !_proof.result.isComplete()
			|| !_proof.control.isComplete() || !_proof.effects.isComplete()
			|| !_proof.declaration.isComplete() || _proof.calleeExits.empty()
			|| !_proof.remaining.empty() || _proof.registerTransfers.size() != 34
			|| !_proof.actualIncomingLink || *_proof.actualIncomingLink != _proof.continuation) throw std::runtime_error("incomplete-original-call");
	}
	friend class retdec::bin2llvmir::ParamReturn;
public:
	const OriginalPartialCall& proof() const { return _proof; }
};
using OriginalCallContract = std::variant<OriginalPartialCall, OriginalCompleteCall>;

struct ReturnDisposition
{
	enum class Kind { Unknown, Value };
	enum : unsigned {
		GprCount = 32,
		HiRegister = 32,
		LoRegister = 33,
		RegisterCount = 34
	};
	struct Instruction {
		uint64_t pc = 0;
		uint32_t word = 0;
		std::string owner;
		unsigned bytes = 0;
		bool mapped = false;
		bool undef = false;
		std::vector<unsigned> fullWidthRegisters;
	};
	struct Edge {
		uint64_t from = 0, to = 0;
		std::optional<uint64_t> delayOwner;
		std::string kind;
	};
	struct Definition {
		unsigned id = 0, reg = 0, width = 0;
		uint64_t pc = 0;
		std::string operation;
		bool delayed = false;
		std::vector<unsigned> inputs, formals, entries;
		std::vector<std::string> bad;
		std::string origin = "instruction", callee;
		uint64_t available = 0, delay = 0;
		std::vector<unsigned> calleeDefinitions, substitutedEntries;
		std::optional<unsigned> equalEntry;
		std::optional<uint32_t> constant;
		std::vector<uint64_t> equalityEvidence;
	};
	struct Exit {
		uint64_t pc = 0, delaySlot = 0;
		bool missing = true;
		std::vector<unsigned> definitions, formals, pendingDefinitions;
		std::vector<std::string> bad;
	};
	struct Call {
		uint64_t pc = 0;
		std::optional<uint64_t> target;
		bool required = true, qualified = false;
		std::vector<std::string> unresolved;
		std::optional<OriginalCallContract> contract;
	};
	struct Obligation {
		uint64_t pc = 0;
		std::string domain, reason;
	};
	struct Evidence {
		std::string symbol;
		uint64_t start = 0, end = 0;
		std::string selection = "diagnostic";
		bool decodeComplete = false, analysisComplete = false;
		std::vector<Instruction> instructions;
		std::vector<Edge> edges;
		std::vector<Definition> definitions;
		std::vector<Exit> exits;
		std::vector<Call> calls;
		std::vector<Obligation> obligations;
	};
	static constexpr std::size_t RowLimit = 4096;
	static constexpr std::size_t ReferenceLimit = 8192;
	Kind kind = Kind::Unknown;
	bool contractGraph = false;
	Evidence evidence;
};

struct OriginalSourceExpression {
	uint64_t leftPc = 0, rightPc = 0;
	unsigned leftDefinition = 0, rightDefinition = 0;
	unsigned entryRegister = 0, viewWidth = 0;
};

/**
 * Represents function.
 *
 * Function's name is its unique ID. Function names in config must be the
 * same as in LLVM IR. Function names in IR must be unique, therefore
 * it is safe to demand unique names in config without loss of generality.
 *
 * Function address is not suitable unique ID. LLVM IR do not know
 * about functions' addresses. Some functions (syscalls) do not have
 * meaningful addresses.
 */
class Function : public retdec::common::AddressRange
{
	public:
		/**
		 * Recognized types of a function that will determine
		 * how the decompiler will treat the specified function.
		 *
		 * When the type is DECOMPILER_DEFINED the decompiler is
		 * allowed to prefer info recieved from some heuristics,
		 * instead of info specified in the config.
		 *
		 * When the type is USER_DEFINED the info about the function
		 * (params, type) specified in a config file will be projected
		 * on the decompiler output and the decompiler should not do
		 * any heuristcs.
		 */
		enum eLinkType
		{
			DECOMPILER_DEFINED = 0,
			USER_DEFINED,
			STATICALLY_LINKED,
			DYNAMICALLY_LINKED,
			SYSCALL,
			IDIOM
		};

	public:
		Function(const std::string& name = std::string());
		Function(
			retdec::common::Address start,
			retdec::common::Address end,
			const std::string& name = std::string());

		/// @name Function query methods.
		/// @{
		bool isDecompilerDefined() const;
		bool isUserDefined() const;
		bool isStaticallyLinked() const;
		bool isDynamicallyLinked() const;
		bool isSyscall() const;
		bool isIdiom() const;
		bool isFromDebug() const;
		bool isWrapper() const;
		bool isConstructor() const;
		bool isDestructor() const;
		bool isVirtual() const;
		bool isExported() const;
		bool isVariadic() const;
		bool isThumb() const;
		/// @}

		/// @name Function set methods.
		/// @{
		void setName(const std::string& n);
		void setRealName(const std::string& n);
		void setDemangledName(const std::string& n);
		void setComment(const std::string& c);
		void addComment(const std::string& c);
		void setDeclarationString(const std::string& s);
		void setSourceFileName(const std::string& n);
		void setWrappedFunctionName(const std::string& n);
		void setStartLine(const retdec::common::Address& l);
		void setEndLine(const retdec::common::Address& l);
		void setIsDecompilerDefined();
		void setIsUserDefined();
		void setIsStaticallyLinked() const;
		void setIsDynamicallyLinked() const;
		void setIsSyscall();
		void setIsIdiom();
		void setIsFromDebug(bool d);
		void setIsConstructor(bool f);
		void setIsDestructor(bool f);
		void setIsVirtual(bool f);
		void setIsExported(bool f);
		void setIsVariadic(bool f);
		void setIsThumb(bool f);
		void setLinkType(eLinkType lt);
		/// @}

		/// @name Function get methods.
		/// @{
		const std::string& getId() const;
		const std::string& getName() const;
		const std::string& getRealName() const;
		std::string getDemangledName() const;
		std::string getComment() const;
		std::string getDeclarationString() const;
		std::string getSourceFileName() const;
		std::string getWrappedFunctionName() const;
		LineNumber getStartLine() const;
		LineNumber getEndLine() const;
		eLinkType getLinkType() const;
		/// @}

		bool operator<(const Function& o) const;
		bool operator==(const Function& o) const;
		bool operator!=(const Function& o) const;

	public:
		common::CallingConvention callingConvention;
		common::Storage returnStorage;
		common::Storage frameBaseStorage;
		common::Type returnType;
		std::optional<ReturnDisposition> returnDisposition;
		std::optional<OriginalFunctionSummary> originalCallSummary;
		std::vector<OriginalSourceExpression> originalSourceExpressions;
		common::ObjectSequentialContainer parameters;
		common::ObjectSetContainer locals;
		std::set<std::string> usedCryptoConstants;
		std::set<common::BasicBlock> basicBlocks;
		/// Addresses of instructions which reference (use) this  function.
		std::set<common::Address> codeReferences;

	private:
		std::string _name; ///< This is objects unique ID.
		std::string _realName;
		std::string _demangledName;
		std::string _comment;
		std::string _declarationString;
		std::string _sourceFileName;
		std::string _wrapperdFunctionName;
		mutable eLinkType _linkType = DECOMPILER_DEFINED;
		LineNumber _startLine;
		LineNumber _endLine;
		bool _fromDebug = false;
		bool _constructor = false;
		bool _destructor = false;
		bool _virtualFunction = false;
		bool _exported = false;
		bool _variadic = false;
		bool _thumb = false;
};

struct FunctionNameCompare
{
	using is_transparent = void;

	bool operator()(const Function& f1, const Function& f2) const
	{
		return f1 < f2;
	}
	bool operator()(const std::string& id, Function const& f) const
	{
		return id < f.getName();
	}
	bool operator()(const Function& f, const std::string& id) const
	{
		return f.getName() < id;
	}
};

struct FunctionAddressCompare
{
	using is_transparent = void;

	bool operator()(const Function& f1, const Function& f2) const
	{
		return f1.getStart() < f2.getStart();
	}
	bool operator()(const retdec::common::Address& id, Function const& f) const
	{
		return id < f.getStart();
	}
	bool operator()(const Function& f, const retdec::common::Address& id) const
	{
		return f.getStart() < id;
	}
};

/**
 * An associative container with functions' names as the key.
 * See Function class for details.
 */
class FunctionContainer : public std::set<Function, FunctionNameCompare>
{
	public:
		bool hasFunction(const std::string& name);
		const Function* getFunctionByName(const std::string& name) const;
		const Function* getFunctionByStartAddress(
				const retdec::common::Address& addr) const;
		const Function* getFunctionByRealName(const std::string& name) const;
};

// TODO:
// Maybe we could use common::RangeContainer for this.
// It contains this functionality, but also some other mechanisms with
// potentially unwanted side effects.
// Also, because it does not take range as template argument, it is not ready
// to be used with common::Function.
class FunctionSet : public std::set<
		retdec::common::Function,
		retdec::common::FunctionAddressCompare>
{
	public:
		const retdec::common::Function* getRange(
				const retdec::common::Address& a) const;
};

} // namespace common
} // namespace retdec

#endif
