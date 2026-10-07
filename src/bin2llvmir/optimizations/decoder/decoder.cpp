/**
* @file src/bin2llvmir/optimizations/decoder/decoder.cpp
* @brief Decode input binary into LLVM IR.
* @copyright (c) 2017 Avast Software, licensed under the MIT license
*/

#include <llvm/IR/Dominators.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/IR/ValueHandle.h>
#include <stdexcept>
#include "mips_call_effects.h"

#include "retdec/fileformat/file_format/elf/elf_format.h"

#include "retdec/utils/conversion.h"
#include "retdec/utils/string.h"
#include "retdec/utils/io/log.h"
#include "retdec/bin2llvmir/optimizations/decoder/decoder.h"
#include "retdec/bin2llvmir/utils/llvm.h"
#include "retdec/bin2llvmir/utils/capstone.h"

using namespace retdec::capstone2llvmir;
using namespace retdec::common;
using namespace retdec::bin2llvmir::st_match;
using namespace retdec::fileformat;
using namespace retdec::utils::io;

namespace retdec {
namespace bin2llvmir {

// MIPS I has a one-instruction GPR load delay. Keep the loaded value's
// store in place, but make reads in the following instruction observe the
// pre-load value. A following write then naturally cancels the pending load.
// Run before pseudo-call/CFG rewrites, while instruction ownership is intact.
static void preserveMipsOneLoadDelay(llvm::Module* module, FileImage* image,
		Abi* abi, bool originalOnlyReturnRecovery)
{
	auto* elf = dynamic_cast<ElfFormat*>(image->getFileFormat());
	// ELF EF_MIPS_ARCH == 0 identifies MIPS I, not interlocked MIPS32.
	if (!originalOnlyReturnRecovery && (!elf
			|| elf->getTargetArchitecture() != retdec::fileformat::Architecture::MIPS
			|| (elf->getFileFlags() & 0xf0000000) != 0))
		return;

	struct DelayedRead {
		llvm::StoreInst* write;
		std::vector<llvm::LoadInst*> reads;
	};
	std::vector<DelayedRead> pending;
	for (auto& entry : AsmInstruction::getLlvmToCapstoneInsnMap(module))
	{
		auto* insn = entry.second;
		switch (insn->id)
		{
			case MIPS_INS_LB: case MIPS_INS_LBU:
			case MIPS_INS_LH: case MIPS_INS_LHU: case MIPS_INS_LW:
			case MIPS_INS_LWL: case MIPS_INS_LWR:
				break;
			default: continue;
		}
		AsmInstruction current(entry.first);
		llvm::StoreInst* write = nullptr;
		for (auto& ir : current)
			if (auto* store = llvm::dyn_cast<llvm::StoreInst>(&ir))
				if (abi->isRegister(store->getPointerOperand())) write = store;
		if (!write) continue;

		AsmInstruction next(module, current.getEndAddress());
		if (!next || next.getBasicBlock() != current.getBasicBlock()) {
			auto* word = image->getConstantInt(llvm::Type::getInt32Ty(module->getContext()), current.getAddress());
			auto* following = image->getConstantInt(llvm::Type::getInt32Ty(module->getContext()), current.getEndAddress());
			auto* previous = image->getConstantInt(llvm::Type::getInt32Ty(module->getContext()), current.getAddress() - 4);
			bool inDelaySlot = true;
			if (previous) {
				uint32_t bits = previous->getZExtValue();
				unsigned op = bits >> 26, fn = bits & 63;
				inDelaySlot = (op >= 1 && op <= 7) || (op == 0 && (fn == 8 || fn == 9))
						|| (op >= 16 && op <= 19);
			}
			if (word && following && !inDelaySlot) {
				unsigned destination = (word->getZExtValue() >> 16) & 31;
				uint32_t bits = following->getZExtValue();
				unsigned op = bits >> 26, rs = (bits >> 21) & 31, rt = (bits >> 16) & 31;
				bool independent = bits == 0;
				if (next) {
					if (op == 2 || op == 3 || op == 15) independent = true;
					if ((op >= 8 && op <= 14) || (op == 32 || op == 33 || op == 35 || op == 36 || op == 37))
						independent = rs != destination;
					if (op == 4 || op == 5 || op == 40 || op == 41 || op == 43)
						independent = rs != destination && rt != destination;
					if (op == 0) {
						unsigned fn = bits & 63;
						if (fn == 0 || fn == 2 || fn == 3) independent = rt != destination;
						if (fn == 8 || fn == 9) independent = rs != destination;
						if (fn == 4 || fn == 6 || fn == 7 || (fn >= 32 && fn <= 39) || fn == 42 || fn == 43)
							independent = rs != destination && rt != destination;
					}
				}
				if (independent) continue;
			}
		}
		if (!next || next.getBasicBlock() != current.getBasicBlock())
			throw std::runtime_error("MIPS I load delay crosses an unsupported decode boundary at "
					+ current.getAddress().toHexString());
		DelayedRead item{write, {}};
		for (auto& ir : next)
			if (auto* load = llvm::dyn_cast<llvm::LoadInst>(&ir))
				if (load->getPointerOperand() == write->getPointerOperand()
						&& !load->getMetadata("retdec.mips.merge"))
					item.reads.push_back(load);
		pending.push_back(item);
	}
	for (auto& item : pending)
	{
		if (item.reads.empty()) continue;
		llvm::IRBuilder<> irb(item.write);
		auto* old = irb.CreateLoad(item.write->getPointerOperand(), "load_delay_old");
		for (auto* read : item.reads)
		{
			read->replaceAllUsesWith(old);
			read->eraseFromParent();
		}
	}
}

static void markMipsBreakDelaySlot(llvm::Instruction* instruction,
		llvm::Value* branchTaken = nullptr)
{
	AsmInstruction slot(instruction);
	for (auto& ir : slot)
	{
		auto* call = llvm::dyn_cast<llvm::CallInst>(&ir);
		if (!call || !call->getCalledFunction()
				|| call->getCalledFunction()->getName() != "__retdec_mips_break")
			continue;
		llvm::IRBuilder<> irb(call);
		auto* type = call->getArgOperand(1)->getType();
		// The pinned Redux interpreter marks only taken branches as BD.
		call->setArgOperand(1, branchTaken ? irb.CreateZExtOrTrunc(branchTaken, type)
				: llvm::ConstantInt::get(type, 1));
	}
}

char Decoder::ID = 0;

static llvm::RegisterPass<Decoder> X(
		"retdec-decoder",
		"Input binary to LLVM IR decoding",
		false, // Only looks at CFG
		false // Analysis Pass
);

Decoder::Decoder() :
		ModulePass(ID)
{

}

Decoder::~Decoder()
{
	if (_dryCsInsn)
	{
		cs_free(_dryCsInsn, 1);
	}
}

bool Decoder::runOnModule(llvm::Module& m)
{
	_module = &m;
	_config = ConfigProvider::getConfig(_module);
	_image = FileImageProvider::getFileImage(_module);
	_debug = DebugFormatProvider::getDebugFormat(_module);
	_names = NamesProvider::getNames(_module);
	_abi = AbiProvider::getAbi(_module);
	_llvm2capstone = &AsmInstruction::getLlvmToCapstoneInsnMap(_module);
	return runCatcher();
}

bool Decoder::runOnModuleCustom(
		llvm::Module& m,
		Config* c,
		FileImage* o,
		DebugFormat* d,
		NameContainer* n,
		Abi* a)
{
	_module = &m;
	_config = c;
	_image = o;
	_debug = d;
	_names = n;
	_abi = a;
	_llvm2capstone = &AsmInstruction::getLlvmToCapstoneInsnMap(_module);
	return runCatcher();
}

bool Decoder::runCatcher()
{
	if (_config && _config->getConfig().parameters.isOriginalOnlyReturnRecovery())
	{
		try { return run(); }
		catch (const std::exception&) {
			publishOriginalDecodeCoverage("decoder-failure");
			throw;
		}
		catch (...) {
			publishOriginalDecodeCoverage("decoder-failure");
			throw;
		}
	}
	// TODO: here, we shoudl catch only the most severe capstone2llvmir
	// problems which prevents us from using it.
	// Other problems (e.g. throws in instruction translating like unxpected
	// number of operands) should get their own special exception types
	// and should be catched lower and possibly ignored.
	//
	try
	{
		return run();
	}
	catch (const BaseError& e)
	{
		Log::error() << "[capstone2llvmir]: " << e.what() << std::endl;
		exit(1);
	}
}

bool Decoder::run()
{
	if (_config == nullptr || _image == nullptr)
	{
		LOG << "[ABORT] Config or object image is not available.\n";
		return false;
	}

	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
		validateOriginalOnlyProfile();
	initTranslator();
	initDryRunCsInstruction();
	initEnvironment();
	initRanges();
	initJumpTargets();

	LOG << _ranges << std::endl;
	LOG << _jumpTargets << std::endl;

	decode();
	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
		publishOriginalDecodeCoverage();
	if (_config->getConfig().architecture.isMipsOrPic32())
		preserveMipsOneLoadDelay(_module, _image, _abi,
			_config->getConfig().parameters.isOriginalOnlyReturnRecovery());

	if (debug_enabled && fs::exists(_config->getOutputDirectory()))
	{
		dumpModuleToFile(_module, _config->getOutputDirectory());
	}

	resolvePseudoCalls();
	patternsRecognize();
	finalizePseudoCalls();

	if (debug_enabled && fs::exists(_config->getOutputDirectory()))
	{
		dumpControFlowToJson(_module, _config->getOutputDirectory());
		dumpModuleToFile(_module, _config->getOutputDirectory());
	}

	initConfigFunctions();
	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
		publishOriginalDecodeCoverage();
	if (_config->getConfig().architecture.isMipsOrPic32()) {
		annotateMipsLeafCalls(_module, _image);
		simplifyMipsGuards(_module, _abi);
	}

	if (debug_enabled && fs::exists(_config->getOutputDirectory()))
	{
		dumpModuleToFile(_module, _config->getOutputDirectory());
	}

	initializeGpReg_mips();

	return false;
}

void Decoder::validateOriginalOnlyProfile() const
{
	const auto& c = _config->getConfig();
	const auto& p = c.parameters;
	auto refuse = [](bool condition) {
		if (!condition) throw std::runtime_error("original-only native profile rejected");
	};
	refuse(c.architecture.isMips() && c.architecture.getBitSize() == 32
		&& c.architecture.isEndianLittle() && c.fileFormat.isRaw32());
	refuse(!p.getInputFile().empty() && p.getSectionVMA().isDefined()
		&& p.getEntryPoint().isDefined() && p.getMainAddress().isUndefined());
	refuse(p.isSelectedDecodeOnly() && p.isKeepAllFunctions()
		&& !p.isDetectStaticCode() && p.selectedRanges.size() == 1
		&& p.selectedFunctions.empty() && p.selectedNotFoundFunctions.empty());
	refuse(c.functions.empty() && c.globals.empty() && c.structures.empty()
		&& c.registers.empty() && c.vtables.empty() && c.classes.empty()
		&& c.patterns.empty());
	refuse(p.getInputPdbFile().empty() && p.getOrdinalNumbersDirectory().empty()
		&& p.staticSignaturePaths.empty() && p.userStaticSignaturePaths.empty()
		&& p.libraryTypeInfoPaths.empty() && p.cryptoPatternPaths.empty()
		&& p.abiPaths.empty());
	const auto& range = *p.selectedRanges.begin();
	refuse(range.getStart().isDefined() && range.getEnd().isDefined());
	auto start = range.getStart().getValue(), end = range.getEnd().getValue();
	refuse(start == p.getEntryPoint().getValue() && start < end
		&& start % 4 == 0 && end % 4 == 0 && end <= (uint64_t(1) << 32));
	auto* format = _image->getFileFormat();
	refuse(format && format->isRawData() && format->getBytesPerWord() == 4
		&& format->isLittleEndian());
	auto bytes = _image->getImage()->getRawSegmentData(start);
	refuse(bytes.first && end - start <= bytes.second);
	const auto& passes = p.llvmPasses;
	auto decoder = std::find(passes.begin(), passes.end(), "retdec-decoder");
	auto param = std::find(passes.begin(), passes.end(), "retdec-param-return");
	auto output = std::find(passes.begin(), passes.end(), "retdec-llvmir2hll");
	refuse(std::count(passes.begin(), passes.end(), "retdec-decoder") == 1
		&& std::count(passes.begin(), passes.end(), "retdec-param-return") == 1
		&& output != passes.end() && decoder < param && param < output);
	refuse(!_debug || (!_debug->hasInformation() && _debug->functions.empty()
		&& _debug->globals.empty() && _debug->types.empty()));
}

void Decoder::captureOriginalInstruction(
	const capstone2llvmir::Capstone2LlvmIrTranslator::TranslationResultOne& result,
	llvm::Instruction* continuation)
{
	auto pc = result.capstoneInsn->address;
	auto extent = _originalExtents.upper_bound(pc);
	if (extent == _originalExtents.begin() || pc >= std::prev(extent)->second)
		throw std::runtime_error("original-instruction-outside-activated-scope");
	--extent;
	auto& disposition = _originalDispositions[extent->first];
	disposition.contractGraph = bool(_config->getConfig().parameters.getOriginalCallScope());
	auto& evidence = disposition.evidence;
	if (getFunctionAtAddress(Address(extent->first)) != result.llvmInsn->getFunction())
		evidence.obligations.push_back({pc, "architectural", "original-function-owner-mismatch"});
	if (evidence.instructions.size() == common::ReturnDisposition::RowLimit)
	{
		if (evidence.obligations.empty())
			evidence.obligations.push_back({result.capstoneInsn->address,
				"architectural", "decode-evidence-exhausted"});
		return;
	}
	common::ReturnDisposition::Instruction row;
	auto* instruction = result.capstoneInsn;
	row.pc = instruction->address;
	row.owner = result.llvmInsn->getFunction() ? result.llvmInsn->getFunction()->getName().str() : "";
	row.bytes = instruction->size;
	row.mapped = row.bytes == 4 && result.llvmInsn->getFunction() != nullptr;
	if (row.bytes == 4)
		for (unsigned i = 0; i < 4; ++i)
			row.word |= uint32_t(instruction->bytes[i]) << (i * 8);
	bool reachedContinuation = false;
	if (continuation && result.llvmInsn->getParent() == continuation->getParent()) {
		for (auto* ir = result.llvmInsn->getNextNode(); ir; ir = ir->getNextNode()) {
			if (ir == continuation) {
				reachedContinuation = true;
				break;
			}
			if (AsmInstruction::isLlvmToAsmInstruction(ir)) break;
			for (const auto& operand : ir->operands())
				row.undef |= llvm::isa<llvm::UndefValue>(operand.get());
			if (auto* store = llvm::dyn_cast<llvm::StoreInst>(ir)) {
				auto id = _abi->getRegisterId(store->getPointerOperand());
				if (store->getValueOperand()->getType()->isIntegerTy(32)) {
					if (MIPS_REG_0 <= id && id <= MIPS_REG_31)
						row.fullWidthRegisters.push_back(id - MIPS_REG_0);
					else if (id == MIPS_REG_HI)
						row.fullWidthRegisters.push_back(common::ReturnDisposition::HiRegister);
					else if (id == MIPS_REG_LO)
						row.fullWidthRegisters.push_back(common::ReturnDisposition::LoRegister);
				}
			}
		}
	}
	if (!reachedContinuation) {
		row.mapped = false;
		row.fullWidthRegisters.clear();
		if (evidence.obligations.size() < common::ReturnDisposition::RowLimit)
			evidence.obligations.push_back({row.pc, "architectural", "unsupported-translation-span"});
	}
	std::sort(row.fullWidthRegisters.begin(), row.fullWidthRegisters.end());
	row.fullWidthRegisters.erase(std::unique(row.fullWidthRegisters.begin(),
		row.fullWidthRegisters.end()), row.fullWidthRegisters.end());
	evidence.instructions.push_back(std::move(row));
}

void Decoder::admitOriginalDirectTarget(uint64_t callPc, uint64_t target)
{
	const auto& scope = _config->getConfig().parameters.getOriginalCallScope();
	if (!scope) return;
	for (const auto& f : scope->callees) {
		if (f.start != target) continue;
		if (_originalExtents.emplace(f.start, f.end).second) {
			_ranges.addPrimary(Address(f.start), Address(f.end));
			createFunction(Address(f.start));
		}
		return;
	}
}

void Decoder::publishOriginalDecodeCoverage(const std::string& failure)
{
	auto& c = _config->getConfig();
	for (const auto& extent : _originalExtents) {
		auto& disposition = _originalDispositions[extent.first];
		disposition.contractGraph = bool(c.parameters.getOriginalCallScope());
		auto& evidence = disposition.evidence;
		evidence.start = extent.first; evidence.end = extent.second;
		evidence.selection = extent.first == c.parameters.getEntryPoint().getValue() ? "selected-root" : "analysis-callee";
		auto* f = getFunctionAtAddress(Address(extent.first));
		auto* cf = _config->getConfigFunction(Address(extent.first));
		if (!cf) {
			common::Function record(Address(extent.first), Address(extent.second),
				f ? f->getName().str() : "undecoded_" + Address(extent.first).toHexString());
			cf = const_cast<common::Function*>(&*c.functions.insert(record).first);
		}
		evidence.symbol = cf->getName();
		for (const auto& row : evidence.instructions)
			if (row.owner != evidence.symbol && evidence.obligations.size() < common::ReturnDisposition::RowLimit)
				evidence.obligations.push_back({row.pc, "architectural", "original-function-owner-mismatch"});
		if (!failure.empty()) evidence.obligations.push_back({evidence.start, "architectural", failure});
		cf->returnDisposition = disposition;
		cf->returnType.setLlvmIr(""); cf->returnStorage = common::Storage::undefined();
	}
}

void Decoder::decode()
{
	LOG << "\n" << "decode():" << std::endl;

	JumpTarget jt;
	while (getJumpTarget(jt))
	{
		LOG << "\t" << "processing : " << jt << std::endl;
		decodeJumpTarget(jt);
	}

	if (!_somethingDecoded)
	{
		throw std::runtime_error("No instructions were decoded");
	}
}

bool Decoder::getJumpTarget(JumpTarget& jt)
{
	if (!_jumpTargets.empty())
	{
		jt = _jumpTargets.top();
		_jumpTargets.pop();
		return true;
	}
	else if (!_ranges.primaryEmpty())
	{
		jt = JumpTarget(
				_ranges.primaryFront().getStart(),
				JumpTarget::eType::LEFTOVER,
				_c2l->getBasicMode(),
				Address());
		return true;
	}
	return false;
}

void Decoder::decodeJumpTarget(const JumpTarget& jt)
{
	const Address start = jt.getAddress();
	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery() && start.isDefined()) {
		auto extent = _originalExtents.upper_bound(start.getValue());
		if (extent == _originalExtents.begin() || start.getValue() >= std::prev(extent)->second) return;
		--extent;
		if (jt.getFromAddress().isDefined() && jt.getType() != JumpTarget::eType::CONTROL_FLOW_CALL_TARGET
			&& (jt.getFromAddress().getValue() < extent->first || jt.getFromAddress().getValue() >= extent->second)) {
			_originalDispositions[extent->first].evidence.obligations.push_back({start.getValue(), "architectural", "cross-function-decode-edge"});
			return;
		}
	}
	if (start.isUndefined())
	{
		LOG << "\t\t" << "unknown target address -> skip" << std::endl;
		return;
	}
	
	if (jt.getFromAddress().isUndefined() && jt.getType() == JumpTarget::eType::IMPORT)
	{
		LOG << "\t\t" << "target address in data section -> skip" << std::endl;
		return;
	}

	bool alternative = false;
	auto* range = _ranges.getPrimary(start);
	if (range == nullptr && jt.getType() < JumpTarget::eType::LEFTOVER)
	{
		range = _ranges.getAlternative(start);
		alternative = true;
	}
	if (range == nullptr)
	{
		LOG << "\t\t" << "found no range -> skip" << std::endl;
		// TODO: arm-pe-ff7e029f2539e37ee590a3cb029762b6
		_ranges.remove(start, start + 1);
		return;
	}
	LOG << "\t\t" << "found range = " << *range << std::endl;

	ByteData bytes = _image->getImage()->getRawSegmentData(start);
	if (bytes.first == nullptr)
	{
		LOG << "\t\t" << "found no data -> skip" << std::endl;
		_ranges.remove(start, start + 1);
		return;
	}

	auto toRangeEnd = range->getEnd() - start;

	bytes.second = toRangeEnd < bytes.second ? toRangeEnd : bytes.second;

	if (jt.hasSize() && jt.getSize() < bytes.second)
	{
		bytes.second = jt.getSize().value();
	}
	if (auto nextBbAddr = getBasicBlockAddressAfter(start))
	{
		auto sz = nextBbAddr - start;
		bytes.second = sz < bytes.second ? sz : bytes.second;
	}
	else if (auto nextFncAddr = getFunctionAddressAfter(start))
	{
		auto sz = nextFncAddr - start;
		bytes.second = sz < bytes.second ? sz : bytes.second;
	}

	bool useAlt = alternative
			&& jt.getType() > JumpTarget::eType::CONTROL_FLOW_RETURN_TARGET
			&& jt.getType() != JumpTarget::eType::ENTRY_POINT;
	bool useStrict = _ranges.isStrict() && !useAlt;

	if (jt.getType() == JumpTarget::eType::LEFTOVER
			|| useAlt)
	{
		if (auto skipSz = decodeJumpTargetDryRun(jt, bytes, useStrict))
		{
			AddressRange sr(start, start+skipSz);
			LOG << "\t\t" << "dry run failed -> skip range = " << sr
					<< std::endl;
			_ranges.remove(sr);
			return;
		}
	}

	llvm::BasicBlock* bb = getBasicBlockAtAddress(start);
	if (bb == nullptr)
	{
		if (jt.getType() != JumpTarget::eType::LEFTOVER)
		{
			LOG << "\t\t" << "found no bb for jt -> skip" << std::endl;
			return;
		}

		llvm::BasicBlock* tBb = nullptr;
		llvm::Function* tFnc = nullptr;
		getOrCreateCallTarget(start, tFnc, tBb);
		if (tFnc && !tFnc->empty())
		{
			bb = &tFnc->front();
		}
		// Function can not be split, use BB. This BB does not have predecessor,
		// which is not ideal, but it might happen.
		//
		else if (tBb)
		{
			bb = tBb;
		}
		else
		{
			return;
		}
	}
	assert(bb && bb->getTerminator());
	llvm::IRBuilder<> irb(bb->getTerminator());
	_irb = &irb;

	if (_c2l->getBasicMode() != jt.getMode())
	{
		_c2l->modifyBasicMode(jt.getMode());
		LOG << "\t\t" << "switch mode -> "
				<< (jt.getMode() == CS_MODE_THUMB ? " (thumb)" : "(arm)")
				<< std::endl;
	}

	Address addr = start;
	bool bbEnd = false;
	do
	{
		LOG << "\t\t\t" << "translating = " << addr << std::endl;

		Address oldAddr = addr;

		auto res = translate(bytes, addr, irb);

		if (res.failed() || res.llvmInsn == nullptr)
		{
			if (auto* bb = getBasicBlockAtAddress(addr))
			{
				if (bb->getParent() == irb.GetInsertBlock()->getParent()
						&& bb != irb.GetInsertBlock())
				{
					auto* br = irb.CreateBr(bb);
					assert(br->getNextNode() == br->getParent()->getTerminator());
					br->getNextNode()->eraseFromParent();
					LOG << "\t\t" << "translation ended -> reached BB @ "
							<< addr << std::endl;
				}
			}
			else
			{
				LOG << "\t\t" << "translation failed" << std::endl;
			}
			break;
		}
		_somethingDecoded = true;

		_llvm2capstone->emplace(res.llvmInsn, res.capstoneInsn);

		bbEnd |= getJumpTargetsFromInstruction(oldAddr, res, bytes.second);
		bbEnd |= instructionBreaksBasicBlock(oldAddr, res);

		handleDelaySlotTypical(addr, res, bytes, irb);
		handleDelaySlotLikely(addr, res, bytes, irb);
	}
	while (!bbEnd);

	auto end = addr > start ? addr : Address(start+1);
	_ranges.remove(start, end);
	LOG << "\t\tdecoded range = " << AddressRange(start, end) << std::endl;
}

capstone2llvmir::Capstone2LlvmIrTranslator::TranslationResultOne
Decoder::translate(ByteData& bytes, common::Address& addr, llvm::IRBuilder<>& irb)
{
	llvm::WeakVH continuation, insertionBlock;
	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery()
		&& irb.GetInsertBlock() && irb.GetInsertPoint() != irb.GetInsertBlock()->end())
	{
		continuation = &*irb.GetInsertPoint();
		insertionBlock = irb.GetInsertBlock();
	}
	auto res = _c2l->translateOne(bytes.first, bytes.second, addr, irb);

	// MIPS 64-bit mode can decompile more instructions than the 32-bit mode.
	// When 32-bit mode is used, some 32-bit instructions that IDA handles fail
	// to disassemble.
	// But we cannot always use 64-bit mode, because some other (FPU)
	// instructions are disassembled differently. Try to swtich modes only if
	// translations fails.
	//
	if (_config->getConfig().architecture.isMipsOrPic32()
			&& (_c2l->getBasicMode() & CS_MODE_MIPS32)
			&& res.failed()
			&& !_config->getConfig().parameters.isOriginalOnlyReturnRecovery())
	{
		_c2l->modifyBasicMode(CS_MODE_MIPS64);
		res = _c2l->translateOne(bytes.first, bytes.second, addr, irb);
		_c2l->modifyBasicMode(CS_MODE_MIPS32);
	}

	if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery()
			&& !res.failed() && res.llvmInsn)
	{
		auto* boundary = llvm::dyn_cast_or_null<llvm::Instruction>(continuation);
		auto* block = llvm::dyn_cast_or_null<llvm::BasicBlock>(insertionBlock);
		captureOriginalInstruction(res,
			boundary && block && boundary->getParent() == block
				&& res.llvmInsn->getParent() == block ? boundary : nullptr);
	}
	return res;
}

/**
 * Check if the given jump targets and bytes can/should be decoded.
 * \return The number of bytes to skip from decoding. If zero, then dry run was
 *         ok and decoding of this chunk can proceed. If non-zero, remove the
 *         number of bytes from ranges to decode.
 */
std::size_t Decoder::decodeJumpTargetDryRun(
		const JumpTarget& jt,
		ByteData bytes,
		bool strict)
{
	// Architecture-specific dry runs.
	//
	if (_config->getConfig().architecture.isX86())
	{
		return decodeJumpTargetDryRun_x86(jt, bytes, strict);
	}
	else if (_config->getConfig().architecture.isArm32OrThumb())
	{
		return decodeJumpTargetDryRun_arm(jt, bytes, strict);
	}
	else if (_config->getConfig().architecture.isArm64())
	{
		return decodeJumpTargetDryRun_arm64(jt, bytes, strict);
	}
	else if (_config->getConfig().architecture.isMipsOrPic32())
	{
		return decodeJumpTargetDryRun_mips(jt, bytes, strict);
	}
	else if (_config->getConfig().architecture.isPpc())
	{
		return decodeJumpTargetDryRun_ppc(jt, bytes, strict);
	}
	else
	{
		assert(false);
	}

	// Common dry run.
	//
	return false;
}

cs_mode Decoder::determineMode(cs_insn* insn, common::Address& target)
{
	if (_config->getConfig().architecture.isArm32OrThumb())
	{
		return determineMode_arm(insn, target);
	}
	else
	{
		return _c2l->getBasicMode();
	}
}

bool Decoder::instructionBreaksBasicBlock(
		common::Address addr,
		capstone2llvmir::Capstone2LlvmIrTranslator::TranslationResultOne& tr)
{
	// On x86 halt may get generated to end the entry point function:
	// https://stackoverflow.com/questions/5213466/why-does-gcc-place-a-halt-instruction-in-programs-after-the-call-to-main
	// The check could be stricter - nop follows, all paths to halt, etc.
	//
	if (_config->getConfig().architecture.isX86()
			&& tr.llvmInsn->getFunction() == _entryPointFunction
			&& tr.capstoneInsn->id == X86_INS_HLT)
	{
		auto* ui = new llvm::UnreachableInst(_module->getContext());
		ReplaceInstWithInst(&*_irb->GetInsertPoint(), ui);
		_irb->SetInsertPoint(ui);
		return true;
	}
	// x86 terminating syscall pattern:
	//    mov eax, 1
	//    int 0x80
	//
	// TODO: other terminating syscalls.
	else if (_config->getConfig().architecture.isX86()
			&& tr.capstoneInsn->id == X86_INS_INT
			&& tr.capstoneInsn->detail->x86.op_count == 1
			&& tr.capstoneInsn->detail->x86.operands[0].type == X86_OP_IMM
			&& tr.capstoneInsn->detail->x86.operands[0].imm == 0x80)
	{
		AsmInstruction ai(tr.llvmInsn);
		auto prev = ai.getPrev();
		if (prev.isValid())
		{
			auto& detail = prev.getCapstoneInsn()->detail->x86;
			if (prev.getCapstoneInsn()->id == X86_INS_MOV
					&& detail.op_count == 2
					&& detail.operands[0].type == X86_OP_REG
					&& detail.operands[0].reg == X86_REG_EAX
					&& detail.operands[1].type == X86_OP_IMM
					&& detail.operands[1].imm == 1)
			{
				auto* ui = new llvm::UnreachableInst(_module->getContext());
				ReplaceInstWithInst(&*_irb->GetInsertPoint(), ui);
				_irb->SetInsertPoint(ui);
				return true;
			}
		}
	}

	return false;
}

/**
 * @return @c True if this instruction ends basic block, @c false otherwise.
 */
bool Decoder::getJumpTargetsFromInstruction(
		common::Address addr,
		capstone2llvmir::Capstone2LlvmIrTranslator::TranslationResultOne& tr,
		std::size_t& rangeSize)
{
	llvm::CallInst*& pCall = tr.branchCall;
	auto nextAddr = addr + tr.size;

	if (_config->getConfig().architecture.isArm32OrThumb())
	{
		AsmInstruction ai(tr.llvmInsn);
		patternsPseudoCall_arm(pCall, ai);
	}

	llvm::BasicBlock* tBb = nullptr;
	llvm::Function* tFnc = nullptr;

	_switchGenerated = false;

	// Function call -> insert target (if computed).
	//
	if (_c2l->isCallFunctionCall(pCall))
	{
		auto t = getJumpTarget(addr, pCall, pCall->getArgOperand(0));
		// TOOD: sometimes we want to enable calls (and other branches) to zero.

		if (t || (t == 0 && AsmInstruction(_module, 0)))
		{
			// TODO: found in x86 macho:
			//__text:00001EE6    sub     esp, 1Ch
			//__text:00001EE9    call    $+5         (target = 0x1EEE)
			//__text:00001EEE    pop     ecx
			if (t == nextAddr)
			{
				return false;
			}
			//.text:08001EE1    call    near ptr loc_8001EE1+1
			//.text:08001EE6    cmp     ebx, esi
			if (addr < t && t < nextAddr)
			{
				return false;
			}

			if (_config->getConfig().parameters.isOriginalOnlyReturnRecovery()
				&& tr.capstoneInsn->size == 4 && (tr.capstoneInsn->bytes[3] >> 2) == 3)
				admitOriginalDirectTarget(addr.getValue(), t.getValue());
			auto m = determineMode(tr.capstoneInsn, t);
			getOrCreateCallTarget(t, tFnc, tBb);

			if (tFnc)
			{
				transformToCall(pCall, tFnc);
			}
			else if (tBb
					&& tBb->getParent() == pCall->getFunction()
					&& tBb->getPrevNode())
			{
				// TODO
				transformToBranch(pCall, tBb);

				_jumpTargets.push(
						t,
						JumpTarget::eType::CONTROL_FLOW_BR_TRUE,
						m,
						addr);
				LOG << "\t\t" << "call @ " << addr << " -> " << t << std::endl;
				return true;
			}
			else
			{
// TODO: defer call solution to later? after all possible branches are solved?
// often, it is possible to split function here, but later it would not be,
// possible. Then, after such split, more splits are needed for those branches
// thet would make the initial split impossible -> problem, we can not
// transform them.
//				assert(false);
				return false;
			}

			_jumpTargets.push(
					t,
					JumpTarget::eType::CONTROL_FLOW_CALL_TARGET,
					determineMode(tr.capstoneInsn, t),
					addr);
			LOG << "\t\t" << "call @ " << addr << " -> " << t << std::endl;

			// The created function might be in range that we are currently
			// decoding -> if so, trim range size.
			if (nextAddr <= t && t < nextAddr + rangeSize)
			{
				rangeSize = t - nextAddr;
			}

			if (tFnc && _terminatingFncs.count(tFnc))
			{
				auto* ui = new llvm::UnreachableInst(_module->getContext());
				ReplaceInstWithInst(&*_irb->GetInsertPoint(), ui);
				_irb->SetInsertPoint(ui);
				return true;
			}
		}
	}
	// Return -> break flow, do not try to compute target.
	//
	else if (_c2l->isReturnFunctionCall(pCall))
	{
		transformToReturn(pCall);
		if (auto* cond = _c2l->isInConditionReturnFunctionCall(pCall))
		{
			// Name the block and assign an address to it -> keep up with IDA.
			auto* nextBb = cond->getSuccessor(1);

			auto* nBb = getBasicBlockAtAddress(nextAddr);
			auto* oldSucc = cond->getSuccessor(1);
			if (nBb && oldSucc->getParent() == nBb->getParent())
			{
				oldSucc->replaceAllUsesWith(nBb);
				oldSucc->eraseFromParent();
			}
			else
			{
				nextBb->setName(names::generateBasicBlockName(nextAddr));
				addBasicBlock(nextAddr, nextBb);
			}

			return false;
		}
		else
		{
			return true;
		}
	}
	// Unconditional branch -> insert target (if computed).
	//
	else if (_c2l->isBranchFunctionCall(pCall))
	{
		if (auto t = getJumpTarget(addr, pCall, pCall->getArgOperand(0)))
		{
			//.text:08001EE1    call    near ptr loc_8001EE1+1
			//.text:08001EE6    cmp     ebx, esi
			if (addr < t && t < nextAddr)
			{
				return false;
			}
			if (nextAddr <= t && t < nextAddr + rangeSize)
			{
				rangeSize = t - nextAddr;
			}

			auto m = determineMode(tr.capstoneInsn, t);

			getOrCreateBranchTarget(t, tBb, tFnc, pCall);
			if (tBb
					&& tBb->getParent() == pCall->getFunction()
					&& tBb->getPrevNode()) // can not be first in function
			{
				transformToBranch(pCall, tBb);
			}
			else if (tFnc)
			{
				transformToCall(pCall, tFnc);
			}

			// TODO: if target was from load of import addr, do not add it,
			// add everywhere, make this somehow better.
			if (_imports.count(t) == 0)
			{
				_jumpTargets.push(
						t,
						JumpTarget::eType::CONTROL_FLOW_BR_TRUE,
						m,
						addr);
			}
			LOG << "\t\t" << "br @ " << addr << " -> "	<< t << std::endl;
		}

		if (_switchGenerated)
		{
			return true;
		}

		if (auto* cond = _c2l->isInConditionBranchFunctionCall(pCall))
		{
			// Name the block and assign an address to it -> keep up with IDA.
			auto nextAddr = addr + tr.size;
			auto* nextBb = cond->getSuccessor(1);

			auto* nBb = getBasicBlockAtAddress(nextAddr);
			if (nBb && nBb->getParent() == cond->getFunction())
			{
				auto* oldSucc = cond->getSuccessor(1);
				oldSucc->replaceAllUsesWith(nBb);
				oldSucc->eraseFromParent();
			}
			else
			{
				nextBb->setName(names::generateBasicBlockName(nextAddr));
				addBasicBlock(nextAddr, nextBb);
			}

			// Break the flow if BB in which pseudo call is continues to the
			// false branch of cond br.
			auto* bodyBb = pCall->getParent();
			auto* tBr = llvm::dyn_cast<llvm::BranchInst>(bodyBb->getTerminator());
			if (tBr
					&& tBr->isUnconditional()
					&& tBr->getSuccessor(0) == cond->getSuccessor(1))
			{
				llvm::ReturnInst::Create(
						pCall->getModule()->getContext(),
						llvm::UndefValue::get(pCall->getFunction()->getReturnType()),
						tBr);
				tBr->eraseFromParent();
			}
			return false;
		}
		else
		{
			return true;
		}
	}
	// Conditional branch -> insert target (if computed), and next (flow
	// may or may not jump/continue after).
	//
	else if (_c2l->isCondBranchFunctionCall(pCall))
	{
		auto nextAddr = addr + tr.size;
		// Right now, delay slots are only in architectures with fixed
		// instruction size (more specifically, only in MIPS).
		// Therefore, we can multiply current instruction size with number of
		// instructions in the delay slot to get its size.
		// If this changes, we will have to modify this -> create nextAddr
		// target only after delay slot instructions are decoded and we know
		// their sizes.
		//
		nextAddr += _c2l->getDelaySlot(tr.capstoneInsn->id) * tr.size;

		if (auto t = getJumpTarget(addr, pCall, pCall->getArgOperand(1)))
		{
			//.text:08001EE1    call    near ptr loc_8001EE1+1
			//.text:08001EE6    cmp     ebx, esi
			if (addr < t && t < nextAddr)
			{
				return false;
			}

			auto m = determineMode(tr.capstoneInsn, t);
			getOrCreateBranchTarget(t, tBb, tFnc, pCall);

			llvm::BasicBlock* tBbN = nullptr;
			llvm::Function* tFncN = nullptr;
			getOrCreateBranchTarget(nextAddr, tBbN, tFncN, pCall);

			if (tBb && tBbN
					&& tBb->getParent() == tBbN->getParent()
					&& tBb->getParent() == pCall->getFunction()
					&& tBb->getPrevNode()) // is not first in fnct, first -> call
			{
				transformToCondBranch(pCall, pCall->getOperand(0), tBb, tBbN);
			}
			else if (tFnc && tBbN
					&& tBbN->getParent() == pCall->getFunction())
			{
				transformToCondCall(pCall, pCall->getOperand(0), tFnc, tBbN);
			}
			else if (tBb && tBbN
					&& tBb->getParent() != pCall->getFunction()
					&& tBbN->getParent() == pCall->getFunction())
			{
				// TODO: In the end, not now, transform to conditional jump out.
				return false;
			}
			else
			{
				// TODO: deal with this
				return false;
			}

			_jumpTargets.push(
					t,
					JumpTarget::eType::CONTROL_FLOW_BR_TRUE,
					m,
					addr);
			LOG << "\t\t" << "cond br @ " << addr << " -> (true) "
					<< t << std::endl;

			// There is no need to break BB and its decoding if target was not
			// found.
			//
			_jumpTargets.push(
					nextAddr,
					JumpTarget::eType::CONTROL_FLOW_BR_FALSE,
					_c2l->getBasicMode(),
					addr);
			LOG << "\t\t" << "cond br @ " << addr << " -> (false) "
					<< nextAddr << std::endl;

			return true;
		}
	}
	// Analyze ordinary (not control flow) instruction.
	// TODO: maybe move to a separate function.
	//
	else
	{
		AsmInstruction ai(tr.llvmInsn);
		for (auto& i : ai)
		{
			// Skip ranges from which there are loads.
			// Mostly for ARM where there are data references after functions
			// in .text section.
			// We do not use Symbolic tree here, since control flow is not fully
			// reconstructed - matching only constants is safe and should be
			// enough for most cases.
			//
			auto* l = llvm::dyn_cast<llvm::LoadInst>(&i);
			if (l && !_abi->isRegister(l->getPointerOperand()))
			{
				auto* val = llvm_utils::skipCasts(l->getPointerOperand());
				auto* ci = llvm::dyn_cast<llvm::ConstantInt>(val);

				if (ci && !ci->isNegative())
				{
					Address t(ci->getZExtValue());
					auto sz = _abi->getTypeByteSize(l->getType());
					AddressRange r(t, t+sz);
					_ranges.remove(r);

					// Trim currently decoding range size if needed.
					auto nextAddr = addr + tr.size;
					if (nextAddr < t && t < nextAddr + rangeSize)
					{
						rangeSize = t - nextAddr;
					}

					LOG << "\t\t\t\t" << "critical skip " << r << std::endl;
				}
			}
		}
	}

	if (_switchGenerated)
	{
		return true;
	}

	return false;
}

common::Address Decoder::getJumpTarget(
		common::Address addr,
		llvm::CallInst* branchCall,
		llvm::Value* val)
{
	auto st = SymbolicTree::OnDemandRda(val, 20);

	// TODO: better implementation.
	// PIC code.
	// User code is calling stub in .plt.
	// Stub in .plt is computing jmp address (address of import).
	// 4-form_grabber-b794ce9e.so.elf, .plt:00001BE0 ___ctype_toupper_loc:
	//   %u1_1be0 = load i32, i32* @ebx
	//   %u2_1be0 = add i32 %u1_1be0, %u0_1be0
	//   %u3_1be0 = load i32, i32* %u2_1be0
	//   call void @__pseudo_br(i32 %u3_1be0)
	// We do not know the value in @ebx. This should be .got.plt section
	// start -> fix value in symbolic tree before simplification.
	//
	auto* plt = _image->getFileFormat()->getSectionFromAddress(addr);
	if (plt && plt->getName() == ".plt")
	{
		// TODO: do not find this all over again every time.
		auto* gotplt = _image->getFileFormat()->getSection(".got.plt");
		if (gotplt)
		{
			auto gotpltAddr = gotplt->getAddress();
			for (auto* n : st.getPostOrder())
			{
				if (_abi->isGeneralPurposeRegister(n->value))
				{
					n->value = llvm::ConstantInt::get(
							_abi->getDefaultType(),
							gotpltAddr);
				}
			}
		}
	}

	if (plt &&
			((plt->getName() == ".plt.sec") || (plt->getName() == ".plt.got")) &&
		   _config->getConfig().architecture.isX86_32())
	{
		// This case is for x86 32 bit compiled with GCC. Its PLT entries are in
		// sections .plt.sec or .plt.got. An entry is of the form:
		//
		// jmp *offset(%ebx)
		//
		// When this code is encountered register %ebx has been loaded with the
		// address of the start of the Global Offset Table (.got) section.
		//
		// The above jump produces llvm code  that matches the following pattern
		// where the global variable is a reference to the ebx register.

		llvm::LoadInst* li1 = nullptr;
		llvm::LoadInst* li2 = nullptr;
		llvm::ConstantInt* ci = nullptr;
		llvm::GlobalVariable* gv = nullptr;
		auto pattern =
			m_Load(
				m_Add(
					m_Load(m_GlobalVariable(gv), &li2),
					m_ConstantInt(ci)),
				&li1);

		if (match(st, pattern) && (gv->getName().str() == "ebx")) {
			auto* gotSec = _image->getFileFormat()->getSection(".got");
			if (gotSec)
			{
				auto gotsecAddr = gotSec->getAddress();
				Address t = gotsecAddr + ci->getZExtValue();
				if (_imports.count(t))
				{
					return t;
				}
			}
		}
	}

	st.simplifyNode();

	llvm::ConstantInt* ci = nullptr;
	if (match(st, m_ConstantInt(ci)))
	{
		return ci->getZExtValue();
	}

	// If there is load, at first try imports.
	if (match(st, m_Load(m_ConstantInt(ci))))
	{
		Address t = ci->getZExtValue();
		if (_imports.count(t))
		{
			return t;
		}
	}
	// TODO: Some nicer, more general solution?
	// ARM:
	// printf:
	//     116FC 00 C0 9F E5    LDR R12, =__imp_printf
	//     11700 00 F0 9C E5    LDR PC, [R12]
	// tree:
	//>|   %3 = load i32, i32* %2
	//		>|   %0 = load i32, i32* inttoptr (i32 71428 to i32*)
	//				>| i32 71428
	//
	// solveMemoryLoads() and simplifyNode() combo will solve both loads
	// -> we can not check for imports.
	//
	if (match(st, m_Load(m_Load(m_ConstantInt(ci)))))
	{
		if (auto* val = _image->getConstantDefault(ci->getZExtValue()))
		{
			Address t = val->getZExtValue();
			if (_imports.count(t))
			{
				return t;
			}
		}
	}

	// Try to recognize switch pattern.
	// getJumpTargetSwitch() doesn't return target to the caller, it takes care
	// of everything - pseudo to switch transform, jump target creation, ...
	// We just need to return from this function if it succeeds.
	//
	if (getJumpTargetSwitch(addr, branchCall, val, st))
	{
		return Address::Undefined;
	}

	// TOOD: ugly hack - recognize MIPS import stub functions.
	// We compute more than we should here -> solve load and jump to _PROCEDURE_LINKAGE_TABLE_.
	// IDA will either change the loaded word to point to synthetic import section,
	// or marks it as ?? ?? ?? ?? so it can not be used. We read _PROCEDURE_LINKAGE_TABLE_ address.
	// Can we use relocations, or something to mark these pointer not to be used.
	// Problem, this is also used in ihex, where there is even less info.
	//
	if (_config->getConfig().architecture.isMipsOrPic32())
	{
		AsmInstruction ai1(_module, addr);
		AsmInstruction ai2 = ai1.getPrev();
		AsmInstruction ai3 = ai2.getPrev();
		AsmInstruction ai4 = ai3.getPrev();
		if (ai4.isInvalid()
				&& ai1.isValid() && ai1.getDsm() == "jr $t9"
				&& ai2.isValid() && ai2.getCapstoneInsn()->id == MIPS_INS_LW
				&& ai3.isValid() && ai3.getCapstoneInsn()->id == MIPS_INS_LUI)
		{
			return Address::Undefined;
		}
	}

	// If there are loads, try to solve them.
	st.solveMemoryLoads(_image);
	st.simplifyNode();

// TODO: doing this will solve more, also it will screw up integration.ack.Test_2015_ThumbGccElf
	if (getJumpTargetSwitch(addr, branchCall, val, st))
	{
		return Address::Undefined;
	}

	if (auto* ci = llvm::dyn_cast<llvm::ConstantInt>(st.value))
	{
		return ci->getZExtValue();
	}

	return Address::Undefined;
}

/**
 * \return \c True if switch recognized, \c false otherwise.
 */
bool Decoder::getJumpTargetSwitch(
		common::Address addr,
		llvm::CallInst* branchCall,
		llvm::Value* val,
		SymbolicTree& st)
{
	unsigned archByteSz =  _config->getConfig().architecture.getByteSize();

	llvm::BinaryOperator* mulOp = nullptr;
	llvm::BinaryOperator* shlOp = nullptr;
	llvm::ConstantInt* mulShlCi = nullptr;
	llvm::ConstantInt* addrTblCi = nullptr;

	// Pattern:
	//>|   %55 = load i32, i32* %54
	//		>|   %53 = add i32 Addr, %52
	//				>|   %52 = mul i32 %51, 4
	//						>| idx
	//						>| i32 4
	//				>| i32 tableAddr
	if (!match(st, m_Load(
			m_c_Add(
					m_CombineOr(
							m_c_Mul(m_Value(), m_ConstantInt(mulShlCi), &mulOp),
							m_Shl(m_Value(), m_ConstantInt(mulShlCi), &shlOp)),
					m_ConstantInt(addrTblCi)))))
	{
		return false;
	}

	if (!((mulOp && mulShlCi->getZExtValue() == archByteSz)
			|| (shlOp
					&& static_cast<uint64_t>(1 << mulShlCi->getZExtValue()) == archByteSz)))
	{
		return false;
	}

	Address tableAddr = addrTblCi->getZExtValue();
	llvm::Value* idx = mulOp ? mulOp->getOperand(0) : shlOp->getOperand(0);

	LOG << "\t\t" << "switch @ " << addr << std::endl;
	LOG << "\t\t\t" << "table addr @ " << tableAddr << std::endl;

	// Default target.
	//
	Address defAddr;
	llvm::BranchInst* brToSwitch = nullptr; // TODO: i don't like how this is used
	llvm::Value* brToSwitchCondVal = nullptr;
	auto* thisBb = branchCall->getParent();

	Address thisBbAddr = getBasicBlockAddress(thisBb);
	for (auto* p : predecessors(thisBb))
	{
		auto* br = llvm::dyn_cast<llvm::BranchInst>(p->getTerminator());
		if (br && br->isConditional())
		{
			brToSwitch = br;

			Address falseAddr = getBasicBlockAddress(br->getSuccessor(1));
			Address trueAddr = getBasicBlockAddress(br->getSuccessor(0));

			// Branching over this BB -> true branching to default case.
			if (falseAddr.isDefined() && thisBbAddr == falseAddr)
			{
				defAddr = trueAddr;
				brToSwitchCondVal = llvm::ConstantInt::getFalse(_module->getContext());
				LOG << "\t\t\t\t" << "default: branching over -> "
						<< defAddr << std::endl;
			}
			// Branching to this BB -> false branching to default case.
			else if (trueAddr.isDefined() && thisBbAddr == trueAddr)
			{
				defAddr = falseAddr;
				brToSwitchCondVal = llvm::ConstantInt::getTrue(_module->getContext());
				LOG << "\t\t\t\t" << "default: branching to -> "
						<< defAddr << std::endl;
			}

			break;
		}
	}

	// ARM:
	// 90C0 03 F1 9F 97    LDRLS PC, [PC,R3,LSL#2] ; switch jump
	// 90C4 18 01 00 EA    B     loc_952C ; jumptable 000090C0 default cas
	//
	// Pseudo call itself is conditional -> next is default.
	//
	llvm::BranchInst* armCondBr = nullptr;
	auto* cond = _c2l->isInConditionBranchFunctionCall(branchCall);
	if (cond && thisBb == cond->getSuccessor(0))
	{
		// TODO: use known current insn size, not AsmInstruction() -> slow.
		brToSwitch = nullptr;
		defAddr = addr + AsmInstruction(branchCall).getByteSize();
		armCondBr = cond;
	}

	// TODO:
	// ARM:
	// 8AB8 00 D8    BHI def_8D4A ; jumptable 00008D4A default case
	// 8ABA 43 E1    B   loc_8D44
	// ...
	// 8D44 loc_8D44:
	//               switch
	//
	if (defAddr.isUndefined()
			|| (armCondBr == nullptr
					&& (brToSwitch == nullptr || brToSwitchCondVal == nullptr)))
	{
		LOG << "\t\t\t" << "no default target -> skip" << std::endl;
		// TODO: detected labels still should become jump targets.
		// problem, we don't know the jump target type -> they can be functions,
		// not just branch targets.
		// e.g. 04023A3 @ call ds:___CTOR_LIST__[ebx*4]
		return false;
	}
	else
	{
		LOG << "\t\t\t" << "default label @ " << defAddr << std::endl;
	}

	// Jump table size.
	// maybe we could check that compared value is indeed index value.
	//
	unsigned tableSize = 0;
if (brToSwitch)
{
	auto stCond = SymbolicTree::OnDemandRda(brToSwitch->getCondition());
	stCond.simplifyNode();

	auto levelOrd = stCond.getLevelOrder();
	for (SymbolicTree* n : levelOrd)
	{
		llvm::ConstantInt* ci = nullptr;

		// x86:
		//>|   %331 = or i1 %329, %330
		//		>|   %317 = icmp ult i8 %312, 90
		//				>|   %296 = sub i32 %295, 32
		//				>| i8 90
		//		>|   %322 = icmp eq i8 %313, 0
		//				>|   %313 = sub i8 %312, 90
		//						>|   %312 = trunc i32 %311 to i8
		//						>| i8 90
		//				>| i8 0
		if (match(*n, m_c_Or(
				m_c_ICmp(llvm::ICmpInst::ICMP_ULT, m_Value(), m_ConstantInt(ci)),
				m_c_ICmp(llvm::ICmpInst::ICMP_EQ, m_Value(), m_Zero()))))
		{
			tableSize = ci->getZExtValue() + 1;
			LOG << "\t\t\t" << "table size (1) = " << tableSize << std::endl;
			break;
		}
		// TODO: apply this only if it si branching over?
		// mips (???):
		//>|   %319 = icmp ne i32 %318, 0
		//		>|   %316 = icmp ult i32 %315, 121
		//				>|   %314 = and i32 %313, 255
		//				>| i32 121
		//		>| i32 0
		else if (match(*n, m_c_ICmp(llvm::ICmpInst::ICMP_NE,
				m_c_ICmp(llvm::ICmpInst::ICMP_ULT, m_Value(), m_not_Zero(ci)),
				m_Zero())))
		{
			tableSize = ci->getZExtValue();
			LOG << "\t\t\t" << "table size (2) = " << tableSize << std::endl;
			break;
		}
		else if (match(*n, m_c_ICmp(llvm::ICmpInst::ICMP_EQ,
				m_c_ICmp(llvm::ICmpInst::ICMP_ULT, m_Value(), m_not_Zero(ci)),
				m_Zero())))
		{
			tableSize = ci->getZExtValue();
			LOG << "\t\t\t" << "table size (3) = " << tableSize << std::endl;
			break;
		}
	}
}

	// integration.current.switch.TestEXE (switch-test-msvc-O0.ex)
	// Two jump tables.
	//
	std::vector<unsigned> idxs;
	unsigned maxIdx = 0;
	auto idxRoot = SymbolicTree::OnDemandRda(idx);
	idxRoot.simplifyNode();

	llvm::LoadInst* l = nullptr;
	llvm::ConstantInt* ci = nullptr;
	llvm::Instruction* insn = nullptr;
	if (_config->getConfig().architecture.isX86()
			&& tableSize
			&& match(idxRoot, m_Load(
					m_c_Add(m_Instruction(insn), m_ConstantInt(ci)),
					&l))
			&& l->getType()->isIntegerTy()
			&& insn->getType()->isIntegerTy())
	{
		auto* it = llvm::cast<llvm::IntegerType>(l->getType());
		retdec::common::Address tableAddr2(ci->getZExtValue());

		LOG << "\t\t\t" << "second table addr @ " << tableAddr2 << std::endl;

		// Switch index must not be the table offset.
		// We have to use the original index.
		idx = insn;

		while (true)
		{
			auto* ci = _image->getConstantInt(it, tableAddr2);
			if (ci == nullptr)
			{
				break;
			}
			// A safer condition to end this would be to track constant
			// (second table size) used in comparison in instruction
			// before the cond jmp instruction.
			unsigned idx = ci->getZExtValue();
			if (tableSize > 0 && idxs.size() == tableSize)
			{
				break;
			}

			LOG << "\t\t\t\t" << idx << std::endl;

			maxIdx = idx > maxIdx ? idx : maxIdx;
			idxs.push_back(idx);
			tableAddr2 += _abi->getTypeByteSize(ci->getType());
		}
	}

	// Get targets from jump table.
	//
	LOG << "\t\t\t" << "table labels:" << std::endl;
	std::vector<Address> cases;
	Address tableItemAddr = tableAddr;
	Address nextTableAddr;
	auto swTblIt = _switchTableStarts.upper_bound(tableAddr);
	if (swTblIt != _switchTableStarts.end())
	{
		nextTableAddr = swTblIt->first;
	}
	while (true)
	{
		auto* ci = _image->getImage()->isPointer(tableItemAddr)
				? _image->getConstantDefault(tableItemAddr)
				: nullptr;
		if (ci == nullptr)
		{
			break;
		}

		Address item = ci->getZExtValue();
		LOG << "\t\t\t\t" << item << " @ " << tableItemAddr << std::endl;

		tableItemAddr += archByteSz;
		cases.push_back(item);

		if (tableSize > 0 && cases.size() == tableSize)
		{
			break;
		}
		// idx from zero, there can be one more item than max idx number.
		if (maxIdx > 0 && cases.size() > maxIdx)
		{
			break;
		}
		if (nextTableAddr.isUndefined() && tableItemAddr >= nextTableAddr)
		{
			break;
		}
	}
	if (cases.empty())
	{
		LOG << "\t\t\t" << "no targets @ " << tableAddr << " -> skip"
				<< std::endl;
		return false;
	}
	Address tableAddrEnd = tableItemAddr;

	// Put together two tables.
	//
	if (!idxs.empty())
	{
		std::vector<Address> tmp = std::move(cases);
		cases.clear();

		for (auto& i : idxs)
		{
			if (tmp.size() > i)
			{
				cases.push_back(tmp[i]);
			}
		}
	}

	//
	//
	std::vector<llvm::BasicBlock*> casesBbs;
	for (auto c : cases)
	{
		llvm::BasicBlock* tBb = nullptr;
		llvm::Function* tFnc = nullptr;
		// TODO: do not split functions here.
		// if case in another function, do not use it - it may belong to another
		// switch table.
		getOrCreateBranchTarget(c, tBb, tFnc, branchCall);
		if (tBb && tBb->getParent() == branchCall->getFunction())
		{
			casesBbs.push_back(tBb);
		}
		else
		{
			return false;
		}
	}

	llvm::Function* tFnc = nullptr;
	llvm::BasicBlock* defBb = nullptr;
	// TODO: do not split functions here
	getOrCreateBranchTarget(defAddr, defBb, tFnc, branchCall);
	if (defBb == nullptr
			|| defBb->getParent() != branchCall->getFunction())
	{
		assert(false);
		return false;
	}

	auto* sw = transformToSwitch(branchCall, idx, defBb, casesBbs);

	// TODO: create only for those that were transformed to BBs.
	for (auto c : cases)
	{
		_jumpTargets.push(
				c,
				JumpTarget::eType::CONTROL_FLOW_SWITCH_CASE,
				_c2l->getBasicMode(), // mode should not change here
				addr);
		LOG << "\t\t" << "switch -> (case) " << c << std::endl;
	}

	_jumpTargets.push(
			defAddr,
			JumpTarget::eType::CONTROL_FLOW_SWITCH_CASE,
			_c2l->getBasicMode(), // mode should bot change here
			addr);
	LOG << "\t\t" << "switch -> (default) " << defAddr << std::endl;

	_ranges.remove(tableAddr, tableAddrEnd);

	_switchTableStarts[tableAddr].insert(sw);
	_switchGenerated = true;

	if (brToSwitch && brToSwitchCondVal)
	{
		brToSwitch->setCondition(brToSwitchCondVal);
	}

	if (armCondBr)
	{
		llvm::BranchInst::Create(armCondBr->getSuccessor(0), armCondBr);
		auto* rmSucc = armCondBr->getSuccessor(1);
		armCondBr->eraseFromParent();
		rmSucc->eraseFromParent();
	}

	return true;
}

/**
 * ; ASM branch insn
 * ; ASM delay slot insn
 *
 * ==>
 *
 * ; ASM branch insn
 *     LLVM IR body without branch
 * ; ASM delay slot insn
 *     LLVM IR body
 *     branch from prev insn
 */
void Decoder::handleDelaySlotTypical(
		common::Address& addr,
		capstone2llvmir::Capstone2LlvmIrTranslator::TranslationResultOne& res,
		ByteData& bytes,
		llvm::IRBuilder<>& irb)
{
	if (!_c2l->hasDelaySlotTypical(res.capstoneInsn->id))
	{
		return;
	}

	assert(res.branchCall);
	assert(_c2l->getDelaySlot(res.capstoneInsn->id));
	assert(_c2l->getDelaySlot(res.capstoneInsn->id) == 1);

	auto* oldIp = res.branchCall->getParent()->getTerminator();

	irb.SetInsertPoint(res.branchCall);
	std::size_t sz = _c2l->getDelaySlot(res.capstoneInsn->id);
	for (std::size_t i = 0; i < sz; ++i)
	{
		auto r = translate(bytes, addr, irb);
		if (r.failed() || r.llvmInsn == nullptr)
		{
			break;
		}
		_llvm2capstone->emplace(r.llvmInsn, r.capstoneInsn);
		markMipsBreakDelaySlot(r.llvmInsn,
				_c2l->isCondBranchFunctionCall(res.branchCall)
						? res.branchCall->getArgOperand(0) : nullptr);
	}

	irb.SetInsertPoint(oldIp);
}

/**
 *     br cond, target_true, target_false
 *     delay_slot_likely_insn
 *
 * ==>
 *
 *     br cond, ds_likely_bb, target_false
 *  ds_likely_bb:
 *     delay_slot_likely_insn
 *     br target_true
 *  target_false:
 *     ...
 */
void Decoder::handleDelaySlotLikely(
		common::Address& addr,
		capstone2llvmir::Capstone2LlvmIrTranslator::TranslationResultOne& res,
		ByteData& bytes,
		llvm::IRBuilder<>& irb)
{
	if (!_c2l->hasDelaySlotLikely(res.capstoneInsn->id))
	{
		return;
	}

	assert(res.branchCall);
	assert(_c2l->getDelaySlot(res.capstoneInsn->id));
	assert(_c2l->getDelaySlot(res.capstoneInsn->id) == 1);

	auto* br = llvm::dyn_cast<llvm::BranchInst>(res.branchCall->getNextNode());
	if (br && br->isConditional())
	{
		auto* nextBb = br->getParent()->getNextNode();
		auto* newBb = llvm::BasicBlock::Create(
				_module->getContext(),
				"",
				br->getFunction(),
				nextBb);

		auto* target = br->getSuccessor(0);
		br->setSuccessor(0, newBb);
		auto* newTerm = llvm::BranchInst::Create(target, newBb);
		irb.SetInsertPoint(newTerm);

		std::size_t sz = _c2l->getDelaySlot(res.capstoneInsn->id);
		for (std::size_t i = 0; i < sz; ++i)
		{
			auto res = translate(bytes, addr, irb);
			if (res.failed() || res.llvmInsn == nullptr)
			{
				break;
			}
			_llvm2capstone->emplace(res.llvmInsn, res.capstoneInsn);
			markMipsBreakDelaySlot(res.llvmInsn);
		}

		_likelyBb2Target.emplace(newBb, target);
	}
	else
	{
		// TODO: This assumes that the pseudo cond branch was solved and cond
		// branch created, but we should handle likely ds even if it was not.
	}
}

void Decoder::resolvePseudoCalls()
{
	// TODO: fix point algorithm that tries to re-solve all solved and unsolved
	// pseudo calls?
	// - the same result -> ok, nothing
	// - no result -> revert transformation
	// - new result -> new transformation
	// This will not be easy. Can fixpoint even be reached? Reverts, etc. are
	// hard and ugly.

	for (llvm::Function& f : *_module)
	for (llvm::BasicBlock& b : f)
	for (auto i = b.begin(), e = b.end(); i != e;)
	{
		llvm::CallInst* pseudo = llvm::dyn_cast<llvm::CallInst>(&*i);
		++i;
		if (pseudo == nullptr)
		{
			continue;
		}
		if (!_c2l->isCallFunctionCall(pseudo)
				&& !_c2l->isReturnFunctionCall(pseudo)
				&& !_c2l->isBranchFunctionCall(pseudo)
				&& !_c2l->isCondBranchFunctionCall(pseudo))
		{
			continue;
		}

		llvm::Instruction* real = pseudo->getNextNode();
		if (real == nullptr)
		{
			continue;
		}
		++i;

		// TODO: fix calls, maybe we could create the calls for the first time
		// here.
		//
		if (_c2l->isCallFunctionCall(pseudo)
				&& llvm::isa<llvm::CallInst>(real))
		{
			Address t = getJumpTarget(
					AsmInstruction::getInstructionAddress(real),
					pseudo,
					pseudo->getArgOperand(0));

			if (t.isUndefined())
			{
				++i;
				auto* st = llvm::cast<llvm::StoreInst>(*real->user_begin());
				st->eraseFromParent();
				real->eraseFromParent();
			}
		}
	}
}

void Decoder::finalizePseudoCalls()
{
	for (auto& f : *_module)
	for (auto& b : f)
	for (auto i = b.begin(), e = b.end(); i != e;)
	{
		auto* pseudo = llvm::dyn_cast<llvm::CallInst>(&*i);
		++i;
		if (pseudo == nullptr)
		{
			continue;
		}

		bool icf = _c2l->isCallFunctionCall(pseudo);
		bool irf = _c2l->isReturnFunctionCall(pseudo);
		bool ibf = _c2l->isBranchFunctionCall(pseudo);
		bool icbf = _c2l->isCondBranchFunctionCall(pseudo);

		if (!icf && !irf && !ibf && !icbf)
		{
			continue;
		}

		if (icf && _config->getConfig().architecture.isMipsOrPic32()
				&& !llvm::isa<llvm::CallInst>(pseudo->getNextNode()))
		{
			auto* retObj = getCallReturnObject();
			auto* type = llvm::FunctionType::get(retObj->getValueType(), false);
			llvm::IRBuilder<> builder(pseudo->getNextNode());
			auto* target = builder.CreateIntToPtr(
					pseudo->getArgOperand(0), type->getPointerTo());
			auto* call = builder.CreateCall(target);
			builder.CreateStore(call, retObj);
		}

		llvm::Instruction* it = pseudo->getPrevNode();
		pseudo->eraseFromParent();

		bool mipsFirstAsmInstr = true;
		while (it)
		{
			if (AsmInstruction::isLlvmToAsmInstruction(it))
			{
				if (_config->getConfig().architecture.isMipsOrPic32()
						&& mipsFirstAsmInstr)
				{
					mipsFirstAsmInstr = false;
				}
				else
				{
					break;
				}
			}

			auto* i = it;
			it = it->getPrevNode();

			// Return address store to stack in x86 calls.
			//
			if (_config->getConfig().architecture.isX86()
					&& (icf || irf))
			if (auto* st = llvm::dyn_cast<llvm::StoreInst>(i))
			{
				if (_abi->isStackPointerRegister(st->getPointerOperand())
						|| llvm::isa<llvm::ConstantInt>(st->getValueOperand()))
				{
					st->eraseFromParent();
					i = nullptr;
				}
			}

			// Return address store to register in MIPS calls.
			//
			if (_config->getConfig().architecture.isMipsOrPic32()
					&& icf)
			if (auto* st = llvm::dyn_cast<llvm::StoreInst>(i))
			{
				if (_abi->isRegister(st->getPointerOperand(), MIPS_REG_RA))
				{
					st->eraseFromParent();
					i = nullptr;
				}
			}

			// Return address store to register in MIPS calls.
			// TODO: what about other possible LR stores? e.g. see
			// patternsPseudoCall_arm().
			//
			if (_config->getConfig().architecture.isArm32OrThumb()
					&& icf)
			if (auto* st = llvm::dyn_cast<llvm::StoreInst>(i))
			{
				if (_abi->isRegister(st->getPointerOperand(), ARM_REG_LR))
				{
					st->eraseFromParent();
					i = nullptr;
				}
			}

			// TODO: again, other possible stores && r32 stores.
			//
			if (_config->getConfig().architecture.isPpc()
					&& icf)
			if (auto* st = llvm::dyn_cast<llvm::StoreInst>(i))
			{
				if (_abi->isRegister(st->getPointerOperand(), PPC_REG_LR))
				{
					st->eraseFromParent();
					i = nullptr;
				}
			}

			if (i && !i->getType()->isVoidTy() && i->use_empty())
			{
				i->eraseFromParent();
			}
		}
	}
}

} // namespace bin2llvmir
} // namespace retdec
