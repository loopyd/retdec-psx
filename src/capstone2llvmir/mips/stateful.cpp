#include "retdec/capstone2llvmir/mips/stateful.h"
#include "retdec/capstone2llvmir/capstone2llvmir.h"

#include <stdexcept>
#include <vector>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

namespace retdec { namespace capstone2llvmir {

llvm::Function* translateMips32Stateful(llvm::Module& module,
        const uint8_t* bytes, std::size_t size, uint32_t base,
        const std::string& name, bool biosBus)
{
    if (!bytes || !size || size % 4 || base % 4 || size > 0x100000000ULL - base
            || !module.empty())
        throw std::invalid_argument("stateful MIPS needs an empty module and aligned code");
    std::vector<uint32_t> words;
    for (std::size_t offset = 0; offset < size; offset += 4) {
        uint32_t w = uint32_t(bytes[offset]) | uint32_t(bytes[offset+1]) << 8
                | uint32_t(bytes[offset+2]) << 16 | uint32_t(bytes[offset+3]) << 24;
        unsigned op = w >> 26, sub = w & 63, rs = (w >> 21) & 31;
        bool special = op == 0 && (sub == 0 || sub == 2 || sub == 3 || sub == 4
                || sub == 6 || sub == 7 || sub == 8 || sub == 9 || sub == 12 || sub == 13
                || (sub >= 16 && sub <= 19) || (sub >= 24 && sub <= 27)
                || (sub >= 32 && sub <= 39) || sub == 42 || sub == 43);
        bool cop0 = op == 16 && (rs == 0 || rs == 2 || rs == 4 || rs == 6
                || w == 0x42000010);
        unsigned rt = (w >> 16) & 31;
        bool regimm = op == 1 && (rt == 0 || rt == 1 || rt == 16 || rt == 17);
        bool memory = (op >= 32 && op <= 38) || op == 40 || op == 41
                || op == 42 || op == 43 || op == 46;
        if (!(special || regimm || (op >= 2 && op <= 15) || cop0 || memory))
            throw std::invalid_argument("unsupported stateful MIPS instruction at " + std::to_string(base+offset));
        words.push_back(w);
    }
    auto translator = Capstone2LlvmIrTranslator::createMips32(&module);
    auto& context = module.getContext();
    llvm::IRBuilder<> b(context);
    auto* word = b.getInt32Ty();
    std::vector<llvm::Type*> parameters = {word->getPointerTo(), b.getInt8PtrTy()};
    if (biosBus) {
        parameters.push_back(b.getInt8PtrTy());
        parameters.push_back(b.getInt8PtrTy());
    }
    auto* fn = llvm::Function::Create(llvm::FunctionType::get(word,
            parameters, false),
            llvm::GlobalValue::ExternalLinkage, name, &module);
    auto* entry = llvm::BasicBlock::Create(context, "dispatch", fn);
    b.SetInsertPoint(entry);
    auto args = fn->arg_begin();
    auto* state = &*args++; state->setName("state");
    auto* ram = &*args++; ram->setName("ram");
    llvm::Value* rom = nullptr;
    llvm::Value* scratch = nullptr;
    if (biosBus) {
        rom = &*args++; rom->setName("rom");
        scratch = &*args; scratch->setName("scratch");
    }
    std::vector<llvm::Value*> slots;
    for (unsigned i = 0; i < (biosBus ? 75u : 73u); ++i)
        slots.push_back(b.CreateGEP(state, b.getInt32(i)));
    auto load = [&](unsigned i) { return b.CreateLoad(slots[i]); };
    auto store = [&](unsigned i, llvm::Value* value) { b.CreateStore(value, slots[i]); };
    auto* pc = load(34);
    auto* branchActive = b.CreateICmpNE(load(67), b.getInt32(0));
    auto* branchTarget = load(68);
    auto* pending = load(69);
    auto* pendingValue = load(70);
    auto* pendingActive = b.CreateICmpNE(load(71), b.getInt32(0));
    auto* pendingMask = load(72);
    auto* missing = llvm::BasicBlock::Create(context, "unmapped", fn);
    auto* dispatch = b.CreateSwitch(pc, missing, words.size());
    b.SetInsertPoint(missing); b.CreateRet(b.getInt32(2));

    for (std::size_t index = 0; index < words.size(); ++index) {
        uint32_t w = words[index], address = base + index * 4;
        unsigned op = w >> 26, sub = w & 63, rs = (w >> 21) & 31;
        unsigned rt = (w >> 16) & 31, rd = (w >> 11) & 31;
        bool branch = op == 1 || op == 2 || op == 3 || (op >= 4 && op <= 7)
                || (op == 0 && (sub == 8 || sub == 9));
        auto* block = llvm::BasicBlock::Create(context, "pc_"+std::to_string(address), fn);
        dispatch->addCase(b.getInt32(address), block); b.SetInsertPoint(block);
        if (branch) {
            auto* valid = llvm::BasicBlock::Create(context, "branch", fn);
            auto* reject = llvm::BasicBlock::Create(context, "unsupported_delay", fn);
            b.CreateCondBr(branchActive, reject, valid);
            b.SetInsertPoint(reject); b.CreateRet(b.getInt32(3)); b.SetInsertPoint(valid);
        }
        // Redux tests software interrupts after Status/Cause writes and RFE.
        // Its delayed-PC overwrite on software IRQ in a taken slot is not a
        // resumable exception. Reject before changing any caller state.
        bool testsSoftwareIrq = op == 16 && (w == 0x42000010
                || ((rs == 4 || rs == 6) && (rd == 12 || rd == 13)));
        llvm::Value* softwareIrq = b.getInt1(false);
        if (testsSoftwareIrq) {
            llvm::Value* status = load(47);
            llvm::Value* cause = load(48);
            if (w == 0x42000010)
                status = b.CreateOr(b.CreateAnd(status,b.getInt32(0xfffffff0)),
                        b.CreateLShr(b.CreateAnd(status,b.getInt32(0x3c)),2));
            else if (rd == 12) status = rt ? static_cast<llvm::Value*>(load(rt)) : b.getInt32(0);
            else cause = b.CreateAnd(rt ? static_cast<llvm::Value*>(load(rt)) : b.getInt32(0),b.getInt32(~0xfc00u));
            softwareIrq = b.CreateAnd(b.CreateICmpNE(b.CreateAnd(status,b.getInt32(1)),b.getInt32(0)),
                    b.CreateICmpNE(b.CreateAnd(b.CreateAnd(status,cause),b.getInt32(0x300)),b.getInt32(0)));
            auto* valid = llvm::BasicBlock::Create(context,"cp0_write",fn);
            auto* reject = llvm::BasicBlock::Create(context,"unsupported_slot_irq",fn);
            b.CreateCondBr(b.CreateAnd(branchActive,softwareIrq),reject,valid);
            b.SetInsertPoint(reject); b.CreateRet(b.getInt32(3)); b.SetInsertPoint(valid);
        }
        bool memory = op >= 32;
        llvm::Value* memoryAddress = nullptr;
        llvm::Value* busPointer = ram;
        llvm::Value* busOffset = nullptr;
        llvm::Value* irqAccess = b.getInt1(false);
        llvm::Value* irqStatusAccess = b.getInt1(false);
        llvm::Value* misaligned = b.getInt1(false);
        bool isLoad = op >= 32 && op <= 38;
        bool merge = op == 34 || op == 38 || op == 42 || op == 46;
        unsigned width = (op == 32 || op == 36 || op == 40) ? 1
                : (op == 33 || op == 37 || op == 41) ? 2 : 4;
        if (memory) {
            memoryAddress = b.CreateAdd(rs ? static_cast<llvm::Value*>(load(rs)) : b.getInt32(0),
                    b.getInt32(int32_t(int16_t(w))));
            misaligned = merge ? b.getInt1(false) : b.CreateICmpNE(
                    b.CreateAnd(memoryAddress,b.getInt32(width-1)),b.getInt32(0));
            auto* physical = b.CreateAnd(memoryAddress,b.getInt32(0x1fffffff));
            auto* segment = b.CreateAnd(memoryAddress,b.getInt32(0xe0000000));
            auto* allowedSegment = b.CreateOr(b.CreateICmpEQ(segment,b.getInt32(0)),
                    b.CreateOr(b.CreateICmpEQ(segment,b.getInt32(0x80000000)),
                            b.CreateICmpEQ(segment,b.getInt32(0xa0000000))));
            auto* validRam = b.CreateAnd(allowedSegment,
                    b.CreateICmpULT(physical,b.getInt32(0x800000)));
            busOffset = b.CreateAnd(physical,b.getInt32(0x1fffff));
            llvm::Value* validBus = validRam;
            if (biosBus) {
                auto* validScratch = b.CreateAnd(allowedSegment,b.CreateAnd(
                        b.CreateICmpUGE(physical,b.getInt32(0x1f800000)),
                        b.CreateICmpULT(physical,b.getInt32(0x1f800400))));
                auto* validRom = b.CreateAnd(allowedSegment,b.CreateAnd(
                        b.CreateICmpUGE(physical,b.getInt32(0x1fc00000)),
                        b.CreateICmpULT(physical,b.getInt32(0x1fc80000))));
                irqStatusAccess = b.CreateICmpEQ(physical,b.getInt32(0x1f801070));
                irqAccess = b.CreateAnd(allowedSegment,b.CreateOr(irqStatusAccess,
                        b.CreateICmpEQ(physical,b.getInt32(0x1f801074))));
                if (merge || width == 1) irqAccess = b.getInt1(false);
                validBus = b.CreateOr(validBus,b.CreateOr(validScratch,irqAccess));
                if (isLoad) validBus = b.CreateOr(validBus,validRom);
                busPointer = b.CreateSelect(validScratch,scratch,b.CreateSelect(validRom,rom,ram));
                busOffset = b.CreateSelect(validScratch,b.CreateSub(physical,b.getInt32(0x1f800000)),
                        b.CreateSelect(validRom,b.CreateSub(physical,b.getInt32(0x1fc00000)),busOffset));
            }
            auto* cacheNormal = b.CreateICmpEQ(b.CreateAnd(load(47),b.getInt32(0x10000)),b.getInt32(0));
            auto* accepted = llvm::BasicBlock::Create(context,"ram_access",fn);
            auto* reject = llvm::BasicBlock::Create(context,"unsupported_bus",fn);
            auto* supported = b.CreateAnd(cacheNormal,b.CreateOr(misaligned,validBus));
            // Redux's current patch cancels delayed PC writes only for BREAK
            // and SYSCALL. Do not assume the same for address-error paths.
            supported = b.CreateAnd(supported,b.CreateNot(b.CreateAnd(branchActive,misaligned)));
            b.CreateCondBr(supported,accepted,reject);
            b.SetInsertPoint(reject); b.CreateRet(b.getInt32(4)); b.SetInsertPoint(accepted);
        }
        store(0, b.getInt32(0));
        store(67, b.getInt32(0)); store(71, b.getInt32(0)); store(72,b.getInt32(0));
        llvm::Value* next = b.CreateSelect(branchActive, branchTarget, b.getInt32(address+4));
        unsigned written = 0;
        llvm::Value* exception = b.getInt1(false);
        unsigned cause = 0;
        if (memory) {
            exception = misaligned; cause = isLoad ? 0x10 : 0x14;
            auto* access = llvm::BasicBlock::Create(context,"aligned",fn);
            auto* fault = llvm::BasicBlock::Create(context,"address_error",fn);
            auto* done = llvm::BasicBlock::Create(context,"memory_done",fn);
            b.CreateCondBr(misaligned,fault,access);
            b.SetInsertPoint(fault); store(43,memoryAddress); b.CreateBr(done);
            b.SetInsertPoint(access);
            llvm::Value* physical = busOffset;
            if (merge) physical = b.CreateAnd(physical,b.getInt32(~3u));
            auto* ordinary = llvm::BasicBlock::Create(context,"memory_bytes",fn);
            if (biosBus) {
                auto* irq = llvm::BasicBlock::Create(context,"irq_register",fn);
                b.CreateCondBr(irqAccess,irq,ordinary); b.SetInsertPoint(irq);
                auto* slot = b.CreateSelect(irqStatusAccess,slots[73],slots[74]);
                auto* oldValue = b.CreateLoad(slot);
                if (isLoad) {
                    llvm::Value* value = oldValue;
                    if (width == 2) {
                        auto* half = b.CreateTrunc(value,b.getInt16Ty());
                        value = op == 33 ? b.CreateSExt(half,word) : b.CreateZExt(half,word);
                    }
                    store(69,b.getInt32(rt)); store(70,value);
                    store(71,b.getInt32(rt != 0)); store(72,b.getInt32(0));
                } else {
                    auto* value = load(rt);
                    // Redux's SH ISTAT uses the entire source register.
                    auto* mask = width == 2 ? b.CreateOr(b.CreateAnd(oldValue,b.getInt32(0xffff0000)),
                            b.CreateAnd(value,b.getInt32(0xffff))) : value;
                    b.CreateStore(b.CreateSelect(irqStatusAccess,b.CreateAnd(oldValue,value),mask),slot);
                }
                b.CreateBr(done);
            } else b.CreateBr(ordinary);
            b.SetInsertPoint(ordinary);
            llvm::Value* value = b.getInt32(0);
            if (isLoad || merge) {
                for (unsigned byte = 0; byte < width; ++byte) {
                    auto* p = b.CreateGEP(busPointer,b.CreateAdd(physical,b.getInt32(byte)));
                    auto* v = b.CreateZExt(b.CreateLoad(p),word);
                    value = b.CreateOr(value,b.CreateShl(v,byte*8));
                }
            }
            auto* byteShift = b.CreateMul(b.CreateAnd(memoryAddress,b.getInt32(3)),b.getInt32(8));
            auto* leftShift = b.CreateSub(b.getInt32(24),byteShift);
            if (isLoad) {
                if (op == 32 || op == 33)
                    value = b.CreateSExt(b.CreateTrunc(value,b.getIntNTy(width*8)),word);
                llvm::Value* mask = b.getInt32(0);
                if (op == 34) {
                    mask = b.CreateNot(b.CreateShl(b.getInt32(~0u),leftShift));
                    value = b.CreateShl(value,leftShift);
                } else if (op == 38) {
                    mask = b.CreateNot(b.CreateLShr(b.getInt32(~0u),byteShift));
                    value = b.CreateLShr(value,byteShift);
                }
                store(69,b.getInt32(rt)); store(70,value); store(71,b.getInt32(rt!=0)); store(72,mask);
            } else {
                auto* source = load(rt);
                if (op == 42) value = b.CreateOr(b.CreateLShr(source,leftShift),
                        b.CreateAnd(value,b.CreateNot(b.CreateLShr(b.getInt32(~0u),leftShift))));
                else if (op == 46) value = b.CreateOr(b.CreateShl(source,byteShift),
                        b.CreateAnd(value,b.CreateNot(b.CreateShl(b.getInt32(~0u),byteShift))));
                else value = source;
                for (unsigned byte = 0; byte < width; ++byte) {
                    auto* p = b.CreateGEP(busPointer,b.CreateAdd(physical,b.getInt32(byte)));
                    b.CreateStore(b.CreateTrunc(b.CreateLShr(value,byte*8),b.getInt8Ty()),p);
                }
            }
            b.CreateBr(done); b.SetInsertPoint(done);
        } else if (branch) {
            llvm::Value* taken = b.getInt1(true);
            llvm::Value* target = b.getInt32(((address+4)&0xf0000000u) | ((w&0x03ffffffu)<<2));
            if (op == 1) {
                auto* a = load(rs);
                taken = (rt & 1) ? b.CreateICmpSGE(a,b.getInt32(0)) : b.CreateICmpSLT(a,b.getInt32(0));
                target = b.getInt32(address+4+int32_t(int16_t(w))*4);
            } else if (op >= 4 && op <= 7) {
                auto* a = load(rs); auto* z = b.getInt32(0);
                if (op == 4) taken = b.CreateICmpEQ(a, load(rt));
                if (op == 5) taken = b.CreateICmpNE(a, load(rt));
                if (op == 6) taken = b.CreateICmpSLE(a, z);
                if (op == 7) taken = b.CreateICmpSGT(a, z);
                target = b.getInt32(address+4+int32_t(int16_t(w))*4);
            } else if (op == 0) target = load(rs);
            if (op == 3 || (op == 1 && rt >= 16) || (op == 0 && sub == 9)) {
                written = op == 0 ? rd : 31;
                if (written) store(written, b.getInt32(address+8));
            }
            store(67, b.CreateZExt(taken, word)); store(68, target);
        } else if (op == 0 && (sub == 12 || sub == 13)) {
            exception = b.getInt1(true); cause = sub == 13 ? 0x24 : 0x20;
        } else if (op == 16) {
            if (w == 0x42000010) {
                auto* sr = load(47);
                store(47, b.CreateOr(b.CreateAnd(sr, b.getInt32(0xfffffff0)),
                        b.CreateLShr(b.CreateAnd(sr,b.getInt32(0x3c)),2)));
            } else if (rs == 0 || rs == 2) {
                store(69, b.getInt32(rt)); store(70, load(35+rd));
                store(71, b.getInt32(rt != 0));
            } else {
                llvm::Value* value = load(rt);
                if (rd == 13) value = b.CreateAnd(value,b.getInt32(~0xfc00u));
                store(35+rd,value);
            }
        } else if (op == 8 || (op == 0 && (sub == 32 || sub == 34))) {
            auto* a = load(rs);
            llvm::Value* c = op == 8 ? static_cast<llvm::Value*>(b.getInt32(int32_t(int16_t(w)))) : load(rt);
            bool subtract = op == 0 && sub == 34;
            auto* value = subtract ? b.CreateSub(a,c) : b.CreateAdd(a,c);
            auto* sign = subtract ? b.CreateXor(a,c) : b.CreateXor(c,value);
            exception = b.CreateICmpSLT(b.CreateAnd(b.CreateXor(a,value),sign),b.getInt32(0));
            cause = 0x30; written = op == 8 ? rt : rd;
            if (written) store(written,b.CreateSelect(exception,load(written),value));
        } else {
            auto result = translator->translate(bytes+index*4,4,address,b,1,false);
            if (result.failed()) throw std::runtime_error("stateful instruction failed translation");
            for (auto pair : result.insns) cs_free(pair.second,1);
            if (op == 0) {
                if (sub <= 7 || sub == 16 || sub == 18 || sub >= 32) written = rd;
            } else written = rt;
        }
        // Commit the preceding load after the instruction reads old GPRs.
        // Merge masks apply to the value at commit, including consecutive LWL/LWR.
        // A current explicit write cancels the delayed write to that register.
        for (unsigned reg = 1; reg != 32; ++reg) {
            llvm::Value* commit = b.CreateAnd(pendingActive,b.CreateICmpEQ(pending,b.getInt32(reg)));
            if (written == reg) commit = b.CreateAnd(commit,exception);
            auto* previous = load(reg);
            auto* merged = b.CreateOr(b.CreateAnd(previous,pendingMask),pendingValue);
            store(reg,b.CreateSelect(commit,merged,previous));
        }
        if (cause) {
            auto* trap = llvm::BasicBlock::Create(context,"exception",fn);
            auto* finish = llvm::BasicBlock::Create(context,"retire",fn);
            b.CreateCondBr(exception,trap,finish); b.SetInsertPoint(trap);
            auto* sr = load(47);
            store(48,b.CreateOr(b.getInt32(cause),b.CreateSelect(branchActive,b.getInt32(0x80000000),b.getInt32(0))));
            store(49,b.CreateSelect(branchActive,b.getInt32(address-4),b.getInt32(address)));
            store(34,b.CreateSelect(b.CreateICmpNE(b.CreateAnd(sr,b.getInt32(0x400000)),b.getInt32(0)),
                    b.getInt32(0xbfc00180),b.getInt32(0x80000080)));
            store(47,b.CreateOr(b.CreateAnd(sr,b.getInt32(~0x3fu)),b.CreateShl(b.CreateAnd(sr,b.getInt32(15)),2)));
            store(67,b.getInt32(0)); b.CreateRet(b.getInt32(1)); b.SetInsertPoint(finish);
        }
        if (testsSoftwareIrq || biosBus) {
            llvm::Value* interrupt = softwareIrq;
            if (biosBus) {
                // Native branchTest polls external interrupts after taken slots.
                // Device producers update ISTAT between step calls; no fabricated
                // cycles or device events are introduced here.
                auto* hardwareIrq = b.CreateAnd(branchActive,b.CreateAnd(
                        b.CreateICmpNE(b.CreateAnd(load(73),load(74)),b.getInt32(0)),
                        b.CreateICmpEQ(b.CreateAnd(load(47),b.getInt32(0x401)),b.getInt32(0x401))));
                interrupt = b.CreateOr(interrupt,hardwareIrq);
            }
            auto* irq = llvm::BasicBlock::Create(context,"interrupt",fn);
            auto* finish = llvm::BasicBlock::Create(context,"no_interrupt",fn);
            b.CreateCondBr(interrupt,irq,finish); b.SetInsertPoint(irq);
            auto* sr = load(47);
            store(48,b.CreateSelect(softwareIrq,load(48),b.getInt32(0x400)));
            store(49,next);
            store(34,b.CreateSelect(b.CreateICmpNE(b.CreateAnd(sr,b.getInt32(0x400000)),b.getInt32(0)),
                    b.getInt32(0xbfc00180),b.getInt32(0x80000080)));
            store(47,b.CreateOr(b.CreateAnd(sr,b.getInt32(~0x3fu)),b.CreateShl(b.CreateAnd(sr,b.getInt32(15)),2)));
            store(67,b.getInt32(0)); b.CreateRet(b.getInt32(1)); b.SetInsertPoint(finish);
        }
        store(34,next); store(0,b.getInt32(0)); b.CreateRet(b.getInt32(0));
    }
    for (unsigned i = 0; i != 34; ++i) {
        unsigned reg = i < 32 ? unsigned(MIPS_REG_0)+i
                : unsigned(i == 32 ? MIPS_REG_HI : MIPS_REG_LO);
        auto* global = translator->getRegister(reg);
        std::vector<llvm::Instruction*> users;
        for (auto* user : global->users())
            if (auto* instruction = llvm::dyn_cast<llvm::Instruction>(user))
                if (instruction->getFunction() == fn) users.push_back(instruction);
        for (auto* user : users) user->replaceUsesOfWith(global,slots[i]);
    }
    std::vector<llvm::Instruction*> mappingStores;
    for (auto& block : *fn)
        for (auto& instruction : block)
            if (translator->isSpecialAsm2LlvmInstr(&instruction))
                mappingStores.push_back(&instruction);
    for (auto* instruction : mappingStores) instruction->eraseFromParent();
    if (llvm::verifyFunction(*fn)) throw std::runtime_error("invalid stateful MIPS IR");
    return fn;
}
} }
