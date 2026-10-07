#ifndef RETDEC_CAPSTONE2LLVMIR_MIPS_STATEFUL_H
#define RETDEC_CAPSTONE2LLVMIR_MIPS_STATEFUL_H

#include <cstddef>
#include <cstdint>
#include <string>

namespace llvm { class Module; class Function; }
namespace retdec { namespace capstone2llvmir {

/** Emit an opt-in R3000 register-state step function into an empty module.
 * Signature: unsigned step(unsigned state[73], unsigned char ram[2097152]).
 * ABI v2: state and RAM must be initialized, writable and nonoverlapping.
 * Layout: GPR[0..31], HI=32, LO=33, PC=34, CP0[35..66],
 * pending branch flag=67, pending target=68, pending load register=69,
 * pending value=70, pending active=71, pending merge-preserve mask=72.
 * Returns 0 after one instruction, 1 on exception entry, 2 for unmapped PC,
 * 3 for a branch inside a taken branch delay slot, 4 for unsupported bus/cache
 * access. Rejected/unmapped steps leave state and RAM unchanged.
 * Code at every supplied aligned PC remains independently reachable.
 * Supports register arithmetic, ordinary branches/jumps, BREAK/SYSCALL,
 * BLTZ/BGEZ/BLTZAL/BGEZAL, MFC0/CFC0/MTC0/CTC0, RFE, LB/LBU/LH/LHU/LW/LWL/LWR and
 * SB/SH/SW/SWL/SWR. RAM mirrors cover physical 0..8 MiB through low/KSEG0/KSEG1
 * aliases. Misalignment raises address exceptions outside taken branch slots;
 * misalignment inside such a slot rejects with code 4 pending oracle validation.
 * Default ABI v2 rejects MMIO, ROM and scratchpad. With biosBus=true the
 * signature is unsigned step(unsigned state[75], unsigned char ram[2097152],
 * const unsigned char rom[524288], unsigned char scratch[1024]). ABI v3 adds
 * ISTAT=73 and IMASK=74. All buffers must be valid and nonoverlapping.
 * ROM reads and scratchpad reads/writes support physical/KSEG0/KSEG1 aliases.
 * Halfword/word accesses to 1f801070/74 implement Redux ISTAT/IMASK semantics.
 * ROM writes, other MMIO, cache isolation and unsupported instructions (GTE)
 * reject. The caller dispatches original PC ranges, including ROM ranges, and
 * must invalidate translations when code bytes change. No live instruction cache.
 * Software interrupts are tested after Status/Cause writes and RFE; delivery in
 * taken slots rejects unchanged with code 3. Hardware IRQ is sampled after a
 * taken slot, as in Redux branchTest, with Cause=0x400 and EPC=next PC. The caller
 * supplies device events by updating ISTAT between calls. No device scheduling,
 * DMA, timers, cache or cycle model is implied. GTE IRQ deferral is unsupported.
 * No ABI recovery or normal function-level optimizer pipeline may be applied.
 * State belongs to the caller; no hidden CPU globals or host exception callback.
 */
llvm::Function* translateMips32Stateful(llvm::Module& module,
        const uint8_t* bytes, std::size_t size, uint32_t base,
        const std::string& name, bool biosBus = false);

} }
#endif
