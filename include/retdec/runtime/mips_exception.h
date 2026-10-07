#ifndef RETDEC_RUNTIME_MIPS_EXCEPTION_H
#define RETDEC_RUNTIME_MIPS_EXCEPTION_H

#include <limits.h>

#if UINT_MAX != 0xffffffffU || CHAR_BIT != 8
#error "MIPS exception runtime requires 32-bit unsigned int and 8-bit bytes"
#endif

#if defined(__GNUC__) || defined(__clang__)
#define RETDEC_MIPS_NORETURN __attribute__((noreturn))
#else
#error "Define non-returning exception dispatch for this compiler"
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* The embedding runtime owns this state and must keep Status current.
 * Other guest registers/memory and pending loads remain the runtime's concern.
 * Dispatch must enter state->pc and must not return to the decompiled C stack.
 * Resumption requires a guest-PC dispatcher, not returning from this helper.
 * Missing runtime bindings intentionally fail at link time.
 */
struct retdec_mips_exception_state {
    unsigned int status;
    unsigned int cause;
    unsigned int epc;
    unsigned int pc;
    unsigned int hi;
    unsigned int lo;
};

extern struct retdec_mips_exception_state *retdec_mips_exception_context(void);
extern void retdec_mips_exception_dispatch(
        struct retdec_mips_exception_state *state) RETDEC_MIPS_NORETURN;

static __inline__ void __retdec_mips_break(
        unsigned int instruction_pc, unsigned int delay_slot, unsigned int hi, unsigned int lo)
        RETDEC_MIPS_NORETURN;
static __inline__ void __retdec_mips_break(
        unsigned int instruction_pc, unsigned int delay_slot, unsigned int hi, unsigned int lo)
{
    struct retdec_mips_exception_state *state = retdec_mips_exception_context();
    state->epc = instruction_pc - (delay_slot ? 4u : 0u);
    state->cause = 0x24u | (delay_slot ? 0x80000000u : 0u);
    state->pc = (state->status & 0x00400000u) ? 0xbfc00180u : 0x80000080u;
    state->status = (state->status & ~0x3fu) | ((state->status & 0x0fu) << 2);
    state->hi = hi;
    state->lo = lo;
    retdec_mips_exception_dispatch(state);
}

#ifdef __cplusplus
}
#endif
#undef RETDEC_MIPS_NORETURN
#endif
