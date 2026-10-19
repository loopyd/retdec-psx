#ifndef RETDEC_BIN2LLVMIR_ORIGINAL_PATH_H
#define RETDEC_BIN2LLVMIR_ORIGINAL_PATH_H
#include "original_storage.h"
#include "retdec/common/psx_memory.h"
namespace retdec { namespace bin2llvmir {
std::optional<common::OriginalSymbolicFrame> recoverBoundPathFrame(const Disposition::EntryPath& path);
std::optional<Disposition::EntryPath> deriveBoundEntryPath(const Disposition::Call& call,
    const RegisterState& before, const std::map<unsigned, Disposition::Definition>& definitions,
    const Disposition::Evidence& caller, const common::ReviewedOriginalFunction& identity,
    const Disposition::Evidence& evidence, const common::PsxMemoryContext& context);
} }
#endif
