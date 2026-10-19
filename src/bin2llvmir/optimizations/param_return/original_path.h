#ifndef RETDEC_BIN2LLVMIR_ORIGINAL_PATH_H
#define RETDEC_BIN2LLVMIR_ORIGINAL_PATH_H
#include "original_storage.h"
#include "retdec/common/psx_memory.h"
namespace retdec { namespace bin2llvmir {
std::optional<common::OriginalSymbolicFrame> recoverBoundPathFrame(const Disposition::EntryPath& path);
std::optional<Disposition::EntryPath> deriveBoundEntryPath(const Disposition::Call& call,
    const RegisterState& before, const std::map<unsigned, Disposition::Definition>& definitions,
    const Disposition::Evidence& caller, const std::string& key, const std::string& imageId,
    uint64_t start, uint64_t end, const Disposition::Evidence& evidence,
    const common::PsxMemoryContext& context);
} }
#endif
