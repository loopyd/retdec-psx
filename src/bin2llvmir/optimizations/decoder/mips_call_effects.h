#pragma once

#include <cstdint>
#include "retdec/common/function.h"

namespace llvm { class Module; }
namespace retdec { namespace config { class Parameters; } namespace bin2llvmir {
class FileImage;
class Abi;

struct MipsLeafEffects {
	bool known = false;
	uint32_t writes = 0;
	unsigned instructions = 0;
	std::map<uint32_t, uint32_t> words;
	std::vector<uint32_t> normalReturnPcs;
};

MipsLeafEffects inspectMipsLeaf(llvm::Module* module, FileImage* image,
		uint32_t entry);
std::optional<common::OriginalCalleeContexts> inspectOriginalMipsCallees(
	FileImage* image, const config::Parameters& parameters,
	const common::ReturnDisposition::Evidence& root);
void annotateMipsLeafCalls(llvm::Module* module, FileImage* image);
void simplifyMipsGuards(llvm::Module* module, Abi* abi);

} }
