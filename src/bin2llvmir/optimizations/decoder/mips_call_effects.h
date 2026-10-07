#pragma once

#include <cstdint>

namespace llvm { class Module; }
namespace retdec { namespace bin2llvmir {
class FileImage;
class Abi;

struct MipsLeafEffects {
	bool known = false;
	uint32_t writes = 0;
	unsigned instructions = 0;
};

MipsLeafEffects inspectMipsLeaf(llvm::Module* module, FileImage* image,
		uint32_t entry);
void annotateMipsLeafCalls(llvm::Module* module, FileImage* image);
void simplifyMipsGuards(llvm::Module* module, Abi* abi);

} }
