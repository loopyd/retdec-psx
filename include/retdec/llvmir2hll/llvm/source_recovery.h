#ifndef RETDEC_LLVMIR2HLL_LLVM_SOURCE_RECOVERY_H
#define RETDEC_LLVMIR2HLL_LLVM_SOURCE_RECOVERY_H

#include "retdec/llvmir2hll/support/smart_ptr.h"
namespace llvm { class Module; }
namespace retdec {
namespace config { class Config; }
namespace llvmir2hll {
class Module;
void recoverPointerExpressions(llvm::Module &module, const config::Config &config);
void recoverSourceSignatures(ShPtr<Module> module, const config::Config &config);
void applyDeclaredAccessQualifiers(ShPtr<Module> module, const config::Config &config);
}
}
#endif
