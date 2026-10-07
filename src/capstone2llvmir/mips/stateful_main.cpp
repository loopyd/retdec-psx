#include "retdec/capstone2llvmir/mips/stateful.h"
#include <fstream>
#include <iostream>
#include <iterator>
#include <limits>
#include <vector>
#include <llvm/IR/Module.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/InitializePasses.h>
#include <llvm/PassRegistry.h>
#include "retdec/utils/io/log.h"
#include "retdec/config/config.h"
#include "retdec/llvmir2hll/llvmir2hll.h"
#include <llvm/Support/raw_ostream.h>

int main(int argc, char** argv)
{
    bool biosBus = false, emitC = false;
    bool valid = argc >= 4;
    for (int i = 4; i < argc; ++i) {
        std::string option = argv[i];
        if (option == "--bios-bus" && !biosBus) biosBus = true;
        else if (option == "--emit-c" && !emitC) emitC = true;
        else valid = false;
    }
    if (!valid) {
        std::cerr << "Usage: retdec-mips-stateful RAW_CODE BASE_ADDRESS FUNCTION_NAME [--bios-bus] [--emit-c] > output\n"
                  << "ABI v2: unsigned step(unsigned state[73], unsigned char ram[2097152]);\n"
                  << "--bios-bus: ABI v3 step(state[75], ram[2097152], rom[524288], scratch[1024]).\n";
        return 2;
    }
    try {
        std::string address = argv[2], name = argv[3];
        std::size_t consumed = 0;
        auto base = std::stoull(address, &consumed, 0);
        if (address.empty() || address.front() == '-' || consumed != address.size()
                || base > std::numeric_limits<uint32_t>::max() || name.empty()
                || name.find_first_not_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_") != std::string::npos
                || (name.front() >= '0' && name.front() <= '9'))
            throw std::invalid_argument("invalid base address or function name");
        std::ifstream input(argv[1], std::ios::binary | std::ios::ate);
        if (!input || input.tellg() <= 0 || input.tellg() > 65536)
            throw std::invalid_argument("input must be 1..65536 bytes of raw little-endian MIPS code");
        std::vector<uint8_t> bytes(static_cast<std::size_t>(input.tellg()));
        input.seekg(0);
        if (!input.read(reinterpret_cast<char*>(bytes.data()), bytes.size()))
            throw std::runtime_error("cannot read input");
        llvm::LLVMContext context;
        llvm::Module module(biosBus ? "mips-stateful-v3" : "mips-stateful-v2", context);
        retdec::capstone2llvmir::translateMips32Stateful(module,
                bytes.data(), bytes.size(), static_cast<uint32_t>(base), name, biosBus);
        if (emitC) {
            auto& registry = *llvm::PassRegistry::getPassRegistry();
            llvm::initializeLoopInfoWrapperPassPass(registry);
            llvm::initializeScalarEvolutionWrapperPassPass(registry);
            retdec::utils::io::Log::set(retdec::utils::io::Log::Type::Info,
                    std::make_unique<retdec::utils::io::Logger>(std::cerr, false));
            retdec::config::Config config;
            config.parameters.setIsBackendKeepLibraryFuncs(true);
            config.parameters.setIsBackendNoTimeVaryingInfo(true);
            config.parameters.setIsBackendNoVarRenaming(true);
            std::string output;
            {
                llvm::legacy::PassManager passes;
                auto* writer = new retdec::llvmir2hll::LlvmIr2Hll(&config);
                writer->setOutputString(&output);
                passes.add(writer);
                passes.run(module);
            }
            if (output.empty()) throw std::runtime_error("C emission produced no output");
            llvm::outs() << output;
        } else module.print(llvm::outs(), nullptr);
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
