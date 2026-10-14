# retdec-psx

`retdec-psx` is a PlayStation 1 fork of
[RetDec](https://github.com/avast/retdec), the LLVM-based machine-code decompiler.
It recovers little-endian, 32-bit PS1 MIPS code and supplies the backend for the
[rz-psxdec](https://github.com/loopyd/rz-psxdec) Rizin plugin. The plugin provides
the Rizin commands; this repository provides the decoder, analysis and C writer.

## Build

Build this backend through the sibling plugin's `rz-psxdec` target. Follow the
[plugin build instructions](https://github.com/loopyd/rz-psxdec#build) for the
standalone Linux clone and CMake commands. RetDec requires C++17 and CMake 3.13 or
newer. The plugin builds the backend from source and links it into `rz-psxdec.so`.

See [build integration](doc/original-analysis.md#build-integration) for local
dependency selection, source version checks and native test setup.

## Use

Load the verified `rz-psxdec.so` into Rizin with `RZ_NOPLUGINS=1` and an explicit
`-l` path, following the [plugin usage guide](https://github.com/loopyd/rz-psxdec#use).
This backend has no separate Rizin plugin to load. `Lcj` reports the loaded
`rz-psxdec` registration and its two-fork build version.

Use `pdz` to decompile the current function or `pdzo` to include offsets. Inspect
`pdz?` and `pdza?` for help. Interactive decompilation uses the current Rizin
analysis and supplied context.

`pdzar /absolute/workspace` runs original-only generation from a workspace
containing the validated request, original image bytes and fixed configuration.
See [original analysis](doc/original-analysis.md) for recovery reports, overlay
state, conditional C proposals and their evidence requirements.

## Evidence limits

Generated C and inferred declarations require independent checks of complete
original bytes, calling contracts, associated data and placement. A successful
plugin invocation or compilation does not establish those facts. Unsupported
instruction, control or memory facts remain explicit obligations, and conditional
proposals do not establish original C declarations or universal behavior.

Keep private original images, authored evaluator references and byte-bearing
captures local. Original-only generation withholds authored answers, names, maps
and source-specific compiler profiles.

## Provenance and license

This fork derives from [Avast RetDec](https://github.com/avast/retdec), copyright
2017 Avast Software. RetDec's code is licensed under the MIT license. See
[LICENSE](LICENSE), the [upstream documentation](https://github.com/avast/retdec/wiki)
and the [upstream contribution guidelines](https://github.com/avast/retdec/wiki/Contribution-Guidelines).

RetDec incorporates modified PeLib code. Avast's added modules use the MIT
license. Original PeLib sources retain the zlib/libpng license and Sebastian
Porst's copyright. See [LICENSE-PELIB](LICENSE-PELIB). Dependencies retain their
own licenses in [LICENSE-THIRD-PARTY](LICENSE-THIRD-PARTY).

Upstream RetDec acknowledges support from the Technology Agency of the Czech
Republic, ALFA Programme No. TA01010667. This fork preserves that provenance.
