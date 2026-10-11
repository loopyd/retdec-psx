# retdec-psx

`retdec-psx` is a PlayStation 1 focused fork of
[RetDec](https://github.com/avast/retdec), the LLVM-based machine-code decompiler.
It supplies the customized backend for the
[rz-psxdec](https://github.com/loopyd/rz-psxdec) Rizin plugin.

## Scope

The fork develops static recovery and C output for little-endian, 32-bit PS1 MIPS
code. Its customized decoder,
parameter and return recovery, and C writer support the plugin's bounded
original-only generation path.

The two repositories have separate roles:

| Repository | Sibling directory | Role |
| --- | --- | --- |
| [rz-psxdec](https://github.com/loopyd/rz-psxdec) | `rz-psxdec` | Rizin plugin and console commands |
| [retdec-psx](https://github.com/loopyd/retdec-psx) | `retdec-psx` | Customized RetDec backend linked into the plugin |

RetDec's upstream architecture and executable-format components remain in the
source tree. Their presence does not establish this fork's acceptance scope.

## Build

Build this backend through the sibling plugin's `rz-psxdec` target. The
[plugin build instructions](https://github.com/loopyd/rz-psxdec#build) give the
standalone Linux clone and CMake commands. They select the plugin's `dev` branch
and this backend's `master` branch, an existing Rizin installation, disposable
LLVM, Capstone and YARA source trees, and a local install prefix.

The plugin's dependency CMake file adds this source tree through
`RETDEC_SOURCE_DIR`. RetDec uses C++17 and CMake 3.13 or newer. Dependency URLs and
SHA-256 pins remain in [cmake/deps.cmake](cmake/deps.cmake). Local source selection
uses `LLVM_LOCAL_DIR`, `CAPSTONE_LOCAL_DIR` and `YARA_LOCAL_DIR`. The target enables
the RetDec component and links it into `rz-psxdec.so`. The plugin requires
`BUILD_BUNDLED_RETDEC=ON` and refuses an installed external backend.

The backend retains RetDec's 5.0 CMake package and `retdec::` APIs. Its displayed
identity is `retdec-psx 5.0` with its actual Git commit. The plugin's generated
version records both full source commits and rejects mismatched explicit
`RZ_PSXDEC_REVISION` or `RETDEC_PSX_REVISION` configure arguments.

Native test builds use the GoogleTest submodule at `deps/googletest/src`, pinned
to commit `90a443f9c2437ca8a682a1ac625eba64e1d74a8a`. Initialize it from the
backend repository before configuring with `RETDEC_TESTS=ON`:

```sh
git submodule update --init --recursive
```

CMake uses that checkout by default. `GOOGLETEST_LOCAL_DIR` can select another
complete local GoogleTest source tree. No GoogleTest archive download is needed.
To clear a previous source override, reconfigure with `-U GOOGLETEST_LOCAL_DIR`.

## Use

Load the plugin's verified `rz-psxdec.so` into Rizin with `RZ_NOPLUGINS=1` and
an explicit `-l` path, as shown in the
[plugin usage guide](https://github.com/loopyd/rz-psxdec#use).
`retdec-psx` is the backend source and libraries, with no separate Rizin plugin
DSO to load. `Lcj` reports the loaded `rz-psxdec` registration and its two-fork
build version.

The plugin exposes `pdz` for the current function, `pdzo` for code with offsets,
and `pdzar /absolute/workspace` for a fixed original-only request. Inspect `pdz?`
and `pdza?` in the loaded plugin for help. Interactive function decompilation
uses the current Rizin analysis and supplied context.

For original-only generation, the absolute workspace must contain the validated
request, original image bytes and fixed configuration expected by `pdzar`.

## Evidence limits

Generated C and inferred declarations require independent review. A successful
plugin invocation, compilation or preservation comparison does not prove original
bytes, calling contracts, associated data or placement. Unsupported instruction,
control or memory facts remain explicit obligations. Inferred machine values
alone do not establish source C declarations.

Original-only recovery can emit conditional C89 body proposals for supported
straight-line code with direct calls. It retains unresolved return, call, memory
and declaration facts. This path rejects indirect and exceptional control,
incomplete lowering and escaping stack use. Proposed signatures describe emitted
syntax and grant no original declaration authority.

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
