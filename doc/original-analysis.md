# PS1 original analysis

This reference describes the backend's build integration, original-only recovery
reports, static image state and conditional C proposals. Use the sibling
[plugin guide](https://github.com/loopyd/rz-psxdec#use) for Rizin loading and
commands. Generated C and inferred declarations require independent review;
plugin execution or compilation alone does not establish original bytes, calling
contracts, associated data or placement. Upstream architecture and executable-format
components remain in the source tree; their presence does not establish this
fork's acceptance scope.

## Build integration

The [plugin build instructions](https://github.com/loopyd/rz-psxdec#build) select
the plugin's `dev` branch and this backend's `master` branch, an existing Rizin
installation, disposable LLVM, Capstone and YARA source trees, and a local install
prefix. Keep the repositories in sibling directories named `rz-psxdec` and
`retdec-psx`.

The plugin's dependency CMake file adds this source tree through
`RETDEC_SOURCE_DIR`. RetDec uses C++17 and CMake 3.13 or newer. Dependency URLs and
SHA-256 pins remain in [cmake/deps.cmake](../cmake/deps.cmake). Local source selection
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

## Original-only recovery

Original register facts evaluate `SLTI` and `SLTIU` when the source is constant.
Both sign-extend the immediate before the signed or unsigned 32-bit comparison.
The result retains its input dependencies and establishes no entry or memory facts.

Original-only analysis can bind a checked runtime entry observation after native
discovery matches its function identity and original instructions. Native stores,
calls, joins and delayed loads recover saved-register relationships within a
fixed RAM frame. The `scopedRestoration` report retains its entry and execution
conditions. It does not establish universal control, effects or C declarations.
An all-exit incoming-link restoration can support assigned register-2 flow into a
direct caller under those retained conditions. Conditional call flow still
refuses ordinary C body admission.

Without an entry observation, original-only analysis can recover canonical
full-word frame saves and restores across an acyclic original control-flow graph.
The `symbolicFrame` report can retain caller register identities and assigned
register-2 flow at a direct call. It requires an aligned frame wholly in ordinary
RAM, frame writes disjoint from fetched code, stable mapping and instructions,
normal accesses, settled load delays and no external interference. Those
conditions remain unresolved. Physical frame writes stay in the access report,
and conditional frame flow refuses ordinary C body admission.

Direct-call evidence can include an `entryPath` diagnostic derived from settled
caller constants and the callee's original instructions. It records one complete
finite path, branch operands and delay slots. Loads produce unknown values with
MIPS-I timing. Unknown branches, reachable calls, loops and unsupported instructions
refuse this diagnostic, as do observed entry states and copied instruction scopes.
The generic callee summary and call contract remain authoritative. This path
establishes no memory effects, stack separation, return target or C declaration.
It assumes original fetched words, normal accesses and no external interference.
Writes that may overlap code and exception behavior remain unresolved.

The `entry-register-relative-first-use/v1` address report describes an operand's
first reach from the original entry through checked instructions and call
bindings. It records the entry, operand boundary, arithmetic evidence and crossed
calls. Recovery refuses any path with an unproved control crossing before that
operand, including branches that bypass it. Later reentry remains unresolved.
The report retains conditional frame obligations and establishes no ordinary
memory effects, object declarations or C admission.

## Overlay state

The backend owns ordered PS1 image mounts through
[`loader::PsxOverlayManager`](../include/retdec/loader/loader/psx_overlay_image.h).
Its immutable [`PsxMemoryContext`](../include/retdec/common/psx_memory.h) records
original-file hashes, payload slices, load metadata and visible byte ownership.
Later mounts replace overlaps. Dismounting restores earlier static mappings.
Invalid batches preserve the previous context. PS1 RAM aliases resolve to the
same owner.

The decoder and data readers use one composed native image. Original-only direct
callee discovery records bounded instruction-derived nodes separately from
reviewed function extents. Context changes select different decompilation caches.
See the [plugin overlay commands](https://github.com/loopyd/rz-psxdec#overlay-state)
for metadata fields and mount, dismount and inspection commands.

An explicit static mount state does not prove historical runtime residency or
original C declarations. These remain evidence requirements for cross-image
decompilation.

## Evidence and C proposals

Fixed-address evidence distinguishes uninterrupted entry prefixes from unique,
load-delay-safe constant chains in the complete original control flow. Initial
file bytes identify static backing from the active image owner. Object extents,
qualifiers, runtime contents and memory effects remain separate obligations.

Original-only summaries and call contracts report `noMemoryWrites` separately
from overall `effects`. A complete fact requires complete native control,
supported instructions, backed ordinary RAM reads and qualified no-write callees.
It covers normal sequential execution. It does not prove stack storage validity,
object contents, C declarations or semantic equivalence.

Call-free original-only bodies with an observed byte access inside a 16- or 32-bit
scalar span may use conditional scalar address views. Accesses require fixed,
aligned RAM addresses and complete backing from active images. Overlapping bytes
use character pointers into the same scalar. The `originalAddressViews` output
records emitted symbols, addresses, widths and original access PCs for
measurement bindings.
These views provide no historical object declaration, initializer, qualifier or
runtime-content proof.

Supported ordinary-body proposals can also bind distinct fixed byte stores to
independent external byte symbols. Native recovery checks the original and IR
memory and direct-call inventories, including the frame's erased saved-link
accesses. Each write view owns one backed byte store. Its declaration has no
initializer, and the original control, call, object and effect obligations remain.

Original-only recovery can emit conditional C89 body proposals for supported
straight-line code with direct calls. It retains unresolved return, call, memory
and declaration facts. This path rejects indirect and exceptional control,
incomplete lowering and escaping stack use. Proposed signatures describe emitted
syntax and grant no original declaration authority.

Call-free bodies with complete direct control flow can also produce a conditional
five-word C89 carrier for one incoming word at `sp+16`. This requires an unchanged
stack pointer and a checked load before any branch or store. The carrier assumes
the O32 word layout and a valid, aligned entry stack slot whose contents stay
stable until the load. Its mechanical signature does not establish the original
C parameters or return declaration; all original obligations remain intact.

Keep private original images, authored evaluator references and byte-bearing
captures local. Original-only generation withholds authored answers, names, maps
and source-specific compiler profiles.
