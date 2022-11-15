<!-- Allow this file to not have a first line heading -->
<!-- markdownlint-disable-file MD041 no-emphasis-as-heading -->

<!-- inline html -->
<!-- markdownlint-disable-file MD033 -->

<div align="center">

# `SPIR-🇹`

**⋯🢒 🇹arget 🠆 🇹ransform 🠆 🇹ranslate ⋯🢒**

[![Embark](https://img.shields.io/badge/embark-open%20source-blueviolet.svg)](https://embark.dev)
[![Crates.io](https://img.shields.io/crates/v/spirt.svg)](https://crates.io/crates/spirt)
[![Docs](https://docs.rs/spirt/badge.svg)](https://docs.rs/spirt)
[![Git Docs](https://img.shields.io/badge/git%20main%20docs-published-blue)](https://embarkstudios.github.io/spirt/spirt/index.html)
[![dependency status](https://deps.rs/repo/github/EmbarkStudios/spirt/status.svg)](https://deps.rs/repo/github/EmbarkStudios/spirt)
[![Build status](https://github.com/EmbarkStudios/spirt/workflows/CI/badge.svg)](https://github.com/EmbarkStudios/spirt/actions)
</div>

**SPIR-🇹** is a research project aimed at exploring shader-oriented IR designs derived from SPIR-V, and producing a framework around such an IR to facilitate advanced compilation pipelines, beyond what existing SPIR-V tooling allows for.

Such a need arose in the [Rust-GPU](https://github.com/EmbarkStudios/rust-gpu) project, which requires a variety of legalization passes to turn general-purpose (Rust<sup>1</sup>) code operating on *untyped* memory, into GPU-friendly direct data-flow.
Our goal is to replace the existing [Rust-GPU](https://github.com/EmbarkStudios/rust-gpu) SPIR-V legalizations passes with **SPIR-🇹** equivalents - but even more imporantly, **SPIR-🇹** should allow writing much more powerful legalization/optimization passes, that would've been unfathomable<sup>2</sup> for direct SPIR-V manipulation.

---

<sub><sup>1</sup> Rust is not unique in its needs here, and more languages (or IRs) could eventually make use of such a framework, but the initial design and implementation work has focused on [Rust-GPU](https://github.com/EmbarkStudios/rust-gpu)</sub>

<sub><sup>2</sup> not outright impossible, but requiring excessive development/maintenance cost, having to constantly balance correctness and power (more conservative passes are easier to trust), etc.</sub>

## Status

🚧 *This project is in active design and development, many details can and will change* 🚧

### Non-goals (at least in the short term)

* supporting the ("OpenCL") `Kernel` dialect of SPIR-V
  * `Kernel` SPIR-V is much closer to LLVM IR, than `Shader` SPIR-V, and
    as such tooling oriented around LLVM is more likely to be a better fit
* textual syntax that can be parsed back
  * i.e. the pretty-printer output is purely a visualization

### Designed and implemented so far

<table>
<tr><td width="50%">

**IR datatypes**:
* allowing near-arbitrary SPIR-V instructions for any unrecognized opcodes
  * IDs are replaced with interned/"entity" handles (see below)
* interning for attributes (decorations & similar), types and constants
  * i.e. automatic deduplication, efficient indexing, and no concept of "definition"
    (only uses of interned handles can lead to a module being considered to contain a specific type/constant)
* "entity" system for e.g. definitions in a module, instructions in a function, etc.
  * disallows iteration in favor of/forcing the use of efficient indexing
* structured control-flow "regions" inspired by RVSDG, stricter than SPIR-V
  (see `ControlRegionDef`'s docs for more details)

</td><td>

**Framework utilities**:
* `visit`/`transform`: immutable/mutable IR traversal
* `print`: pretty-printer with (syntax-highlighted and hyperlinked) HTML output

**Passes (to/from/on SPIR-🇹)**:
* `spv::lower`: "lowering" from SPIR-V, normalizing away many irrelevant details
  * lossy for some relevant details (these are bugs, though many are non-semantic so lower priority)
* `spv::lift`: "lifting" back up to SPIR-V, making arbitrary choices where necessary
  * comparable to e.g. generating GLSL syntax from SPIR-V, just one level down
* `cfg::Structurizer`: (re)structurization, from arbitrary control-flow to the stricter structured "regions"
* `passes::link`: mapping (linkage) imports to relevant exports

</td></tr></table>

## Simple example (with non-trivial control-flow)

<table>
<tr><td>

**GLSL** ([`for-loop.vert.glsl`](tests/data/for-loop.vert.glsl))
```glsl
#version 450
out int output0;
void main() {
    int o = 1;
    for(int i = 1; i < 10; i++)
    	  o *= i;
    output0 = o;
}
```
**WGSL** ([`for-loop.wgsl`](tests/data/for-loop.wgsl))
<!--FIXME(eddyb) this is WGSL but GitHub can't syntax-highlight it yet -->
```glsl
@vertex
fn main() -> @location(0) i32 {
    var o: i32 = 1;
    for(var i: i32 = 1; i < 10; i++) {
    	o *= i;
    }
    return o;
}
```
</td><td>

<!--FIXME(eddyb) link to GH pages having a `.spirt.html` render of this -->
**SPIR-🇹**:
<!--FIXME(eddyb) this is SPIR-T but GitHub can't syntax-highlight it (ever?) -->
```cxx
#{
  OpDecorate<Decoration.Flat>,
  OpDecorate<Decoration.Location(0)>,
}
global_var0 in StorageClass.Output: s32

func0() -> OpTypeVoid {
  loop(v5: s32 <- 1s32, v6: s32 <- 1s32) {
    v2 = OpSLessThan(v6, 10s32): bool
    (v7: bool, v8: s32, v9: s32) = if v2 {
      v3 = OpIMul(v5, v6): s32
      v4 = OpIAdd(v6, 1s32): s32
      (true, v3, v4)
    } else {
      OpStore(&global_var0, v5)
      (false, OpUndef: s32, OpUndef: s32)
    }
    (v8, v9) -> (v5, v6)
  } while v7
}
```
</td><td>

**SPIR-V** ([`for-loop.wgsl.spvasm`](tests/data/for-loop.wgsl.spvasm))
<!--FIXME(eddyb) this is SPIR-V assembly but GitHub can't syntax-highlight it yet -->
```llvm
%typeof_output0 = OpTypePointer Output %i32
%output0 = OpVariable %typeof_output0 Output

%typeof_main = OpTypeFunction %void
%main = OpFunction %void None %typeof_main
  %entry = OpLabel
    OpBranch %bb0
  %bb0 = OpLabel
    OpBranch %bb1
  %bb1 = OpLabel
    %o = OpPhi %i32 %1_i32 %bb0 %o_next %bb5
    %i = OpPhi %i32 %0_i32 %bb0 %i_next %bb5
    OpLoopMerge %bb6 %bb5 None
    OpBranch %bb2
  %bb2 = OpLabel
    %cond = OpSLessThan %bool %i %10_i32
    OpSelectionMerge %bb4 None
  OpBranchConditional %cond %bb4 %bb3
  %bb3 = OpLabel
    OpBranch %bb6
  %bb4 = OpLabel
    %o_next = OpIMul %i32 %o %i
    OpBranch %bb5
  %bb5 = OpLabel
    %i_next = OpIAdd %i32 %i %1_i32
    OpBranch %bb1
  %bb6 = OpLabel
    OpStore %output0 %o
    OpReturn
OpFunctionEnd
```
</td></tr></table>

## GPU (shader) IR landscape overview
*(and the vision of how **SPIR-🇹** fits into it)*

![](docs/landscape.svg)

The distinction being made here is between:
* **Interchange IRs** (standards that many tools can use to interoperate)
  * SPIR-V was very much intended as such a standard
    (outside of the GPU space, wasm is also a great example)
  * they only need to encode the right concepts, not straying too far away from what tools understand, but the design effort is often oriented around being a "serialization" format
* **Compiler IRs** (non-standard implementation details of compilers)
  * LLVM is quite well-known, but Mesa's NIR is even closer to **SPIR-🇹**
    (both being shader-oriented, and having similar specialized choices of e.g. handling control-flow)
  * these _have to_ handle legalization/optimization passes quite well, and in general a lot of on-the-fly transformations - as their main purpose is to _expedite_ such operations
  * this is where **SPIR-🇹** sits, as a kind of "relative"/dialect of SPIR-V, but making trade-offs in favor of the "intra-compiler" usage

## Contribution

[![Contributor Covenant](https://img.shields.io/badge/contributor%20covenant-v1.4-ff69b4.svg)](CODE_OF_CONDUCT.md)

We welcome community contributions to this project.

Please read our [Contributor Guide](CONTRIBUTING.md) for more information on how to get started.
Please also read our [Contributor Terms](CONTRIBUTING.md#contributor-terms) before you make any contributions.

Any contribution intentionally submitted for inclusion in an Embark Studios project, shall comply with the Rust standard licensing model (MIT OR Apache 2.0) and therefore be dual licensed as described below, without any additional terms or conditions:

### License

This contribution is dual licensed under EITHER OF

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

For clarity, "your" refers to Embark or any other licensee/user of the contribution.
