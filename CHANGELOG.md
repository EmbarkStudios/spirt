<!-- markdownlint-disable blanks-around-headings blanks-around-lists no-duplicate-heading -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- NOTE(eddyb) sections from the original template:

### Added ⭐
- New features go here in a bullet list

### Changed 🛠
- Changes to existing functionality go here in a bullet list

### Deprecated 🚧
- Mark features soon-to-be removed in a bullet list

### Removed 🔥
- Features that have been removed in a bullet list

### Fixed 🩹
- Bug fixes in a bullet list

### Security 🔐
- Changes/fixes related to security vulnerabilities in a bullet list

-->

<!-- next-header -->

## [Unreleased] - ReleaseDate

### Changed 🛠
- [PR#48](https://github.com/EmbarkStudios/spirt/pull/48) changed CFG structurization
  from "maximal loops" to "minimal loops" (computed using Tarjan's SCC algorithm),
  and added `OpLoopMerge` support on top (by extending a "minimal loop" as needed)

## [0.3.0] - 2023-07-25

### Added ⭐
- [PR#45](https://github.com/EmbarkStudios/spirt/pull/45) added the ability to
  pretty-print `OpExtInst`s (SPIR-V "extended instructions") using official
  `extinst.*.grammar.json` descriptions and/or custom ones (registered via `Context`)

### Changed 🛠
- [PR#43](https://github.com/EmbarkStudios/spirt/pull/43) tweaked several pretty-printing
  details to improve visual cohesion ("named arguments" in `module.{dialect,debuginfo}`)
  and ergonomics (multi-line string literals, HTML entities for anchor escaping,
  hover on multi-version table cells to disable "no changes" desaturation/dimming)
- [PR#36](https://github.com/EmbarkStudios/spirt/pull/36) started using `OpName`s
  in pretty-printing, to replace the `T1`/`F2`/`v3` "anonymous" style, when unambiguous
- [PR#40](https://github.com/EmbarkStudios/spirt/pull/40) increased the pretty-printed
  HTML `font-size` from `15px` to `17px`, to improve readability
- [PR#39](https://github.com/EmbarkStudios/spirt/pull/39) shortened pretty-printed names
  like `type2`/`func3`/etc. to `T2`/`F3`/etc. (with e.g. `type T2 = ...` style definitions)
- [PR#38](https://github.com/EmbarkStudios/spirt/pull/38) split off `print::Node::Root`,
  allowing "roots" and "non-root nodes" to have different APIs, and dynamic dispatch
  to be limited to "roots" (as "non-root nodes" are a small finite set of types)
- [PR#35](https://github.com/EmbarkStudios/spirt/pull/35) abandoned the custom
  `#{A, B, C}` "attribute set" style in favor of Rust-like `#[A]` `#[B]` `#[C]`
  (and always printing them inline, without any `attrs123` shorthands)
- [PR#33](https://github.com/EmbarkStudios/spirt/pull/33) replaced the `spv.OpFoo<imms>(IDs)`
  style of pretty-printing with `spv.OpFoo(A: imm, B: ID, C: imm, ...)` (unified parenthesized
  list of operands, with deemphasized operand names in `foo:` "named arguments" style)
- [PR#28](https://github.com/EmbarkStudios/spirt/pull/28) moved two `DataInstDef`
  fields (`kind` and `output_type`) to `DataInstForm`, a new interned type
- [PR#30](https://github.com/EmbarkStudios/spirt/pull/30) replaced the old `spv-lower-dump`
  example (which only dumped plaintext, not HTML) with a more useful `spv-lower-print` one

### Fixed 🩹
- [PR#34](https://github.com/EmbarkStudios/spirt/pull/34) fixed `OpTypePointer`s being
  spuriously printed as dependencies of `GlobalVarDecl`/`PtrToGlobalVar` (neither of
  which actually print the pointer type), and added a CI check for `README.md` examples
- [PR#37](https://github.com/EmbarkStudios/spirt/pull/37) fixed pretty-printing layout
  accuracy regarding line widths (by tracking `font-size`-aware "fractional columns"),
  and raised the maximum line width back up to `120` columns
- [PR#27](https://github.com/EmbarkStudios/spirt/pull/27) fixed some pretty-printing issues
  in the initial `Attr::Diagnostics` implementation (`BUG` paths and `/* ... */` indentation)

## [0.2.0] - 2023-04-21

### Added ⭐
- [PR#24](https://github.com/EmbarkStudios/spirt/pull/24) added `qptr` ("quasi-pointer") type
  and associated passes to destroy and recreate pointer-related type information
  (see [PR#24](https://github.com/EmbarkStudios/spirt/pull/24) for a much more detailed overview)
- [PR#22](https://github.com/EmbarkStudios/spirt/pull/22) added `Diag` and `Attr::Diagnostics`,
  for embedding diagnostics (errors or warnings) in SPIR-T itself
- [PR#18](https://github.com/EmbarkStudios/spirt/pull/18) added anchor-based alignment
  to multi-version pretty-printing output (the same definitions will be kept on
  the same lines in all columns, wherever possible, to improve readability)

### Changed 🛠
- [PR#26](https://github.com/EmbarkStudios/spirt/pull/26) allowed using `OpEmitMeshTasksEXT` as a terminator (by hardcoding it as `Control-Flow`)
- [PR#25](https://github.com/EmbarkStudios/spirt/pull/25) updated SPIRV-headers from 1.5.4 to 1.6.1
- [PR#21](https://github.com/EmbarkStudios/spirt/pull/21) tweaked pretty-printing
  styles around de-emphasis (shrinking instead of thinning, for width savings),
  and SPIR-V ops/enums (via de-emphasized `spv.` prefix and distinct orange color)

## [0.1.0] - 2022-12-16
*Initial public release of SPIR-T for minimal Rust-GPU integration.*
### Added ⭐
- Conversions from/to SPIR-V (`spv::lower`/`spv::lift`).
- Control-flow structurizer, from CFGs to SPIR-T's stricter structured control-flow.
- Pretty-printer with (styled and hyperlinked) HTML output.

<!-- next-url -->
[Unreleased]: https://github.com/EmbarkStudios/spirt/compare/0.3.0...HEAD
[0.3.0]: https://github.com/EmbarkStudios/spirt/compare/0.2.0...0.3.0
[0.2.0]: https://github.com/EmbarkStudios/spirt/compare/0.1.0...0.2.0
<!-- HACK(eddyb) `0.0.0` doesn't exist as a "tag before the initial commit", but
     the commit hash referenced here is the newest from `opensource-template`,
     that predates `0.1.0`, i.e. the `opensource-template` parent of the merge
     commit that combined the two repositories' history, which makes it quite
     suitable for a comparison point, as GitHub will dutifully list all commits
     that don't come from `opensource-template`, even the initial commit itself!
-->
[0.1.0]: https://github.com/EmbarkStudios/spirt/compare/c5d63c6974d03e1495eba2c72ff403a246586a40...0.1.0
