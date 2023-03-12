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
[Unreleased]: https://github.com/EmbarkStudios/spirt/compare/0.1.0...HEAD
<!-- HACK(eddyb) `0.0.0` doesn't exist as a "tag before the initial commit", but
     the commit hash referenced here is the newest from `opensource-template`,
     that predates `0.1.0`, i.e. the `opensource-template` parent of the merge
     commit that combined the two repositories' history, which makes it quite
     suitable for a comparison point, as GitHub will dutifully list all commits
     that don't come from `opensource-template`, even the initial commit itself!
-->
[0.1.0]: https://github.com/EmbarkStudios/spirt/compare/c5d63c6974d03e1495eba2c72ff403a246586a40...0.1.0
