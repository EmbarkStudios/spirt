<!-- markdownlint-disable blanks-around-headings blanks-around-lists no-duplicate-heading -->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- NOTE(eddyb) sections from the original template:

### Added
- New features go here in a bullet list

### Changed
- Changes to existing functionality go here in a bullet list

### Deprecated
- Mark features soon-to-be removed in a bullet list

### Removed
- Features that have been removed in a bullet list

### Fixed
- Bug fixes in a bullet list

### Security
- Changes/fixes related to security vulnerabilities in a bullet list

-->

<!-- next-header -->
## [Unreleased] - ReleaseDate
*Initial public release of SPIR-T for minimal Rust-GPU integration.*
### Added
- Conversions from/to SPIR-V (`spv::lower`/`spv::lift`).
- Control-flow structurizer, from CFGs to SPIR-T's stricter structured control-flow.
- Pretty-printer with (styled and hyperlinked) HTML output.

<!-- next-url -->
[Unreleased]: https://github.com/EmbarkStudios/spirt/compare/0.0.0...HEAD
