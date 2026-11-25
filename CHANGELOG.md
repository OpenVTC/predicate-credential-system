# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.1](https://github.com/OpenVTC/predicate-credential-system/compare/predicate-credential-system-v0.1.0...predicate-credential-system-v0.1.1) - 2026-11-25

Maintenance release on the 0.1 line. No API or behaviour change from 0.1.0.

### Fixed

- *(deps)* take `url` 2.5.9 in `Cargo.lock` for [RUSTSEC-2026-0592](https://rustsec.org/advisories/RUSTSEC-2026-0592.html).
  `url` is not a dependency of the published crate (it reaches the workspace only through the
  unpublished `demo/` prototype's `vta-sdk`), so consumers of `predicate-credential-system` were
  never exposed through this crate.

### Other

- *(release)* mark the unpublished `pcs-vetting-prototype` as `publish = false` in
  `release-plz.toml`, so release-plz no longer refuses to run.

## [0.1.0](https://github.com/OpenVTC/predicate-credential-system/releases/tag/predicate-credential-system-v0.1.0)

- Initial release.
