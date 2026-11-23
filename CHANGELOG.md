# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.0](https://github.com/OpenVTC/predicate-credential-system/compare/predicate-credential-system-v0.1.0...predicate-credential-system-v0.2.0) - 2026-11-23

### Added

- [**breaking**] move to pcreds with Jali 0.3.0 and application contexts

### Fixed

- *(deps)* url 2.5.9 for RUSTSEC-2026-0592 ([#6](https://github.com/OpenVTC/predicate-credential-system/pull/6))
- *(pcreds)* separate empty and absent attestation contexts in π_iss
- *(demo)* address review findings on the pcreds port

### Other

- *(deps)* take affinidi-did-resolver-cache-sdk 0.8.40 — a deactivated did:webvh no longer resolves
