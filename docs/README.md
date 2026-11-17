# Predicate Credentials Documentation

Deeper material for the crate. The entry point is the repo root [`README.md`](../README.md); the
API documentation is generated from the sources (`cargo docs`, see the root README). The guides
describe the protocol module `pcreds` (`Π_PCreds` of the paper, §5) with its pairing-based
backend and, in a section of their own, its lattice backend (feature `lattice`).

- [Operating a helper](./operating-a-helper.md): what the operator of a helper decides and
  enforces around the library: the policy `Pol_k` and the optional limit on attestations, root admission,
  what the helper learns, the durability of the set `I` of issued identifiers (`IssuanceStore`),
  restoring a helper, one key per deployment, sessions and contact names; for the lattice
  instantiation also the helper's randomness, the issuance cap, one live instance per key,
  rotation, memory and the work per requester. Its examples are compiled and run as doctests.
- [Design notes](./design-notes.md): the design of `pcreds` and why: the `Backend` trait, the
  type-state hardening (`HelperKey`, `PendingAttestation`, `EvaluatedRequest`), the binding to a
  deployment, the issuance record, the contexts, the tags and bases, what was removed with the
  earlier construction and why, the limitations; then the lattice backend: its objects, its
  relations and parameter sets, and what it does not meet of the paper.
- [Encodings and interoperability](./encodings.md): the compact fixed format of the messages, the
  canonical encodings, the oracles and proof contexts byte by byte, the JSON forms (`serde`), IETF
  BBS (`pcreds::pairing::ietf`), and the normative bytes and oracles of the lattice
  backend.
- [Testing and benchmarks](./testing-and-benchmarks.md): what the suites cover, how to run them,
  the checks a change has to pass, what each benchmark function measures, reproducibility, and
  the measured sizes and timings of the lattice instantiation.
- [OpenVTC integration](./openvtc-integration.md): where the library fits into OpenVTC, the
  flows, what the client stores, the JSON messages, the errors to map, and what is missing on
  both sides.
- [`katex-header.html`](./katex-header.html): loaded by rustdoc to render the formulas of the API
  documentation.
- [Jali](https://github.com/etairi/jali): the standalone lattice zero-knowledge library that
  implements the [LNP22 port design](./lnp22-rust-port-plan.md), with its own tests and
  documentation.
