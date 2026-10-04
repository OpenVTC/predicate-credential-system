# Predicate Credential System Documentation

Deeper material for the crate. The entry point is the repo root [`README.md`](../README.md); the
API documentation is generated from the sources (`cargo docs`, see the root README).

- [Operating a helper](./operating-a-helper.md) — what the operator of a helper has to decide
  and enforce around the library: predicates, policy, keys, root issuance; for the lattice
  instantiation also the helper's randomness, the issuance cap (stored ahead of issuance, one
  live instance per key), key rotation, memory and the work per requester.
- [Design notes](./design-notes.md) — how the implementation is put together and why, its
  limitations, and how it relates to the paper's boxes, the lattice instantiation included.
- [Encodings and interoperability](./encodings.md) — wire format, JSON (`serde` feature), IETF
  BBS bytes, and the normative bytes, oracles and contexts of the lattice instantiation.
- [Testing and benchmarks](./testing-and-benchmarks.md) — what the suites cover, the gates, the
  benchmarks, and the measured sizes and timings of the lattice instantiation.
- [OpenVTC integration](./openvtc-integration.md) — where the library fits into OpenVTC, how
  the integration could look, and what is missing on both sides.
- [`katex-header.html`](./katex-header.html) — loaded by rustdoc to render the formulas of the
  API documentation.
- [Jali](https://github.com/etairi/jali) — the standalone lattice zero-knowledge library that
  implements the [LNP22 port design](./lnp22-rust-port-plan.md), with its own tests and
  documentation.
