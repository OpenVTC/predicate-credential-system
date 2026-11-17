//! # Predicate credentials
//!
//! A Rust rendering of the *predicate credentials* (PCreds) of the accompanying paper: a helper
//! issues a credential to a user once enough credentialed users attest for it (for the
//! threshold policy: `k` distinct credentialed users), without learning who they are, and the
//! user then proves anonymously that it is credentialed or that a message comes from a
//! credentialed user. Security is defined by an ideal functionality, `F_PCreds`, which the
//! protocol `Π_PCreds` realizes; the protocol is generic over a credential base, a key-injective
//! PRF ("tag") and a NIZK.
//!
//! ## Paper-to-module map
//!
//! | Paper | Module |
//! |---|---|
//! | §3.1 random oracles, hash to group | [`hash`] |
//! | §3.3 sigma protocols, generalized Schnorr, Fiat-Shamir | [`sigma`] |
//! | §4.1 key-injective PRFs; §6.1 `Tag_DDH`, `Tag_DY` (and the short-key `Tag_LWR`) | [`kiprf`] |
//! | §4.2 credential bases; §6.2.1–6.2.2 `Σ-PS`, `Σ-BBS` | [`pcreds::pairing::base`] |
//! | §5.1 the ideal functionality `F_PCreds`; §5.2 the protocol `Π_PCreds` | [`pcreds`]: [`pcreds::Protocol`], generic over a [`pcreds::Backend`] |
//! | §5.2 the relations `R_Tag`, `R_att`, `R_iss`, `R_Possess` and the proof contexts | [`pcreds::pairing::PairingBackend`], [`pcreds::Protocol::issuance_context`] and the other contexts |
//! | §7.1 the sizes of attestations, requests and proofs | [`pcreds::codec`] (fixed-format encoding) |
//! | §6.2.3 the post-quantum instantiation: `Σ-vSIS`, the short-key `Tag_LWR`, lattice proofs (feature `lattice`) | `pcreds::lattice` (`LatticeBackend`, `base`), `kiprf::lwr`, `lattice` |
//!
//! Supporting modules: [`error`] (every `⊥` of the paper is an [`Error`]) and
//! [`serialization`] (the byte encoding of protocol objects, and JSON forms with the feature
//! `serde`). With the feature `jali`, the standalone lattice zero-knowledge library Jali is
//! re-exported as `jali`; with the feature `lattice`, the module `lattice` holds the shared
//! foundations of the post-quantum instantiation (the parameter set, the ring types, the random
//! oracles and Jali's embedded parameter and extraction sets), and `pcreds::lattice` its backend.
//!
//! ## Getting started
//!
//! [`pcreds::Protocol`] is the protocol; its methods are the steps of the interfaces of
//! `F_PCreds` (`Register`, `AttestationRequest`, `AttestationRequestResponse`,
//! `CredentialRequest`, `CredentialRequestResponse`, `Prove`, `Verify`). The module docs of
//! [`pcreds`] map the functionality to the methods and contain a complete flow (root admission,
//! attestations, issuance, a membership proof) for the paper's main instantiation
//! `Σ-PS + Tag_DDH` over BLS12-381 ([`pcreds::pairing::PairingProtocol`]); `tests/pcreds.rs`
//! and `tests/pcreds_correctness.rs` run it, with chaining, for every pair, and the benchmarks
//! print the sizes of all objects. The pairing-based bases `Σ-PS` and `Σ-BBS` are supported,
//! each with `Tag_DDH` or `Tag_DY`.
//!
//! The post-quantum instantiation is the second backend, `pcreds::lattice::LatticeBackend`
//! (feature `lattice`): the lattice base `Σ-vSIS` with an NTRU trapdoor (the sibling crate
//! `ntru-trapdoor`), the short-key LWR tag, and Jali proofs, under the same
//! [`pcreds::Protocol`]. An attestation is a proof of about 88 KB that takes seconds (about 7 s
//! to prove and 3.5 s to verify at one thread) and up to about 0.7 GB to prove or to verify.
//!
//! ## Conventions
//!
//! * The paper writes groups multiplicatively (`g^x`); the code is additive (`g * x`). Doc
//!   comments quote the paper's multiplicative formulas.
//! * Pairing-based code is generic over `E: ark_ec::pairing::Pairing`. The modules that name
//!   a concrete curve are [`hash::bls12_381`] (hash to curve), [`sigma::ciphersuite`] (the
//!   ciphersuite identifiers of the groups of BLS12-381 in the Fiat-Shamir tag) and
//!   [`pcreds::pairing::ietf`] (IETF BBS).
//! * Randomized algorithms take an explicit `rng: &mut R` with
//!   `R: RngCore + CryptoRng + ?Sized` (the traits of `ark_std::rand`, i.e. rand 0.8), so a
//!   trait object works as well as a concrete generator. There is no hidden system RNG.
//! * `⊥` is `Err(`[`Error`]`)` (or `None` for a tag evaluation). Verifiers return `bool` (or a
//!   `Result` naming the reason of a rejection, in the `check_*` methods) and do not panic on
//!   adversarial input.
//! * Decoding accepts the identity point and the zero scalar, so every non-degeneracy
//!   requirement of the paper (`t ≠ 1`, `σ'_1 ≠ 1`, ...) is an explicit check of the verifier of
//!   the corresponding relation, and so is the admissibility of a helper key
//!   ([`pcreds::Protocol::helper_key`]).
//! * The cargo feature `test-utils` (off by default, switched on for `cargo test` by the crate's
//!   dev-dependency on itself) exposes test helpers: the INSECURE oracle of `hash::testing`.
//!
//! ## Formulas
//!
//! Doc comments quote the paper's formulas as plain text (`g_1^usk`, `e(σ_1, X̃) = …`), which
//! reads in an editor and in every build of the documentation. In addition, the central
//! equations of a module are typeset under the heading "In formulas", e.g. in [`kiprf::ddh`],
//! [`kiprf::dy`] and [`sigma`]. Math is written inside code, inline as `` $`…`$ `` and
//! displayed as a code block with the language tag `math`, so that Markdown leaves the LaTeX
//! source alone. `cargo docs` (an alias defined in `.cargo/config.toml`) and docs.rs render it
//! with KaTeX through `docs/katex-header.html`; a plain `cargo doc` shows the LaTeX source
//! instead. A sample: $`t_{P \to Q} = \mathsf{Tag}(usk_P, x_Q)`$.
//!
//! ## Limitations
//!
//! * **Research artifact.** Not audited; see the README, "Security". Secret scalars are wiped
//!   on drop where this crate owns them, but field elements are `Copy` and temporaries may stay
//!   on the stack.
//! * **Plain Fiat-Shamir.** Proofs are Fiat-Shamir-compiled sigma protocols in the random-oracle
//!   model; knowledge extraction is by rewinding. The theorem of the paper assumes an online
//!   simulation-extractable NIZK, whose compilers are out of scope, as is the SNARK-based
//!   variant.
//! * **The post-quantum instantiation** (feature `lattice`) runs Jali, whose proofs are Jali's
//!   straight-line extractable proofs (Katsumata's transform, an argument that Jali gives as an
//!   outline in the classical random-oracle model), or with the feature `lattice-plain`
//!   Fiat-Shamir proofs with extraction by rewinding, and whose arithmetic, sampling and decoding
//!   run in variable time, as do `SampPre` and `TrapGen`. Its parameters meet the paper's base lemma
//!   (the request pseudorandom under MLWE, `s ≠ 0` extracted exactly), but its one-more
//!   assumption is not estimated at these parameters (`pcreds::lattice`, "What the paper claims,
//!   and what this code can claim").

// docs.rs builds with `--cfg docsrs` on nightly: feature-gated items get an "Available on crate
// feature …" badge. Stable builds never see the attribute.
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![warn(rust_2018_idioms, missing_debug_implementations)]
// Naming policy: in struct, trait and type-alias names the acronyms of schemes, primitives and
// assumptions keep the paper's capitalisation (PS, BBS, DY, DDH, LWR, KIPRF, FS for Fiat-Shamir):
// `BBS`, `DDH`, `KIPRF`, `FSProof`. The instantiations carry the bare acronym, without the
// paper's `Σ-` / `Tag_` prefix: the credential bases are `pcreds::pairing::{PS, BBS}`, the tags
// are `kiprf::{DDH, DY}`, so that a scheme reads
// `PairingProtocol<Bls12_381, PS, DDH<G1Projective, G1Hasher>>`. Function, module and file names
// stay snake_case / lowercase. clippy would prefer `Bbs`-style names, hence this allowance.
#![allow(clippy::upper_case_acronyms)]

pub mod error;
pub mod hash;
pub mod kiprf;
#[cfg(feature = "lattice")]
pub mod lattice;
pub mod pcreds;
mod sample;
pub mod serialization;
pub mod sigma;

pub use crate::error::Error;

/// Jali, the standalone lattice zero-knowledge library (<https://github.com/etairi/jali>),
/// re-exported with the feature `jali`. It is the proof backend of the post-quantum
/// instantiation (feature `lattice`).
#[cfg(feature = "jali")]
pub use jali;

/// Compiles and runs the Rust code blocks of `README.md` under `cargo test --doc`, so that the
/// examples shown there cannot drift away from the API. Not part of the library.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
pub struct ReadmeDoctests;

/// The same for the guide `docs/operating-a-helper.md`.
#[cfg(doctest)]
#[doc = include_str!("../docs/operating-a-helper.md")]
pub struct HelperGuideDoctests;
