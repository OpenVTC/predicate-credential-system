# Predicate Credential System (PCS)

[![Rust](https://img.shields.io/badge/rust-1.95.0%2B-blue.svg?maxAge=3600)](https://github.com/etairi/predicate-credential-system)

Rust implementation of the *predicate credential system* (PCS): a helper issues a credential to
a user who proves, in zero knowledge, that it holds attestations from `k` pairwise-distinct
credentialed users, none of whom is the user itself. Built on [arkworks](https://arkworks.rs) 0.6.

> **Research artifact.** Not audited. See [Security](#security).

The standalone [Jali library](https://github.com/etairi/jali) implements lattice-based
zero-knowledge proofs, currently the LNP22 proof stack described in the
[Rust port plan](./docs/lnp22-rust-port-plan.md). It lives in its own repository; this crate
depends on it as a git dependency (feature `jali`), and its post-quantum instantiation (feature
`lattice`) proves its relations with it. See Jali's README for its status and limits.

## Overview

`predicate-credential-system` (imported as `predicate_credential_system`) follows the paper's
modular construction: generalized Schnorr proofs, a key-injective PRF (the *tag*) and a
*credential base* are combined by one generic protocol. Every public value of a user is a tag
under its secret key, which is what makes attesters countable without being identifiable:

```math
id = \mathsf{Tag}(usk, c_0), \qquad T_j = \mathsf{Tag}(usk_j, H_0(id)), \qquad T_0 = \mathsf{Tag}(usk, H_0(id))
```

A proof for the threshold `k` carries `k` attestations whose tags `T_j` are pairwise distinct
and differ from the requester's own `T_0`. A scheme is a choice of pairing, credential base, tag
and (optionally) attribute policy:

```rust,ignore
type Scheme = PCS<Bls12_381, PS<Bls12_381>, DDH<G1Projective, G1Hasher>>;
```

The post-quantum instantiation is `LatticePCS` (feature `lattice`): the lattice credential base
`Σ-vSIS` on an NTRU trapdoor, the short-key LWR tag, and [Jali](https://github.com/etairi/jali)
proofs in place of the sigma protocols, behind the same trait.

## Modules

| Module | Description |
|--------|-------------|
| `pcs` | The construction (paper §5.1): trait `PredicateCredentialSystem` (the ten algorithms of §4) and its implementation `PCS<E, B, T, P>`, predicates and `EncPred`, attribute policies, root credentials, the fixed-format codec that reproduces the paper's sizes. With `lattice`, `pcs::lattice::LatticePCS<P>`, the post-quantum instantiation (§5.2), with its relations, contexts and codec. |
| `cred` | Credential bases (§3.2): `PS` (Pointcheval-Sanders, the main instantiation), `BBS`, `EQ` (SPS-EQ) and the designated-verifier `MAC`, behind the traits `CredentialBase` / `SigmaFriendlyCredentialBase`; with `lattice`, `VSIS` (`Σ-vSIS`) behind `CredentialBase`. `cred::bbs::ietf` derives the `BBS` generators as IETF BBS does. |
| `kiprf` | Key-injective PRFs, the tags (§3.1): `DDH` (`Tag_DDH`) and `DY` (`Tag_DY`, Dodis-Yampolskiy), with a stand-alone tag proof; with `lattice`, `LWR` (the short-key `Tag_LWR`). |
| `lattice` | Feature `lattice`: the shared foundations of the post-quantum instantiation, i.e. its parameter set, the ring types `Rq`, `Ternary`, `BinaryPoly`, the SHAKE128 oracles `H_mat`, `H_0`, `EncPred`, and Jali's parameter sets, embedded and pinned by SHA-256. |
| `sigma` | Sigma protocols (§2.3): linear relations over `G_1`, `G_2`, `G_T` with shared witness variables, the interactive protocol with simulator and extractor, and the strong Fiat-Shamir transform with compact `(c, z)` proofs. |
| `hash` | The random oracles `H_0`, `H_1`, `H_2` (§2.1) and the transcript; hash-to-curve for BLS12-381. |
| `serialization` | Validated compressed byte encoding; with the `serde` feature also JSON forms (multibase strings). |
| `error` | The error type `Error`: every `⊥` of the paper is a variant. |

`PCS`, `PredicateCredentialSystem` and `Error` are re-exported at the crate root, and so is
`LatticePCS` with the feature `lattice`.

## Instantiations

Sizes are bytes in the fixed-format encoding, as asserted by the tests: over BLS12-381 for the
pairing bases, at Jali proof degree 128 for the lattice base.

| Credential base | Type | Tags | `att` | `π` (`k = 5`) | `cred` |
|-----------------|------|------|-------|---------------|--------|
| `Σ-PS` | `cred::PS<E>` | `DDH`, `DY` | 240 | 1392 | 96 |
| `Σ-BBS` | `cred::BBS<E, H>` | `DDH`, `DY` | 416 | 2272 | 112 |
| `Σ-EQ` | `cred::EQ<E>` | `DDH` only (`Setup` refuses `DY`) | 480 | 2512 | 192 |
| `Σ-MAC` | `cred::MAC<G, H>` | base and possession proof only | | | |
| `Σ-vSIS` | `cred::VSIS` (feature `lattice`) | `LWR` (short-key `Tag_LWR`) | ≈ 83,600 | ≈ 462,100 | 5888 |

The `Σ-vSIS` row is the post-quantum instantiation `LatticePCS`: ring degree 1024 with
`q = 2^20 − 3`, the short-key LWR tag (tag set R) and Jali proofs at proof degree 128, under
parameters at an estimated 128-bit security level. `att` and `π` carry Jali proofs (about 83.1 KB
for `R_att` and 41.1 KB for `R_issue`; `π` also holds the `k` attestations), whose lengths vary by
tens of bytes with the proof seed, so the row gives rounded means.
At `k = 5` on an Apple M4, one thread / with the feature `parallel` on ten cores: `Attest`
5.9 / 3.0 s, `VerifyAtt` 3.0 / 1.6 s, `Prove` 17.5 / 5.8 s, `VerifyProof` 15.4 / 4.0 s and
`Issue` 15.4 / 3.9 s; `HKeyGen` takes 6 ms, `Unblind` and `VerifyCred` 0.14 ms. Peak memory is
about 0.6 GiB at one thread and 2.5 GiB with `parallel`. Every figure, including other `k`:
[Testing and benchmarks](./docs/testing-and-benchmarks.md).

The designated-verifier variant of the construction for `Σ-MAC` is not implemented yet. Out of
scope: the private credential requests (PRC) of the paper's appendix for the lattice
instantiation, the SNARK-based variant and straight-line extractable proof compilers.

## Feature Flags

| Flag | Default | Description |
|------|---------|-------------|
| `serde` | no | `Serialize` / `Deserialize` for the protocol objects: multibase base58btc strings and camelCase JSON objects. See [Encodings](./docs/encodings.md). |
| `parallel` | no | rayon-based parallelism inside arkworks, inside Jali's prover and verifier when Jali is enabled, and across the `k` attestation verifications of the lattice `VerifyProof`, `Issue` and `Prove` (the same verdicts; up to `min(k, threads)` verifications of 0.5-0.6 GiB each at once, bounded by `RAYON_NUM_THREADS` or a rayon pool of your own). |
| `asm` | no | Assembly backend of `ark-ff` on x86_64. |
| `print-trace` | no | Nested timings from `ark_std`. |
| `test-utils` | no | Test helpers, including an INSECURE hash-to-group oracle. Never enable in a deployment. |
| `jali` | no | Re-exports [Jali](https://github.com/etairi/jali), the standalone lattice zero-knowledge library, as `predicate_credential_system::jali`. It is the proof backend of the lattice instantiation. |
| `lattice` | no | The post-quantum instantiation: `cred::VSIS`, `kiprf::LWR`, the module `lattice` and `pcs::lattice::LatticePCS` (re-exported as `LatticePCS`). Enables `jali` (with Jali's `serde`, which loads the embedded parameter sets), `ntru-trapdoor` and `shake`. Jali and `ntru-trapdoor` are git dependencies pinned by revision. |

## Usage

The crate is not on crates.io; depend on it by path or git. The example is a two-vouch admission
policy: Alice and Bob hold community credentials and each vouches for Carol, who holds none.
Carol proves to the issuer, in zero knowledge, that two DISTINCT credentialed members vouched
for her, and receives a credential of her own. It uses `Σ-PS` with `Tag_DDH` over BLS12-381,
the paper's main instantiation.

```rust
use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    cred::PS,
    hash::bls12_381::G1Hasher,
    kiprf::DDH,
    pcs::{PCS, Predicate, PredicateCredentialSystem, SetupParams},
    Error,
};
use rand::rngs::OsRng;

type Scheme = PCS<Bls12_381, PS<Bls12_381>, DDH<G1Projective, G1Hasher>>;

fn main() -> Result<(), Error> {
    let mut rng = OsRng;
    let pcs = Scheme::setup(SetupParams::new(b"example.org/community".to_vec()))?;
    let (hvk, hsk) = pcs.helper_keygen(&mut rng); // the issuer of community credentials

    // Alice and Bob are founding members: the issuer admitted them after ITS OWN out-of-band
    // check and issued their credentials through the root path.
    let f_founder = Predicate::root(b"founders".to_vec());
    let (id_a, usk_a) = pcs.user_keygen(&mut rng)?;
    let (request, state) = pcs.root_request(&hvk, &f_founder, &id_a, &usk_a, &mut rng)?;
    let pre = pcs.issue_root(&hvk, &hsk, &f_founder, &id_a, &request, &mut rng)?;
    let cred_a = pcs.unblind(&hvk, &usk_a, &f_founder, &pre, &state)?;

    let (id_b, usk_b) = pcs.user_keygen(&mut rng)?;
    let (request, state) = pcs.root_request(&hvk, &f_founder, &id_b, &usk_b, &mut rng)?;
    let pre = pcs.issue_root(&hvk, &hsk, &f_founder, &id_b, &request, &mut rng)?;
    let cred_b = pcs.unblind(&hvk, &usk_b, &f_founder, &pre, &state)?;

    // Carol has a key pair and no credential. Alice and Bob each vouch for HER identifier.
    let (id_c, usk_c) = pcs.user_keygen(&mut rng)?;
    let vouch_a = pcs.attest(&hvk, &usk_a, &f_founder, &cred_a, &id_c, &mut rng)?;
    let vouch_b = pcs.attest(&hvk, &usk_b, &f_founder, &cred_b, &id_c, &mut rng)?;

    // The admission policy: two vouches from distinct credentialed members.
    let f_member = Predicate::new(2, b"members".to_vec());

    // Two vouches from the SAME member do not count, and Carol cannot even build a proof.
    let twice = [vouch_a.clone(), vouch_a.clone()];
    assert_eq!(
        pcs.prove(&hvk, &f_member, &id_c, &usk_c, &twice, &mut rng).err(),
        Some(Error::DuplicateAttester)
    );

    // Carol proves that she holds two vouches from distinct members. The issuer verifies the
    // proof and issues blindly: it never sees `usk_c`, and it does not learn who vouched.
    let vouches = [vouch_a, vouch_b];
    let (proof, state) = pcs.prove(&hvk, &f_member, &id_c, &usk_c, &vouches, &mut rng)?;
    assert!(pcs.verify_proof(&hvk, &f_member, &id_c, &proof));
    let pre = pcs.issue(&hvk, &hsk, &f_member, &id_c, &proof, &mut rng)?;
    let cred_c = pcs.unblind(&hvk, &usk_c, &f_member, &pre, &state)?; // fails closed
    assert!(pcs.verify_cred(&hvk, &usk_c, &f_member, &cred_c));

    // Carol is a member now and can vouch for the next applicant.
    Ok(())
}
```

From the proof the issuer learns Carol's identifier, that two distinct holders of valid
credentials vouched for it, and the class label of each voucher's credential (here "founders").
By the paper's Theorem "Attester anonymity" it does not learn which members vouched, although
it issued their credentials, and vouches of one member for different applicants cannot be
linked. A predicate is a threshold `k ≥ 1` with a
label; the attribute policy decides which voucher classes count. A helper must not run with the
default policy `P ≡ 1` and must serve a closed set of predicates: see
[Operating a helper](./docs/operating-a-helper.md). `to_compact_bytes` / `from_compact_bytes`
and the `serde` feature put proofs on the wire: see [Encodings](./docs/encodings.md).

The post-quantum instantiation runs the same flow through the same trait (feature `lattice`).
Each attestation is a Jali proof of about 83 KB that takes seconds to prove and to verify, so
this example is compiled but not run by the documentation tests:

```rust,no_run
use predicate_credential_system::{
    LatticePCS,
    pcs::{Predicate, PredicateCredentialSystem, SetupParams},
    Error,
};
use rand::rngs::OsRng;

fn main() -> Result<(), Error> {
    let mut rng = OsRng;
    let f_founder = Predicate::root(b"founders".to_vec());
    let f_member = Predicate::new(2, b"members".to_vec());
    let open = LatticePCS::setup(SetupParams::new(b"example.org/community".to_vec()))?;
    // the issuer counts vouches from founders and members only
    let policy = open.allow_list([&f_founder, &f_member]);
    let pcs = LatticePCS::from_public_parameters(open.public_parameters().clone(), policy)?;
    let (hvk, hsk) = pcs.helper_keygen(&mut rng); // an NTRU trapdoor

    let mut vouchers = Vec::new();
    for _ in 0..2 {
        let (id_j, usk_j) = pcs.user_keygen(&mut rng)?;
        let (request, state) = pcs.root_request(&hvk, &f_founder, &id_j, &usk_j, &mut rng)?;
        let pre = pcs.issue_root(&hvk, &hsk, &f_founder, &id_j, &request, &mut rng)?;
        let cred_j = pcs.unblind(&hvk, &usk_j, &f_founder, &pre, &state)?;
        vouchers.push((usk_j, cred_j));
    }
    let (id_c, usk_c) = pcs.user_keygen(&mut rng)?;
    let mut vouches = Vec::new();
    for (usk_j, cred_j) in &vouchers {
        vouches.push(pcs.attest(&hvk, usk_j, &f_founder, cred_j, &id_c, &mut rng)?);
    }
    let (proof, state) = pcs.prove(&hvk, &f_member, &id_c, &usk_c, &vouches, &mut rng)?;
    let pre = pcs.issue(&hvk, &hsk, &f_member, &id_c, &proof, &mut rng)?; // VerifyProof first
    let cred_c = pcs.unblind(&hvk, &usk_c, &f_member, &pre, &state)?;
    assert!(pcs.verify_cred(&hvk, &usk_c, &f_member, &cred_c));
    Ok(())
}
```

## Building and Testing

Rust 1.95.0 or higher (edition 2024).

```bash
cargo build
cargo test                        # unit, integration and documentation tests
cargo bench --bench pcs           # also: --bench cred, --bench kiprf
```

`cargo test` compiles the lattice instantiation too (the crate's dev-dependency on itself
enables `lattice`) and runs its light tests. Its end-to-end flows and attacks run Jali proofs of
seconds and about 0.5 GiB each, so they run in release, one at a time:

```bash
cargo test --release --features lattice --test lattice_pcs     # the k = 1 flow, about 30 s
RUST_TEST_THREADS=1 cargo test --release --features lattice \
    --test lattice_flows --test lattice_attacks -- --ignored    # the harness's flows at k = 3, 5; attacks
RUST_TEST_THREADS=1 cargo test --release --features lattice \
    --test lattice_pcs --test lattice_adversarial --test lattice_sizes -- --ignored  # more flows, sizes
RUST_TEST_THREADS=1 cargo test --release --features lattice,parallel \
    --test lattice_parallel -- --ignored     # CheckAtts_P in parallel; run it without, too
cargo bench --bench lattice --features lattice                  # about 18 minutes at one thread
```

Each benchmark first prints the sizes of the objects it handles. Before a change is proposed:

```bash
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings
RUSTDOCFLAGS='-D warnings' cargo doc --no-deps
```

## Documentation

```bash
cargo docs
```

builds the API documentation with the `serde` layer, the `jali` re-export, the lattice
instantiation and rendered formulas, and opens it. It is an alias (`.cargo/config.toml`) that hands
`docs/katex-header.html` to rustdoc, as the
`[package.metadata.docs.rs]` section of `Cargo.toml` does for docs.rs. Formulas are written
inside code (`` $`…`$ `` inline, `math` code blocks for display) and rendered with
[KaTeX](https://katex.org) loaded from a CDN; a plain `cargo doc` shows their LaTeX source.

## Security

- **Research artifact** — not audited, and we do not claim any constant-time behaviour.
- **Random-oracle model, plain Fiat-Shamir** — knowledge extraction is by rewinding. By the
  paper's Remark "Concurrent issuance" its theorems then hold for sequential issuance and
  constant `k`; the crate does not enforce sequential issuance.
- **Standing endorsements** — an attestation binds the subject's `id` and the attester's key,
  not a session or a predicate, and can be presented again for the same `id`.
- **Received objects are re-validated** — every algorithm checks that the group elements it
  receives are in the prime-order subgroup, and every verifier rebuilds its Fiat-Shamir context
  from public data. Decoding is validated and strict.
- **Zeroization** — secrets owned by the crate are wiped on drop (`zeroize`), but field
  elements are `Copy` and temporaries may remain on the stack.
- **No unsafe code** — `#![forbid(unsafe_code)]`.
- **The helper's policy decides** — the construction is as strong as the helper's admission
  decisions; see [Operating a helper](./docs/operating-a-helper.md).
- **The lattice instantiation is not covered by a security theorem yet** — the paper
  references its post-quantum theorem without stating it. Jali, `SampPre` and `TrapGen` run in
  variable time. The helper's RNG must be the operating system's
  CSPRNG (the trapdoor is a function of it). A helper key answers at most `Q_max = 2^48`
  issuances and counts them in `hsk`: run one live instance per key and store `hsk` before
  issuing (`to_bytes_reserving`). Every preimage is checked exactly before it leaves the key;
  each attestation verification takes about 0.5 GiB, and with `parallel` a request verifies up
  to `min(k, threads)` of them at once. See
  [Operating a helper](./docs/operating-a-helper.md#the-lattice-instantiation-feature-lattice)
  and [Design notes](./docs/design-notes.md#limitations-of-the-lattice-instantiation).

## Additional Resources

- [Operating a helper](./docs/operating-a-helper.md)
- [Design notes, limitations and relation to the paper](./docs/design-notes.md)
- [Encodings and interoperability](./docs/encodings.md)
- [Testing and benchmarks](./docs/testing-and-benchmarks.md)
- [OpenVTC integration](./docs/openvtc-integration.md)
- [`demo/`](./demo/README.md) — a throwaway prototype of hidden-vetter admission on top of this
  crate; a workspace member, not published

## License

Licensed under [MIT](./LICENSE).
