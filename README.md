# Predicate Credentials (PCreds)

[![Rust](https://img.shields.io/badge/rust-1.95.0%2B-blue.svg?maxAge=3600)](https://github.com/etairi/predicate-credential-system)

Rust implementation of the *predicate credentials* (PCreds) of the accompanying paper. In the
words of its §4: "A predicate credential system (PCreds) lets users obtain a credential from a
helper once enough credentialed users satisfying some policy attest for them, and then prove
anonymously that they are credentialed or that a message comes from a credentialed user." Users
reach attesters through contact names, an attestation is addressed to the requester's
identifier, and for the threshold policy the helper issues once the attestations come from `k`
distinct credentialed users, without learning who they are. Built on
[arkworks](https://arkworks.rs) 0.6.

> **Research artifact.** Not audited. See [Security notes and limitations](#security-notes-and-limitations).

The module `pcreds` implements the protocol `Π_PCreds` (§4.2) of the ideal functionality
`F_PCreds` (§4.1), generic over its building blocks, with the pairing-based instantiations of §5
and the post-quantum instantiation of §5.2.3 (feature `lattice`; see
[Instantiations](#instantiations)). The standalone [Jali library](https://github.com/etairi/jali)
implements the lattice zero-knowledge proofs that the lattice instantiation uses (the LNP22 proof
stack described in the [Rust port plan](./docs/lnp22-rust-port-plan.md)); this crate depends on
its crates.io release (feature `jali`). See Jali's README for its status and limits.

## Overview

A user `P` holds a tag key `usk_P` and, with a helper key `hvk`, the identifier
`id_P = Tag(usk_P, x_0)` at the identifier point `x_0 = H_id(⟨hvk⟩)` of that key. An attestation
from `P` to `Q` carries an *attestation tag* at the *recipient point* `x_Q`, where `j_Q` is the
least counter with `x_Q ≠ x_0` (§4.2, "Identifiers and attestation tags"):

```math
x_0 = H_{\mathsf{id}}(\langle hvk \rangle), \qquad id_P = \mathsf{Tag}(usk_P, x_0), \qquad x_Q = H_{\mathsf{req}}(\langle pp, hvk, id_Q, j_Q \rangle), \qquad t_{P \to Q} = \mathsf{Tag}(usk_P, x_Q)
```

Each helper key determines its own identifier point, so a user who reuses `usk_P` with two
helpers has unrelated identifiers at them.

One key gives the same tag at a given recipient, so repeated attestations from one source count
once, through whatever contact names they arrive; tags at different recipients are unlinkable.
The helper keeps the set `I` of identifiers it has issued to and issues at most once per
identifier. What each party learns (§4.1, Table "What each party learns"): the attester learns
`id_Q` and the contact name through which it was reached; the recipient learns the tag; the
helper learns `id_Q`, the tags named in the request and the policy result; a membership proof on
a message reveals nothing about the prover.

### Interfaces, protocol steps and methods

`pcreds::Protocol<Bk>` holds `pp` and implements every step of the protocol box; the calls of
`F_PCreds` that keep state between messages are values the caller holds (`PendingAttestation`,
the `Attestation`s, `IssuanceState`, `EvaluatedRequest`), and the algorithm that completes a
call takes its pending state by value ("pending state is consumed on completion"). Delivery,
contact routing and the bulletin board are the application's.

| `F_PCreds` (§4.1) | `Π_PCreds` (§4.2) | `pcreds::Protocol` |
|---|---|---|
| (setup, helper) | `pp = (pp_Σ, H_id, H_req, H_1)`; `(hvk, sk) ← KeyGen(pp)`, `I ← ∅`; users return `⊥` if `hvk ∉ V_pp`; all parties derive `x_0 = H_id(⟨hvk⟩)` | `setup(label)`, `from_public_parameters(pp)`; `helper_keygen(policy, rng)`, `helper_keygen_with_store`, `restore_helper`, `helper_from_key_pair`; users: `helper_key(vk)`, once (the `HelperKey` carries `x_0`) |
| `Register` | reuse `usk` or sample `usk ← TagKeyGen(1^λ)`; `id = Tag(usk, x_0)`, `RegisterFailed` if `⊥` | `register(&hvk, rng)`, `register_reusing(&hvk, &user)`; `user(&hvk, usk)`, `check_user(&hvk, &user)` for a stored key |
| `ContactRegister` | register a route with the contact service | none (the application's contact service) |
| `AttestationRequest` | `Q`: `π_id` for `R_Tag` at `(id_Q, x_0)` under `(ssid, P̃)`; `P`: checks `id_Q ∈ T` and `π_id`, retains the request | `request_attestation(&hvk, &user, ssid, contact, rng)`; `receive_attestation_request(&hvk, &request, ssid, contact)` → `PendingAttestation` |
| `AttestationRequestResponse` | `P`: `t_{P→Q}`, `σ* = ReRand(…)`, `π_att`; `Q`: checks `t ∈ T` and `π_att`, keeps the first attestation per tag | `attest(&hvk, &attester, &cred, pending, rng)`; `check_attestation(&hvk, id_q, &att)` / `verify_attestation` |
| `CredentialRequest` | `Q`: `Ĉ = PrepareIssue(hvk, usk_Q; τ)`, `CredentialRequestFailed` if `Ĉ = ⊥`, `π_iss` under `(ssid, att⃗)`; helper: checks `id_Q ∈ T` and `π_iss`, computes `N''` and `v = [\|N''\| ≥ k]` | `request_credential(&hvk, &user, attestations, ssid, rng)` → `(CredentialRequest, IssuanceState)`; `evaluate_request(&helper, &message, ssid)` → `EvaluatedRequest` (`id()`, `tags()` = `N''`, `is_valid()` = `v`) |
| `CredentialRequestResponse` | helper, on `d ∈ {policy, root}`: `Fail`, `issued`, or `I ← I ∪ {id_Q}` and then `σ̂ ← BlindIssue(sk, Ĉ)`; `Q`: `Unblind`, `Verify` | `respond(&mut helper, evaluated, Decision::Policy / Decision::Root, rng)` → `Reply::{Fail, Issued, PreCredential(σ̂)}`; `unblind(&hvk, &user, &pre, state)` → `Credential` |
| `Prove` | `σ* = ReRand(…)`, `π_prove` for `R_Possess` under `m` | `prove(&hvk, &user, &cred, m, rng)` → `MembershipProof` |
| `Verify` | the check of `π_prove` under `m` | `verify(&hvk, m, &proof)`; `check_membership` names the reason of a rejection |

The proof contexts, `H_id` and `H_req` are public functions of public data
(`identifier_context`, `attestation_context`, `issuance_context`, `prove_context`,
`identifier_point`, `recipient_point`), so that a test harness can play a cheating prover; every
verifier rebuilds its context itself.

**Application contexts (OpenVTC, not in the paper).** `attest_in_context`,
`check_attestation_in_context` and `verify_attestation_in_context` bind an attestation to the
caller's bytes `app`, such as a validity window or the deployment's statement metadata, and
`request_credential_in_context` and `evaluate_request_in_context` bind `π_iss` to the context of
each attestation and to the request's own one. The attester, the requester and the helper supply
the same bytes, and a verifier takes them from its own copy of the public data, never from the
prover. An attestation then verifies under its own context only and counts for the helper only
under it, while its tag, and so the count of distinct attesters, does not depend on it. Without
application contexts every context is the paper's, byte for byte ([Design
notes](./docs/design-notes.md#contexts)). The lattice backend gets them too, as its proofs take
the same contexts.

## Instantiations

`Π_PCreds` starts from "a credential base `Σ` that certifies a user's secret tag key `usk`", with
a key-injective PRF `Tag` and an online simulation-extractable NIZK (§4.2). In code, one such
triple is a
`pcreds::Backend`, and `Protocol<Bk>` is written once over it.

| Backend | Credential base | Tag | NIZK | Status |
|---|---|---|---|---|
| `pcreds::pairing::PairingBackend<E, B, T>` | `B = PS` (`Σ-PS`, §5.2.1) or `BBS<H>` (`Σ-BBS`, §5.2.2) | `T = kiprf::DDH<G1, H>` (`Tag_DDH`, §5.1.1) or `kiprf::DY<G1, H>` (`Tag_DY`, §5.1.2) | generalized Schnorr proofs, plain Fiat–Shamir after the IETF CFRG drafts `draft-irtf-cfrg-sigma-protocols-04` and `draft-irtf-cfrg-fiat-shamir-04` | implemented, every pair, over BLS12-381 (`H = hash::bls12_381::G1Hasher`) |
| `pcreds::lattice::LatticeBackend` | `Σ-vSIS` (§5.2.3) on an NTRU trapdoor | short-key `Tag_LWR` (§5.1.3) | Jali proofs (LNP22, straight-line extractable, or plain Fiat–Shamir with the feature `lattice-plain`) | implemented (feature `lattice`); two hypotheses of the paper not met, see below |

`pcreds::pairing::PairingProtocol<E, B, T>` is `Protocol<PairingBackend<E, B, T>>`. The paper's
main instantiation is `Σ-PS` with `Tag_DDH`, i.e.
`PairingProtocol<Bls12_381, PS, DDH<G1Projective, G1Hasher>>` (the [example](#example) below).
`Σ-EQ` and `Σ-MAC`, which the earlier construction supported, were dropped: the current paper does
not have them. Not part of the paper either: `pcreds::pairing::ietf` derives the generators of
`Σ-BBS` as IETF BBS (BLS12-381-SHA-256) does, so that a credential is an IETF BBS signature on
`(usk, ρ)`, with byte bridges to IETF keys and signatures; presentations are not IETF BBS proofs.
Under these parameters `h_0` depends on the helper's key, while the paper's lemma on `Σ-BBS`
takes `pp` before the key, so the lemma is not claimed for them
([Encodings](./docs/encodings.md#interoperability-with-ietf-bbs-pcredspairingietf)).

### Sizes

Bytes over BLS12-381 (`G_1` 48, `G_2` 96, `Z_p` 32, compressed) at `k = 5`, in the fixed-format
encoding of `pcreds::codec`, for either tag. `tests/pcreds.rs` (`sizes_match_the_paper`) asserts
every number, for all four base/tag pairs; they agree with the paper's Table "Sizes" (§6).

| Base | `att` | `π` (`k = 5`) | `cred` | membership proof |
|------|-------|---------------|--------|------------------|
| `Σ-PS` | 240 | 1344 | 96 | 192 |
| `Σ-BBS` | 448 | 2384 | 112 | 400 |

* `att` = `t` (48) + `σ*` + `π_att`: for `Σ-PS` `(σ'_1, σ'_2)` (96) and `(c, z_usk, z_t)` (96);
  for `Σ-BBS` `(Ā, B̄, D)` (144) and `c` with seven responses (256).
* `π` (`CredentialRequest::size`) counts, as in the paper, the `k` attestations, the issuance
  request `Ĉ` (48) and the requester's issuance proof `π_iss = (c, z_usk, z_ρ)` (96). The wire
  encoding of a credential request (`to_compact_bytes`) adds `id_Q` (48) and a 4-byte count:
  1396 and 2436 bytes.
* `cred` is the credential of the base: `(σ_1, σ_2)` for `Σ-PS`, `(A, e, ρ)` for `Σ-BBS`.
* A membership proof is `σ*` and `π_prove`. An identifier `id` has 48 bytes.

Layouts, the derived canonical encodings and the JSON forms: [Encodings](./docs/encodings.md).

### The lattice instantiation (feature `lattice`)

`pcreds::lattice::LatticeProtocol` is `Protocol<LatticeBackend>`: the same protocol over the
credential base `Σ-vSIS` on an NTRU trapdoor (the crate `ntru-trapdoor`), the short-key LWR tag
(`kiprf::LWR`) and Jali proofs for the four relations `R_Tag`, `R_att`, `R_iss` and `R_Possess`.
Every proof is a Jali proof of 28 to 88 kilobytes that takes up to about seven seconds at one
thread and up to about 0.7 GB to prove or to verify. A credential is `(s, x_1, x_0)`, 6144
bytes, and a show is empty (lattice signatures do not re-randomize: the whole credential is the
witness). The sizes, measured on real proofs (`tests/lattice_sizes.rs`; they vary by tens of
bytes with the proof seed) and bounded by the decoders and verifiers at twice the estimate of
each Jali parameter set:

| object | bytes (measured) | proof bound |
|---|---|---|
| attestation request `id_Q ‖ π_id` | 28,477-28,485 | `π_id` ≤ 58,336 |
| `att` = `t ‖ π_att` | 87,772-87,844 | `π_att` ≤ 180,432 |
| `π` at `k = 5` (five attestations, `Ĉ`, `π_iss`) | 485,881-485,954 | `π_iss` ≤ 92,416 |
| credential request at `k = 5` on the wire | 486,221-486,294 | |
| reply with `σ̂ = (s, x_1)` | 5377 | |
| membership proof `π_prove` | 82,340-82,356 | `π_prove` ≤ 169,808 |

An identifier has 336 bytes and `hvk` 2560; the helper's stored key 8489 (with its issuance
count). Measured on 2026-10-18 in seeded runs: [Testing and
benchmarks](./docs/testing-and-benchmarks.md#measurements-of-the-lattice-instantiation).

#### Straight-line extractable proofs (the default) and plain ones (feature `lattice-plain`)

The paper's theorem assumes a NIZK whose extractor does not rewind, so the backend proves every
relation in Jali's straight-line extractable mode (Katsumata's transform): each proof also commits to its witness with an extractable linear
homomorphic commitment, under a key that the random oracle outputs on the parameters, the
extraction set, the context and the statement, so that an extractor holding trapdoors for such
keys recovers the witness from one proof. Each parameter set takes an extraction set, derived by
Jali's parameter tool under the set's own policy and gated by lattice-estimator at 128 bits
([`tools/lattice/sets/README.md`](./tools/lattice/sets/README.md#extraction-sets)). The feature
`lattice-plain` proves with plain Fiat–Shamir instead, with shorter proofs that only rewinding
extracts. The choice changes the lattice proofs and the digest of the lattice `pp`, so every party
of a deployment builds with the same choice, and the two builds refuse each other's parameters and
proofs. The pairing instantiation keeps plain Fiat–Shamir. Jali argues this extraction in the classical
random-oracle model, as an outline with the status of each step.

The proofs are about 5.7 times as long (one seeded run of `tests/lattice_sizes.rs` per build,
2026-11-15):

| object | bytes, plain build | bytes, extractable build | proof bound, extractable build |
|---|---|---|---|
| attestation request `id_Q ‖ π_id` | 28,481 | 167,109 | `π_id` ≤ 340,064 |
| `att` = `t ‖ π_att` | 87,789-87,813 | 496,161-496,249 | `π_att` ≤ 1,008,656 |
| `π` at `k = 5` (five attestations, `Ĉ`, `π_iss`) | 485,889 | 2,803,886 | `π_iss` ≤ 652,320 |
| credential request at `k = 5` on the wire | 486,229 | 2,804,226 | |
| membership proof `π_prove` | 82,354 | 463,551 | `π_prove` ≤ 942,896 |

Time grows far less than size. Over a protocol run (setup, a root admission, an attestation
request and its check, an attestation and its check, a membership proof and its check) the
extractable build retired 1.08 times the instructions of the plain one (seeds 1 to 3, one
thread). Its provers took 1.02 to 1.37 times by the means of the three seeds, figures that the
provers' restarts dominate, and its verifiers stayed within 6 % of the plain ones, inside the
variation between proofs and between runs. Peak memory grew from 0.65 to 0.73 GB ([Testing and
benchmarks](./docs/testing-and-benchmarks.md#the-extractable-build)).

The parameters follow the paper's base lemma: the issuance randomness `x_0` has 3 ternary
components, which make the request pseudorandom under MLWE (lem:base-vsis (b); lattice-estimator
prices the instance at 2^344.9 in rough mode, `tools/lattice/hiding_estimate.sage`), and the
proofs bound `s` on both sides, `1 ≤ ‖s‖² ≤ β_s²`, so that they extract `s ≠ 0` (Jali's
`Norm::L2SquaredRange`); §5.2.3 of the paper gives the argument. No
theorem covers the instantiation as implemented: its proofs are straight-line extractable proofs
whose argument Jali gives as an outline (below), or with the feature `lattice-plain` Fiat–Shamir
proofs extracted by rewinding, and the one-more assumption of `Σ-vSIS` is not
estimated at these parameters (the module docs of `pcreds::lattice`). The four Jali parameter sets were derived for
this backend with Jali's parameter tool (`tools/lattice/sets/`).

Running times, one thread / with the feature `parallel` on ten cores (`cargo bench --bench
lattice`, Apple M4, rustc 1.99.1, 2026-10-18; criterion's means): an attestation takes 6.8 s /
3.4 s to make and 3.5 s / 1.8 s to check; the helper's evaluation of a request at `k = 5`
18.0 s / 4.1 s; a credential request (`π_iss`) 2.0-2.1 s / 1.3 s; a membership proof 5.1 s /
2.3 s and its check 3.0 s / 1.5 s; `π_id` 1.10 s / 0.93 s. `respond` (`BlindIssue` and the
record) takes about a millisecond, `Unblind` 0.15 ms, `KeyGen` 6 ms and `Setup` 3 ms. A proof or
verification holds up to about 0.7 GB, and the benchmark process peaked at 0.71 GB at one thread
and 2.9 GB with `parallel`. Against Stage 1 (`ℓ_r = 2`, no lower bound on `‖s‖²`), the proofs
that carry `x_0` take 4 to 19 % more time and their messages 5 to 8 % more bytes; the
statistical variant with 13 components of `x_0` took 2.6 to 3.7 times as long as now and needed
up to 1.7 GB. Details: [Testing and
benchmarks](./docs/testing-and-benchmarks.md#measurements-of-the-lattice-instantiation).

## Example

Two founders are admitted by the helper as root users and attest for Carol, who obtains a
credential under the threshold policy `Pol_2` and then proves membership on a message. The
example is compiled and run by `cargo test --doc` (the crate includes this README as a doctest).

```rust
use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::DDH,
    pcreds::{
        CredentialRequest, Decision, Policy, Protocol, Reply,
        pairing::{PS, PairingBackend},
    },
};
use rand::{SeedableRng, rngs::StdRng};

/// `Σ-PS` with `Tag_DDH` over BLS12-381, the paper's main instantiation.
type Bk = PairingBackend<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;

fn main() -> Result<(), Error> {
    // Seeded so that the example is reproducible. A deployment draws every key and every
    // proof from the operating system's CSPRNG (`rand::rngs::OsRng`).
    let mut rng = StdRng::seed_from_u64(2026);

    // The helper: transparent setup from the deployment label, and its key under Pol_2.
    let issuer = Protocol::<Bk>::setup(b"example.org/community")?;
    let mut helper = issuer.helper_keygen(Policy::threshold(2)?, &mut rng);

    // Users accept the published pp only if Setup derives it from its label, and check the
    // published hvk once (hvk ∈ V_pp).
    let pcreds = Protocol::<Bk>::from_public_parameters(issuer.public_parameters().clone())?;
    let hvk = pcreds.helper_key(helper.key().vk())?;

    // Root users: ordinary requests without attestations, which the policy rejects and the
    // helper admits with d = root, after ITS OWN admission check.
    let mut members = Vec::new();
    for ssid in [b"root-alice".as_slice(), b"root-bob"] {
        let user = pcreds.register(&hvk, &mut rng)?;
        let (request, state) = pcreds.request_credential(&hvk, &user, Vec::new(), ssid, &mut rng)?;
        let evaluated = issuer.evaluate_request(&helper, &request, ssid)?;
        assert!(!evaluated.is_valid());
        let Reply::PreCredential(pre) =
            issuer.respond(&mut helper, evaluated, Decision::Root, &mut rng)?
        else {
            unreachable!("a root admission of a new identifier issues");
        };
        let cred = pcreds.unblind(&hvk, &user, &pre, state)?;
        members.push((user, cred));
    }

    // Carol asks each member for an attestation through the member's contact name. She proves
    // that she owns her identifier (π_id); a member attests only on a checked request.
    let carol = pcreds.register(&hvk, &mut rng)?;
    let mut attestations = Vec::new();
    for (j, (member, cred)) in members.iter().enumerate() {
        let (ssid, contact) = (format!("att-{j}"), format!("member-{j}@example.org"));
        let (ssid, contact) = (ssid.as_bytes(), contact.as_bytes());
        let request = pcreds.request_attestation(&hvk, &carol, ssid, contact, &mut rng)?;
        // the member, on a request that reached it through ITS contact name
        let pending = pcreds.receive_attestation_request(&hvk, &request, ssid, contact)?;
        let att = pcreds.attest(&hvk, member, cred, pending, &mut rng)?;
        // Carol checks the reply before she stores it
        pcreds.check_attestation(&hvk, carol.id(), &att)?;
        attestations.push(att);
    }

    // A second attestation from the first member, through another contact name, carries the
    // same tag: a source counts once, and two attestations from it do not satisfy Pol_2.
    let request =
        pcreds.request_attestation(&hvk, &carol, b"att-2", b"alice@example.net", &mut rng)?;
    let pending =
        pcreds.receive_attestation_request(&hvk, &request, b"att-2", b"alice@example.net")?;
    let again = pcreds.attest(&hvk, &members[0].0, &members[0].1, pending, &mut rng)?;
    assert_eq!(again.tag, attestations[0].tag);
    let twice = vec![attestations[0].clone(), again];
    let (request, _) = pcreds.request_credential(&hvk, &carol, twice, b"req-1", &mut rng)?;
    let evaluated = issuer.evaluate_request(&helper, &request, b"req-1")?;
    assert_eq!(evaluated.tags().len(), 1);
    assert_eq!(issuer.respond(&mut helper, evaluated, Decision::Policy, &mut rng)?, Reply::Fail);

    // Two distinct members: the helper learns id_Q, the tags and the policy result, and
    // issues blindly; Carol's unblind verifies the credential (it fails closed).
    let (request, state) =
        pcreds.request_credential(&hvk, &carol, attestations, b"req-2", &mut rng)?;
    let evaluated = issuer.evaluate_request(&helper, &request, b"req-2")?;
    assert_eq!(evaluated.id(), carol.id());
    assert_eq!(evaluated.tags().len(), 2);
    assert!(evaluated.is_valid());
    let Reply::PreCredential(pre) =
        issuer.respond(&mut helper, evaluated, Decision::Policy, &mut rng)?
    else {
        unreachable!("a valid request of a new identifier issues");
    };
    let cred = pcreds.unblind(&hvk, &carol, &pre, state)?;

    // At most one credential per identifier: a later valid request is answered `issued`.
    let atts = request.attestations.clone();
    let (later, _) = pcreds.request_credential(&hvk, &carol, atts, b"req-3", &mut rng)?;
    let evaluated = issuer.evaluate_request(&helper, &later, b"req-3")?;
    assert_eq!(issuer.respond(&mut helper, evaluated, Decision::Policy, &mut rng)?, Reply::Issued);
    assert_eq!(helper.store().len(), 3); // the set I: two founders and Carol

    // Anonymous use: a membership proof on a message, which anyone holding hvk verifies.
    let proof = pcreds.prove(&hvk, &carol, &cred, b"posted by a member", &mut rng)?;
    assert!(pcreds.verify(&hvk, b"posted by a member", &proof));
    assert!(!pcreds.verify(&hvk, b"another message", &proof));

    // On the wire: the fixed-format encoding, whose sizes are those of the table above.
    assert_eq!(request.attestations[0].size(), 240);
    assert_eq!(request.size(), 2 * 240 + 48 + 96); // k attestations, Ĉ and π_iss
    assert_eq!(proof.size(), 192);
    let bytes = request.to_compact_bytes()?;
    assert_eq!(bytes.len(), 48 + 4 + request.size()); // id_Q and the count
    assert_eq!(CredentialRequest::<Bk>::from_compact_bytes(&bytes)?, request);
    Ok(())
}
```

The same flow runs for `PS` or `BBS<G1Hasher>` with `DDH<G1Projective, G1Hasher>` or
`DY<G1Projective, G1Hasher>` (`tests/pcreds.rs` runs all four). What an operator of a helper
has to decide around these calls (the policy, root admissions, the durability of `I`, the key):
[Operating a helper](./docs/operating-a-helper.md). How an application maps them to its
messages and storage: [OpenVTC integration](./docs/openvtc-integration.md).

## Modules

| Module | Description |
|--------|-------------|
| `pcreds` | The protocol `Π_PCreds` (§4): `Protocol<Bk>` over a `Backend`; its objects and messages (`pcreds::types`: `Policy`, `Helper`, `HelperKey`, `IssuanceStore`, `IssuanceRecord`, `User`, `Credential`, `IssuanceState`, `AttestationRequest`, `Attestation`, `CredentialRequest`, `EvaluatedRequest`, `Decision`, `Reply`, `MembershipProof`); the fixed-format codec (`pcreds::codec`). |
| `pcreds::pairing` | The pairing-based backend `PairingBackend<E, B, T>`, the public relation builders of `R_Tag`, `R_att`, `R_iss`, `R_Possess`, and the credential bases `PS` and `BBS<H>` behind the trait `Base` (`pcreds::pairing::base`). `pcreds::pairing::ietf`: the generators of `Σ-BBS` as IETF BBS (BLS12-381-SHA-256) derives them, under which a credential is an IETF BBS signature, and the byte bridges (not part of the paper). |
| `kiprf` | Key-injective PRFs, the tags (§3.1, §5.1): `DDH` (`Tag_DDH`) and `DY` (`Tag_DY`) behind `ProtocolTag`, with a stand-alone proof of `R_Tag`; with `lattice`, `LWR` (short-key `Tag_LWR`). |
| `sigma` | Sigma protocols (§2.3): linear relations over `G_1`, `G_2`, `G_T` with shared witness variables, the interactive protocol with simulator and extractor, and the Fiat–Shamir transform with compact `(c, z)` proofs. The transform follows `draft-irtf-cfrg-sigma-protocols-04` (SHAKE128 duplex sponge, compact NARG strings, the context in the tag): relations over `G_1` are the draft's, under its ciphersuite `sigma-proofs_Shake128_BLS12381`, and relations with `G_2` or `G_T` equations use a documented extension of this crate with its own identifier. `tests/ietf_vectors.rs` runs the drafts' vectors (`kat/ietf/`). |
| `hash` | The transcript and the oracles (`H_2 = htag`, the generators of `Σ-BBS` and `Tag_DY`, with `H_id` and `H_req` transcripts of `pcreds`), `hash::duplex_sponge`, the SHAKE128 duplex sponge of `draft-irtf-cfrg-fiat-shamir-04` behind `H_1`, and hash-to-curve for BLS12-381. `hash::testing` (feature `test-utils`): an INSECURE oracle for other groups. |
| `serialization` | Validated compressed byte encoding; with `serde`, JSON forms (multibase base58btc strings). |
| `error` | The error type `Error`: every `⊥` of the paper is a variant. |
| `pcreds::lattice` | Feature `lattice`: the lattice backend `LatticeBackend` (`LatticeProtocol`), its parameters, points and proofs, and the credential base `Σ-vSIS` (`pcreds::lattice::base`). |
| `lattice` | Feature `lattice`: the foundations of the post-quantum instantiation: the parameter set, the ring types `Rq` and `Ternary`, the oracles `H_mat`, `H_id`, `H_req` (`lattice::oracles`) and the embedded Jali parameter sets (`lattice::sets`). |

`Error` is re-exported at the crate root, and Jali as `predicate_credential_system::jali` with the
feature `jali`.

## Feature flags

| Flag | Default | Description |
|------|---------|-------------|
| `serde` | no | `Serialize` / `Deserialize` for the protocol objects: messages as camelCase JSON objects whose leaves are multibase base58btc strings, everything else one string; secrets through a wiping adapter. See [Encodings](./docs/encodings.md). |
| `parallel` | no | rayon-based parallelism inside arkworks (MSM, batch normalisation, batch checks) and inside Jali's prover and verifier, and across the attestations of a credential request in `Protocol::evaluate_request` (the same verdicts; batches no wider than the rayon pool, which bounds the memory of a lattice request: up to about 0.7 GB per attestation verification). |
| `asm` | no | Assembly backend of `ark-ff` on x86_64 (bmi2 + adx); a no-op elsewhere. |
| `print-trace` | no | Nested timings from `ark_std`. |
| `test-utils` | no | Test helpers: the INSECURE hash-to-group oracle `hash::testing` (known discrete logarithms). Never enable in a deployment. |
| `jali` | no | Re-exports [Jali](https://github.com/etairi/jali) as `predicate_credential_system::jali`, the proof backend of the lattice instantiation. |
| `lattice` | no | The post-quantum instantiation: the modules `lattice` and `pcreds::lattice` (`LatticeBackend`, `Σ-vSIS`), and `kiprf::LWR`. Its proofs are straight-line extractable: Jali's extractable mode (Katsumata's transform, classical random-oracle model) with the embedded extraction sets. Enables `jali` (with Jali's `serde`, which loads the embedded parameter sets) and `ntru-trapdoor`. Jali and `ntru-trapdoor` come from crates.io, pinned to one release each (Jali `=0.3.0`, `ntru-trapdoor` `=0.1.1`). |
| `lattice-plain` | no | The lattice instantiation with plain Fiat–Shamir proofs instead of the straight-line extractable ones, extracted by rewinding only. The proofs are several times shorter. It changes the lattice proofs and the digest of the lattice `pp`, so every party of a deployment builds with the same choice. Enables `lattice`. `lattice-extractable` overrides it. The pairing instantiation is unchanged. |
| `lattice-extractable` | no | The straight-line extractable proofs that `lattice` proves by default, kept for the commands of earlier versions. Overrides `lattice-plain`, so a build with every feature is extractable. Enables `lattice`. |

The crate's dev-dependency on itself enables `test-utils`, `serde`, `jali` and `lattice`, so
`cargo test` compiles everything, and a normal build contains none of them. `cargo test` runs the
suite in the default, extractable build, and `cargo test --features lattice-plain` in the plain
build.

## Building and testing

Rust 1.95.0 or higher (edition 2024). The crate is on
[crates.io](https://crates.io/crates/predicate-credential-system), released from this repository
by release-plz ([RELEASING.md](./RELEASING.md)).

```bash
cargo build
cargo test                         # unit, integration and documentation tests
cargo test --doc --all-features    # the documentation tests, this README included
cargo test --test ietf_vectors     # the test vectors of the IETF CFRG drafts (kat/ietf/)
cargo bench --bench pcreds         # Π_PCreds at k = 5 for every pairing-based base/tag pair
cargo bench --bench kiprf          # Tag_DDH and Tag_DY
cargo bench --bench lattice --features lattice   # the lattice instantiation; about 12 minutes at one thread
```

Each benchmark first prints the sizes of the objects it handles. For stable numbers pin
`cargo bench --bench pcreds` to one core (on Linux `taskset -c N`) and record `rustc --version`
and the commit. What each suite and each benchmark covers:
[Testing and benchmarks](./docs/testing-and-benchmarks.md).

`cargo test` also runs the light tests of the lattice instantiation. Its end-to-end flows and
attacks run Jali proofs of seconds and up to about 0.7 GB each, so they run in release, one at a
time:

```bash
cargo test --release --features lattice --test lattice_protocol   # the k = 1 flow, about a minute
cargo test --release --features lattice --lib pcreds::lattice      # the relations with real proofs
RUST_TEST_THREADS=1 cargo test --release --features lattice \
    --test lattice_protocol --test lattice_flows --test lattice_adversarial \
    --test lattice_attacks --test lattice_sizes -- --include-ignored --nocapture   # flows, attacks, sizes
cargo test --release --features lattice --test pcreds_correctness lattice  # the generic tests
RUST_TEST_THREADS=1 cargo test --release --features lattice,parallel \
    --test lattice_parallel -- --include-ignored   # attestations in parallel; run it without, too
```

They run the default, extractable build. The same commands with `--features lattice-plain` in
place of `--features lattice` run the plain build, whose proofs are shorter.

### Continuous integration

`.github/workflows/pcs.yml` runs on Ubuntu with Rust 1.95.0 and stable, on every change to the
sources, tests, benchmarks, `Cargo.toml`, `Cargo.lock`, `.cargo/`, this README and `docs/` (the
README and `docs/operating-a-helper.md` are compiled as doctests):

```bash
cargo fmt --all -- --check
cargo clippy --locked --all-targets --all-features -- -D warnings   # the extractable build
cargo clippy --locked --all-targets --features serde,jali,lattice-plain,parallel,test-utils -- -D warnings
cargo test --locked
cargo test --locked --features lattice-plain
RUSTDOCFLAGS='-D warnings' cargo doc --locked --no-deps --features serde,jali,lattice
RUSTDOCFLAGS='-D warnings' cargo doc --locked --no-deps --features serde,jali,lattice-plain
cargo test --locked --release --features lattice --test lattice_protocol quick_end_to_end_k1
cargo test --locked --release --features lattice --lib proofs_are_in_the_mode_of_the_build
cargo test --locked --release --features lattice-plain --test lattice_protocol quick_end_to_end_k1
cargo test --locked --release --features lattice-plain --lib proofs_are_in_the_mode_of_the_build
```

The last four commands (the job `lattice`) run the lattice flow at `k = 1` with real Jali proofs
in both builds, and check that each build proves and verifies in its own mode only. The other
heavy lattice tests are not part of CI. Run the same commands before proposing a change.

## Documentation

```bash
cargo docs
```

builds the API documentation with the `serde` layer, the `jali` re-export, the lattice
instantiation and rendered formulas, and opens it. It is an alias (`.cargo/config.toml`) that hands
`docs/katex-header.html` to rustdoc, as the `[package.metadata.docs.rs]` section of `Cargo.toml`
does for docs.rs. Formulas are written inside code (`` $`…`$ `` inline, `math` code blocks for
display) and rendered with [KaTeX](https://katex.org) loaded from a CDN; a plain `cargo doc`
shows their LaTeX source. The guides are in [`docs/`](./docs/README.md).

## Security notes and limitations

- **Research artifact.** Not audited, and we do not claim any constant-time behaviour.
- **Plain Fiat–Shamir, not the NIZK the theorem assumes.** Theorem "Security of `Π_PCreds`"
  (§4.3) assumes an online simulation-extractable NIZK (Def. "Online simulation-extractable
  NIZK", §2.4). The paper states that the usual Fiat–Shamir extractor rewinds, whereas its
  definition requires extraction without rewinding; it names Fischlin's transform and an analysis
  of Fiat–Shamir in the algebraic group model as approaches to online extraction, notes that
  online extraction alone does not give extraction after simulated proofs of false statements,
  which its relations need, and computes its cost estimates with plain Fiat–Shamir (§2.4,
  "Instantiations"). For the pairing instantiation this crate implements plain Fiat–Shamir only
  (the challenge hashes the context, the complete statement and the commitment). Neither approach
  is implemented or shown here to cover the relations of this crate (which include equations in
  `G_T`). The lattice instantiation proves in Jali's straight-line extractable mode, and with
  plain Fiat–Shamir as well when it is built with the feature `lattice-plain` (below). The tests check algebraic and structural facts on
  sampled instances, not the theorem.
- **The helper's decisions are inputs.** Root admission (`Decision::Root`) issues regardless of
  the policy; the integrity guarantees are relative to the root admissions of the honest helper
  (Remark "Root users and chaining"). Never derive the decision from the request.
- **At most once per identifier, as durable as the store.** `respond` records `id_Q` in the
  helper's `IssuanceStore` with one test-and-set before `BlindIssue` runs and releases nothing if
  the store fails. The default `IssuanceRecord` lives in memory: persist it, or implement the
  trait on durable storage ([Operating a helper](./docs/operating-a-helper.md)).
- **One deployment per object, one helper key per user.** The helper's key, a checked
  `HelperKey`, users, pending attestation requests and issuance states carry the digest of their
  `pp`, and every algorithm refuses them under another `pp`. A user's identifier is an evaluation
  at the identifier point `x_0 = H_id(⟨hvk⟩)` of ONE helper key, so a `User` (and a pending
  attestation request) also carries the fingerprint of its key and is refused under another; a
  user who reuses its key with another helper registers again (`register_reusing`). A `Σ-PS`
  credential is a signature under `hvk` and nothing else: do not serve two deployments with one
  key.
- **Attestations have no session context** (§4.2: "the attestation may be used in several
  credential requests"); they are bound to `pp`, `hvk` and the recipient's identifier through
  `x_Q`, and an attester answers only a request whose `π_id` it checked.
- **Received objects are re-validated.** Every algorithm checks that the group elements it
  receives are on the curve and in the prime-order subgroup and that tags lie in `T`, whatever
  way the object was built; decoding is validated and rejects trailing bytes. The helper accepts
  a request with `k` or more distinct valid tags among any number of attestations; it may limit
  that number as an operational bound on its work (`Policy::with_max_attestations`; no limit by
  default).
- **Not implemented:** revocation and expiry, the additional attributes of Remark "Additional
  attributes", threshold issuance, the SNARK-based variant, online-extractable proof compilers
  for the pairing instantiation.
- **Zeroization.** Secrets owned by the crate are wiped on drop (`zeroize`), print as
  `<redacted>` and are not `Clone` (the credential excepted), but field elements are `Copy` and
  temporaries may remain on the stack.
- **No unsafe code**: `#![forbid(unsafe_code)]`.
- **The lattice instantiation**: no theorem of the current paper covers it as implemented.
  Corollary "cor:pcs-instantiations" (iii) is stated for an online-extractable argument system,
  and Jali's proofs are its straight-line extractable proofs (Katsumata's transform), whose
  extractor neither rewinds nor queries the random oracle, after simulated proofs of other
  statements and contexts (with the feature `lattice-plain` they are Fiat–Shamir proofs
  extracted by rewinding). Jali argues this in the classical random-oracle model
  only, and as an outline with the status of each step, so the hypothesis is targeted but not
  established. The extraction of `s ≠ 0`
  rests on the lower-bound argument of §5.2.3, and the one-more
  vSIS assumption is not estimated at these parameters. Jali, `SampPre`
  and `TrapGen` run in variable time. The helper's RNG must be the operating system's CSPRNG (the
  trapdoor is a function of it). A helper key answers at most `Q_max = 2^48` issuances and counts
  them in its encoding: run one live instance per key and store it before issuing
  (`Helper::to_bytes_reserving`). See
  [Operating a helper](./docs/operating-a-helper.md#the-lattice-instantiation-feature-lattice)
  and [Design notes](./docs/design-notes.md#the-lattice-instantiation-feature-lattice).

## Additional resources

- [Operating a helper](./docs/operating-a-helper.md)
- [Design notes](./docs/design-notes.md)
- [Encodings and interoperability](./docs/encodings.md)
- [Testing and benchmarks](./docs/testing-and-benchmarks.md)
- [OpenVTC integration](./docs/openvtc-integration.md)
- [`demo/`](./demo/README.md) — a throwaway prototype of hidden-vetter admission on top of this
  crate's `pcreds`, with application contexts. A workspace member, not published

## License

Licensed under [MIT](./LICENSE).
