# OpenVTC Integration

How this library could be integrated into [OpenVTC](https://github.com/OpenVTC/openvtc). This is
a proposal: nothing of it exists in OpenVTC today. Statements about OpenVTC refer to its
repository at commit `3329195` (2026-09-19) and to the crates it links (`vta-sdk` 0.43,
`dtg-credentials` 0.9, `affinidi-data-integrity` 0.7). They were verified there by the earlier
revision of this document; for this revision a few were checked again at that commit (the
dependency policy of `deny.toml`, `rust-version`, the join submission's `extensions`, the 1 MiB
message guard, the inbound type filter, `spawn_blocking` for Argon2id). That code base moves
quickly, so re-check before building on a detail. The community service (VTC) lives in another
repository (`OpenVTC/verifiable-trust-infrastructure`), which was not reviewed: everything about the
helper side is derived from OpenVTC's client code and design documents.

Each section says what was **verified** (read in the code, or run) and what is **proposed**. The
library side refers to the protocol module `pcreds` (`Π_PCreds` of the paper, §5.2).

## Where the library fits

The library lets a helper issue a credential once `k` distinct credentialed users attested for
the requester, without learning who they are, and lets a credential holder prove anonymously
that a message comes from a credentialed user. OpenVTC has one flow with the first shape, and it
is not the VRC exchange:

- **Vetted admission** (`docs/design/vetting-process.md`): a community admits an applicant on
  `minStatements` vetting statements from distinct eligible vetters. A statement is an
  endorsement credential (VEC) that names the vetter's member DID in the clear, by decision D7
  of that document. Its roadmap lists "k-of-n proofs over hidden vetters" as a later item. That
  is the place for this library. (Verified.)
- **VRCs** are not consumed by any join, personhood or presentation path, and since pairwise
  relationship DIDs became the default a VRC no longer names either persona. They are not a
  suitable carrier. (Verified.)

| Library (`pcreds`) | OpenVTC |
|---------|---------|
| the helper (`Helper`, published `hvk`) | the community service (VTC); one helper key per community |
| the deployment label of `Setup` | the community's VTC DID, plus a version string |
| a user (`User`: `usk`, `id`) | the applicant's per-community persona; `usk` is a NEW local secret, `id` is bound to the persona DID at the message layer |
| a contact name `P̃` | the route through which an applicant reaches a vetter (the vetter's DID or another handle the contact mechanism resolves) |
| `ssid` | the identifier of the exchange (the DIDComm thread) |
| root admission (`Decision::Root`) | admission by invitation (VIC) or personhood (PHC): the VTC decides after its existing check |
| an attestation | replaces the vetting statement that names the vetter |
| `Policy::threshold(k)` | `minStatements` of the join policy |
| `request_credential` → `evaluate_request` → `respond` → `unblind` | join request submit → verdict → credential delivery |
| a membership proof (`prove` / `verify`) | an anonymous "a member of this community said `m`" (no OpenVTC flow uses it today) |
| the issued credential | kept by the new member, used to attest for later applicants and for membership proofs |

Two consequences must be decided by the OpenVTC maintainers before any code is written:

- **Vetter accountability.** The vetting design wants ACCOUNTABLE vetters: the VTC counts distinct
  vetters by member record and applies velocity caps and cascade review per vetter. With this
  library the VTC learns `id_Q`, the tags of the request and the policy result: it sees which
  attestations of ONE request share a source, but tags of one vetter for two applicants are
  unlinkable by design, so per-vetter velocity caps and cascade review are not possible.
- **Who may vet.** A credential certifies `usk` alone, with no attribute: every holder of a
  credential under `hvk` counts as an attester. OpenVTC's "eligible vetters" (today the
  `CommunityRole: vetter` endorsement) cannot be expressed. The paper describes the extension
  (Remark "Additional attributes"); the library does not implement it.

## Packaging

- **Source.** OpenVTC's `deny.toml` denies git dependencies (`unknown-git = "deny"`) and
  registries other than crates.io. (Verified.) Every dependency of this crate comes from
  crates.io, including the optional Jali 0.3.0 and `ntru-trapdoor` 0.1.1 (feature `lattice`),
  so `cargo package` accepts the manifest. (Verified with Jali 0.1.1, with Jali 0.2.0 on
  2026-11-15, and with Jali 0.3.0 on 2026-11-16.) The crate is on crates.io, released from
  this repository by release-plz ([RELEASING.md](../RELEASING.md)), and vendoring it as a
  workspace member remains an alternative.
- **Licence.** This crate is MIT, which is on their allow-list for dependencies. Vendoring the
  sources into the Apache-2.0 workspace is a separate decision.
- **Toolchain.** Edition 2024 and `rust-version = "1.95.0"` on both sides. (Verified.)
- **Footprint.** Measured for the earlier version of this crate, whose dependencies are
  unchanged: added as a dependency of `openvtc-core`, it brought 13 new packages (the arkworks
  stack), no duplicate versions, and built without warnings; the `serde` feature adds no package,
  because `serde` and `multibase` are already in their graph.
- **Feature gate.** Put the integration behind a non-default cargo feature of `openvtc-core`,
  e.g. `pcreds`, as they do for `openpgp-card`. (Proposed.)
- **CI.** Their pipeline runs fmt, clippy with `-D warnings`, rustdoc with `-D warnings`,
  `cargo deny`, an MSRV job, and tests on Linux, macOS and Windows. This crate's workflow runs
  fmt, clippy, the tests and rustdoc on Ubuntu with Rust 1.95.0 and stable; Windows is untested.

## Client side: a `pcreds` module in `openvtc-core`

Proposed. The `openvtc` crate is a binary, so testable logic belongs in the core crate.

- **Received parameters.** The client accepts a community's `pp` only through
  `Protocol::from_public_parameters(pp)`, which recomputes `Setup` from the label and compares,
  and its `hvk` only through `Protocol::helper_key(vk)` (`hvk ∈ V_pp`), once per process: a
  `HelperKey` is not decodable, so after a restart the client checks the stored `vk` again. For a
  community that runs `Σ-BBS` under IETF parameters, the client recomputes them
  (`BBSParams::ietf`) and calls `from_public_parameters_with_params`.
- **What the client stores, per community.** The secrets are `User` (`usk`, `id` and the digest
  of `pp`), the `Credential` once issued, and one `IssuanceState` per credential request until the
  VTC answers (as secret as `usk`: it holds `τ`). Each has a wiped encoding (`to_bytes()`
  returns a buffer that is wiped on drop; the way back is `WireFormat::from_bytes`, followed by
  `Protocol::check_user` / `Protocol::verify_credential` for a value read from storage) and, with
  the feature `serde`, a JSON form through the wiping `serialization::secret` adapter (one
  multibase string; serialize a `Σ-PS` credential as the `Credential` wrapper, not as the bare
  `PSPair`). They belong in OpenVTC's encrypted `ProtectedConfig` or the OS keyring
  (`SecuredConfig`), next to the other secrets. The client also keeps its attestations, the
  first one per tag (public objects, but they link the applicant to the community), and `pp` and
  `hvk`.
- **Key custody.** Generate `usk` locally with `Protocol::register` and never hand it to the
  VTA. New OpenVTC profiles are VTA-backed: the VTA generates and stores persona keys, can sign
  as the user and sees the relationship graph, by written design. Tags are deterministic in
  `usk`, so a VTA that held `usk` could link every attestation of its user. The VTA key types
  (Ed25519, X25519, P-256, ML-DSA) have no scalar-field key anyway, and an OpenPGP card cannot
  run these protocols, so `usk` cannot live on one.
- **Binding `id` to the persona.** The library has no notion of a DID. Bind the two at the
  message layer: the persona key signs `(id, community, purpose)` as a Data Integrity proof, and
  every message that carries `id` travels authcrypt from the persona DID, as the join request
  already does. `id` is ONE identifier per user and community, disclosed to every vetter and to
  the VTC: colluding vetters can link the requests of one applicant, whatever pairwise DIDs it
  uses towards them ("A user's identifier links its requests at its attesters and the helper",
  §5.1).
- **Calls.** Randomized algorithms take `rand::rngs::OsRng` (rand 0.8), the generator OpenVTC
  uses everywhere. (Verified at `3329195`.) Proving and verifying cost pairings (the paper
  reports, on one core at 2.2 GHz, about 5 to 9 ms for an attestation and 27 to 30 ms for the
  VTC's check of a request at `k = 5`; §7.1): run them through `tokio::task::spawn_blocking`,
  the pattern OpenVTC uses for Argon2id, never on the event loop.

## The flows

With `pcreds = Protocol::<Bk>::from_public_parameters(pp)?` and `hvk = pcreds.helper_key(&vk)?`
on every client, and the VTC's own `Protocol` and `Helper`:

| step | who | call | wire |
|---|---|---|---|
| registration | applicant | `register(&mut OsRng)` → `User`; store `user.to_bytes()` | none |
| attestation request | applicant, to a vetter's contact name | `request_attestation(&user, ssid, contact, rng)` → `AttestationRequest` | `{"id", "proof"}` |
| receipt | vetter | `receive_attestation_request(&request, ssid, own_contact)` → `PendingAttestation`: `π_id` checked, `id_Q` known | none |
| attestation | vetter, after vetting the applicant out of band | `attest(&hvk, &me, &my_cred, &pending, rng)` → `Attestation` | `{"tag", "show", "proof"}` |
| check | applicant | `check_attestation(&hvk, user.id(), &att)`; keep the first attestation per tag | none |
| join submit | applicant, to the VTC | `request_credential(&hvk, &user, attestations, ssid, rng)` → `(CredentialRequest, IssuanceState)`; store the state | `{"id", "attestations": […], "request", "proof"}` |
| verdict | VTC | `evaluate_request(&helper, &request, ssid)` → `EvaluatedRequest` (`id()`, `tags()`, `is_valid()`), then `respond(&mut helper, evaluated, decision, rng)` → `Reply` | `"fail"`, `"issued"` or `{"preCredential"}` |
| delivery | applicant | on a pre-credential: `unblind(&hvk, &user, &pre, &state)` → `Credential` (verified; fails closed); store it | none |
| membership proof | member | `prove(&hvk, &user, &cred, m, rng)` → `MembershipProof`; anyone: `verify(&hvk, m, &proof)` | `{"show", "proof"}` |

Rules at the seams:

- **The vetter passes ITS OWN contact name** (the one the request arrived through) and the
  `ssid` of the exchange to `receive_attestation_request`, never values taken from the request:
  `π_id` is bound to `(ssid, P̃)`. A vetter that answers later keeps the `AttestationRequest`
  and receives it again (`PendingAttestation` is not decodable).
- **The VTC evaluates and answers in one go.** `EvaluatedRequest` is not decodable either: a VTC
  that answers later keeps the `CredentialRequest` and evaluates it again under the same `ssid`.
- **`"issued"`** means that the identifier holds a credential already: a client that holds one
  ignores it; one that does not lost the earlier reply, and the identifier is spent unless the
  VTC re-delivers the stored `σ̂` (see [Operating a helper](./operating-a-helper.md)).
- **`"fail"`**: fewer than `k` distinct valid attestations. An attestation that does not verify
  is not an error of `evaluate_request`: it is not counted. The applicant may gather more and
  send a new request (new `ssid`, new `IssuanceState`).

```text
applicant                          vetter_1 … vetter_k                  VTC (helper)
    |  manifest request ----------------------------------------------------->|
    |<------------------------------------------ pp, hvk, suite, k (policy) --|
    |  attestation request {id, proof} ---->|                                 |
    |                                       |  receive (checks π_id)          |
    |                                       |  vets the applicant             |
    |<------------------ {tag, show, proof} |  attest                         |
    |  check_attestation, keep one per tag                                    |
    |  join submit {id, attestations, request, proof} in extensions --------->|
    |                                  evaluate_request, decision, respond    |
    |<------------------------------- "fail" / "issued" / {"preCredential"} --|
    |  unblind (fails closed), store the credential                           |
```

## Messages

Proposed. Everything in OpenVTC is JSON over DIDComm or TSP, with multibase base58btc for
binary values; the `serde` feature produces exactly that: the messages are JSON objects with
camelCase members whose leaves are multibase base58btc strings (`z…`) of the canonical encodings,
and every other object is one such string ([Encodings](./encodings.md)):

```text
AttestationRequest   { "id": "z…", "proof": "z…" }
Attestation          { "tag": "z…", "show": "z…", "proof": "z…" }
CredentialRequest    { "id": "z…", "attestations": [ <Attestation>, … ], "request": "z…", "proof": "z…" }
Reply                "fail" | "issued" | { "preCredential": "z…" }
MembershipProof      { "show": "z…", "proof": "z…" }
```

Decoding is strict (base58btc only, validated canonical bytes, no trailing bytes, a message only
as an object with exactly its members, each once, and a reply only in its three forms). At
`k = 5` a credential request came to about 2.2 KB of JSON for `Σ-PS` and 3.6 KB for `Σ-BBS`
(measured on seeded instances), far below OpenVTC's 1 MiB message guard. A policy
engine can read the tags of a request without decoding group elements; the VTC's verdict needs
`evaluate_request` all the same. The post-quantum backend (feature `lattice`) fits these
carriers only at small `k`: an attestation is about 120 KB of JSON and a credential request at
`k = 5` about 665 KB, so by the same per-attestation size a request with more than eight
attestations would exceed the 1 MiB guard, and base58btc takes seconds for strings of this length
([Encodings](./encodings.md#json)). (Measured here at `k = 5`, extrapolated beyond; not tried in
OpenVTC.)

| Step | Carrier |
|------|---------|
| community parameters: `pp`, `hvk`, the suite (base and tag), `k` | the `vetting` object of the join manifest |
| attestation request, applicant → vetter | new peer message next to `vetting/request` |
| attestation, vetter → applicant | new peer message; replaces the vetting statement |
| join submit: the credential request | the join submission's `extensions` member, an open JSON member that is already on the wire |
| reply, VTC → applicant | new message next to `credential-exchange/issue` |

New DIDComm types must match OpenVTC's inbound type filter, which admits
`https://trusttasks.org/spec/vetting/*`, `https://trusttasks.org/spec/vtc/*`,
`https://firstperson.network/*` and `https://linuxfoundation.org/openvtc/*`, and need an arm in
its dispatch chain; a new Trust Task additionally needs a published spec. (Verified.)

The credential itself never needs a W3C envelope: it is used to attest and to prove membership,
and neither reveals it. `DTGCredential.proof` is one `DataIntegrityProof` with a closed
cryptosuite enum, so a proof object of this library does not deserialize there. (Verified.) If a
community wants the membership to be visible as a VC, it keeps issuing its VMC as today, next to
the `pcreds` credential.

## Errors to map

Map `predicate_credential_system::Error` into one variant of `OpenVTCError` (`thiserror`). The
type carries static descriptions, lengths and indices only, never key material or witness values.
It is `#[non_exhaustive]`: match with a wildcard arm. The variants the `pcreds` API returns:

| `Error` | raised by | meaning, and what to do |
|---|---|---|
| `InvalidPublicParameters(_)` | `from_public_parameters*` | the received `pp` is not what `Setup` derives: refuse the community's manifest |
| `InvalidKey` | `helper_key`, every call with a helper key, `restore_helper`, `helper_from_key_pair`, `respond` | `hvk ∉ V_pp`, a key or helper of another deployment, or a request evaluated by another helper: configuration error |
| `IdentifierMismatch`, `IssuanceStateMismatch` | calls with a user or state, `check_user`, `unblind` | a stored user or state of another deployment or user: storage corruption or a mix-up |
| `InvalidGroupElement(_)`, `InvalidTag` | every check of a received object | a malformed or inadmissible identifier, tag, show, request or pre-credential: reject the message |
| `InvalidProof`, `InvalidCredential`, `InvalidIssuanceEncoding` | `receive_attestation_request`, `check_attestation`, `evaluate_request`, `check_membership` | the proof or the public checks fail (wrong `ssid` or contact name, tampering, another key): reject the message |
| `TooManyAttestations { max, actual }` | `evaluate_request` | only if the VTC set a limit on the attestations of a request (`Policy::with_max_attestations`): the request is longer; the applicant sends at most `max` |
| `InvalidPreCredential` | `unblind` | the VTC's answer does not give a valid credential: report the VTC |
| `Storage(_)` | `respond` | the VTC's issuance store failed and nothing was released: retry later |
| `UndefinedTag` | `register`, `user`, `attest` | `Tag(usk, x) = ⊥` (for `Tag_DY` with probability about `1/p`): for `attest`, the vetter cannot attest for this applicant with this key |
| `ZeroThreshold`, `DegenerateInput(_)`, `HashToCurve(_)` | `Policy::threshold`, `with_max_attestations`, `Setup` | configuration error |
| `WitnessDoesNotSatisfyRelation` | `attest`, `prove` | the credential does not belong to the user under `hvk` (with `Σ-BBS`, `attest` returns an attestation that every verifier rejects instead): a bug or a corrupted store |
| `Serialization(_)`, `TrailingBytes`, `LengthMismatch { .. }` | decoders | a malformed encoding: reject the message |

## Helper side: the VTC

Proposed, and subject to the rules of [Operating a helper](./operating-a-helper.md):

- **One helper key per community**, generated with the operating system's CSPRNG, stored as
  `Helper::to_bytes()` (secret) and restored with `Protocol::restore_helper`; the library refuses
  it under another `pp`.
- **The policy** is `Policy::threshold(minStatements)`, the VTC's own input, with the default cap
  of `k` attestations per request.
- **The issued identifiers `I`** live in the VTC's database: implement `IssuanceStore` with one
  atomic insert-if-absent that is committed before `record` returns, so that two VTC processes
  never both issue to one identifier, and fail rather than forget.
- **Verdict.** Run `evaluate_request` before the Rego policy and hand it facts, e.g. that the
  issuance proof verified, the number of distinct valid tags `tags().len()` and `is_valid()`.
  Answer with `Decision::Policy`; a `"fail"` needs no further input.
- **Root admission** with `Decision::Root`, only behind the existing invitation or personhood
  check, never on a request alone.
- **Rate limits.** Every request costs the VTC one issuance proof and up to `k` attestation
  verifications; rate-limit by `id` (public in every request), and answer only after
  `evaluate_request` (an `"issued"` to an unverified request would tell any vetter, who knows
  `id`, whether the applicant is a member).

## Choice of instantiation

`Σ-BBS` with `Tag_DDH` aligns with the BBS work that exists upstream (`affinidi-bbs`, the
`bbs-2023` cryptosuite). With `BBSParams::ietf(interface, &hvk, header)` (module
`pcreds::pairing::ietf`, not part of the paper) the generators are the IETF ones and a credential
is an IETF BBS signature on `(usk, ρ)`; according to `tests/bbs_ietf_interop.rs`, credentials of
the blind interfaces cross both ways with `affinidi-bbs` 0.3.3. Presentations do not: an
attestation or a membership proof of this crate is not an IETF BBS proof (the possession proof has
a third clause and its own challenge and layout), and the per-verifier pseudonym is not
`Tag_DDH`. Under IETF parameters `h_0` depends on the helper's key, while the paper's lemma on
`Σ-BBS` takes `pp` before the key; that the lemma carries over is not claimed
([Encodings](./encodings.md)). `Σ-PS` with `Tag_DDH` is the paper's main instantiation and has the
smallest messages (and, the paper notes, threshold issuance comes almost for free for PS). Both
work with everything above; the suite is one field of the community parameters (it enters the
digest of `pp`).

## What is missing

In the library:

- **Attributes**, for "who may vet" and membership classes (Remark "Additional attributes").
- **Freshness of attestations.** OpenVTC binds vetting material to a request id, an audience and
  a validity window of minutes. Attestation requests and credential requests carry an `ssid`
  (bound into `π_id` and `π_iss`), which can be the request id. Attestations carry no session
  context by design and remain valid for their recipient, which issuance once per identifier
  limits. They can carry an application context instead (`attest_in_context`, an
  implementation note for OpenVTC that is not in the paper), such as a validity window, which
  the recipient and the helper check against their own copy. The demo binds each statement's
  metadata this way.
- **Revocation and expiry.** OpenVTC credentials carry status entries and validity intervals.
  The library has neither.
- **Platforms and review.** Tests on Windows, and a security review.

In OpenVTC: a home for `usk` outside the VTA, the message types above, the VTC-side store,
verifier and policy facts, and the decisions on vetter accountability and on who may vet.

## Suggested order of work

1. Decide on vetter accountability and on who may vet; decide on publishing or vendoring the
   crate.
2. Run the crate's test suite on Linux, macOS and Windows.
3. Add the `pcreds` module to `openvtc-core` behind a feature: state, storage, JSON, a local
   end-to-end test with three clients and a mock VTC.
4. Specify the messages and implement them on both sides, starting with root admission.
5. Implement the VTC's `IssuanceStore` on its database, wire `evaluate_request` into the policy
   evaluation, and define the operating procedures.
