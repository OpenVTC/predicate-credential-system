# Design Notes

How the protocol module `pcreds` is put together, and why: the design of the migration from the
earlier, game-based construction (the deleted modules `pcs` and `cred`) to the protocol
`Π_PCreds` of the current paper (§5.2). None of this changes what honest parties compute; each
point records a rule the code keeps or a choice the paper leaves open. The lattice backend
(feature `lattice`), the second backend of the same protocol, is described at the end.

## One state machine over a `Backend`

"The protocol uses a credential base `Σ` (Def. "Credential base") that certifies the user's tag
key `usk`, a key-injective PRF `Tag` (Def. "Key-injective PRF"), and an online
simulation-extractable NIZK" (§5.2). The trait `pcreds::Backend` is exactly one such triple,
together with the algebra its proofs run over, and `pcreds::Protocol<Bk>` is written once over
it, as the protocol box is written once over `Σ`, `Tag` and the NIZK.

| the box uses | `Backend` |
|---|---|
| `pp_Σ`, `pp_Tag`; `H_id` and `H_req` onto `X`, the rule `x_Q ≠ x_0` | `Params`, `setup`, `check_params`; `identifier_point`, `request_point`, `same_point` |
| `TagKeyGen`, `TagEval`, `t ∈ T` | `tag_keygen`, `tag`, `check_tag`; types `UserKey`, `Point`, `Tag` |
| `Σ.KeyGen`, `V_pp` | `keygen`, `check_key`, `key_pair_matches`; types `VerificationKey`, `SigningKey` |
| the issuance cap of `Σ-vSIS` (§5.2.3, "Issuance cap") | `signing_key_bytes_reserving`, `check_issuance_capacity` (asked before the record); `blind_issue` refuses at the cap |
| `Σ.PrepareIssue`, `Σ.BlindIssue`, `Σ.Unblind`, `Σ.Verify` | `prepare_issue`, `blind_issue`, `unblind` (fails closed), `verify`; types `Request`, `IssuanceTape`, `PreCredential`, `Credential` |
| the NIZK for `R_Tag`, `R_att`, `R_iss`, `R_Possess` | `prove_tag` / `check_tag_proof`, `prove_attestation` / `check_attestation_proof`, `prove_issuance` / `check_issuance_proof`, `prove_possession` / `check_possession_proof`; types `Show`, `Proof` |
| "parse each proof in a fixed format" (§7.3) | `ProofKind`, `serialize_proof_compact`, `deserialize_proof_compact`, `proof_compact_size` |

Why one trait rather than one implementation per instantiation:

* **One state machine.** Everything the protocol box adds to its building blocks (the
  identifier proof and its context, the recipient point, counting distinct tags, the policy, the
  issuance record, the decision `d`, failing closed in `Unblind`, the deployment binding) is
  written once, in `pcreds::protocol` and `pcreds::context`, and so is every rule of the
  following sections. The earlier code had the protocol logic twice, in `pcs::construction`
  (pairings) and `pcs::lattice` (lattices), and its rules had to be kept twice.
* **Both instantiations fit.** A backend contributes types and algebra only. The lattice
  backend ([below](#the-lattice-instantiation-feature-lattice)) has points that are not scalars
  (inputs of a matrix oracle), tags that are vectors, proofs that are not `(c, z)` pairs and an
  empty show (`Show` is "empty for a base whose signatures do not re-randomize"). Its port asked
  three things of the trait and of the protocol, none of which changes what honest parties
  compute: `Send + Sync` public types (for the parallel verification of attestations), the hook
  `signing_key_bytes_reserving` for a key that counts its issuances, and `BlindIssue` before the
  issuance record in `respond`
  ([below](#the-issuance-record-blindissue-then-one-test-and-set)).
* **The contract is the trait's.** The `check_*` functions are deterministic, never panic on
  adversarial input, re-validate every value they are given and name the reason of a rejection;
  the `prove_*` functions refuse a witness that does not satisfy their relation
  (`Error::WitnessDoesNotSatisfyRelation`). `Protocol` relies on nothing else.

`PairingBackend<E, B, T>` composes a credential base `B: Base<E>` (`PS`, `BBS<H>`), a tag
`T: ProtocolTag<E::G1>` (`DDH`, `DY`) and the sigma layer with Fiat–Shamir. In every relation
`usk` is variable 0, shared by the clauses of the base and the tag clause, so one response
covers it (witness-preserving AND composition); the base allocates its further variables after
it (`Base::POSSESSION_VARIABLES`, `Base::ISSUANCE_VARIABLES`), and the number of responses of a
proof (`PairingBackend::responses`) is a constant of the base and the proof's kind, which is
what makes the compact format decodable without a length. The relation builders
(`identifier_relation`, `attestation_relation`, `issuance_relation`, `possession_relation`) are
public, because a test harness that runs the interactive protocol, its simulator and its
extractor needs exactly the relations the proofs use.

## Type-state hardening

Three values can only be produced by the check they stand for. They have private fields, no
public constructor and, deliberately, no decoder.

* **`HelperKey`: `hvk` checked once.** "Users return `⊥` if `hvk ∉ V_pp`" (protocol box).
  `Protocol::helper_key(vk)` runs that check (validity of every group element, and the
  admissible-key test of the base: for `Σ-PS` `Y ≠ 1`, `Ỹ ≠ 1` and `e(Y, g̃) = e(g_1, Ỹ)`, a
  pairing product) and returns a `HelperKey` that carries the digest of its `pp`. The helper's
  own key generation produces one for the key it generates, and `restore_helper` and
  `helper_from_key_pair` after the same check of `hvk` and a check that `sk` belongs to it. Every other algorithm takes a
  `&HelperKey` and compares 32 bytes instead of checking the key again. It is not decodable:
  whoever receives `hvk` checks it.
* **`PendingAttestation`: `attest` only on a verified `π_id`.** `receive_attestation_request`
  checks `id_Q ∈ T` and `π_id` under `(ssid, P̃)` and returns the pending request; `attest` takes
  nothing else. This protects attester anonymity: the attestation tag
  `t_{P→Q} = Tag(usk_P, x_Q)` is DETERMINISTIC in the attester and the recipient, and the helper
  sees `id_Q` and the tags of `Q`'s request. An attester that attested for an identifier without a
  proof of ownership would let anybody who knows `id_Q` (the helper, any other attester) ask it
  for an attestation for `id_Q` and compare its tag with the tags of `Q`'s request, learning
  whether it attested for `Q`. With the gate, only the owner of `usk_Q` obtains attestations for
  `id_Q`, and `π_id` is bound to the contact name and the session through which it arrived.
* **`EvaluatedRequest`: `respond` only on a checked `π_iss`.** `evaluate_request` checks
  `id_Q ∈ T` and `π_iss` under `(ssid, att⃗)`, computes `N''` and `v`, and retains
  `(ssid, id_Q, Ĉ)`; `respond` takes the evaluated request by value and runs `BlindIssue` on
  exactly its `Ĉ`. This is the paper's lesson "Issuance must run on the proof" (§7.3) made a
  type. An evaluated request is bound to the helper that evaluated it (a fingerprint of `pp` and
  `hvk`, oracle `/PCREDS-HELPER`), and it is not decodable: a helper that wants to answer later
  keeps the `CredentialRequest` and evaluates it again, because a stored "valid" flag would be an
  admission that nobody checked.

The secrets (`User`, `Credential`, `IssuanceState`, the helper's `sk`) are wiped on drop,
redacted in `Debug` and not `Clone` (the credential excepted, as a backup may be wanted); their
encodings come in buffers that are wiped on drop.

## Deployment binding by the digest of `pp`

The digest of `pp` (oracle `/PCREDS-PP` over the deployment label, the name of the backend, its
parameters and `x_0`) is computed once per `Protocol`, leads every proof context, and is carried
by `HelperKey` (hence `Helper`), `User`, `IssuanceState` and `PendingAttestation`. Every algorithm
refuses an object of another deployment (`Error::InvalidKey`, `Error::IdentifierMismatch`,
`Error::IssuanceStateMismatch`). Why:

* `H_1` has no deployment input of its own (module `hash`), so a proof is bound to a deployment
  only through its context, and the algebraic parameters alone do not determine the deployment:
  `pp_Σ` of `Σ-PS` is empty. The digest covers the label explicitly, and the name of the backend
  separates two instantiations under one label.
* A `Σ-PS` credential is a signature under `hvk` on `usk` and nothing else, so a helper key that
  served two deployments would certify, in each of them, the users of the other. The helper's key
  records its digest, and `restore_helper` refuses key bytes of another deployment.
* `Setup` is transparent: `pp_Σ` and `pp_Tag` are derived from the label (for `Tag_DY` the paper
  samples `g_1`; a random oracle on the label realizes it), so
  `Protocol::from_public_parameters` accepts a received `pp` only if it EQUALS what `Setup`
  derives from its label. The identifier point is not in `pp`: "once the helper publishes `hvk`,
  set `x_0 = H_id(⟨hvk⟩)`", so every helper key has its own (`HelperKey::identifier_point`), and
  a `User` belongs to one helper key. Well-formed parameters are not good enough: generators with a known
  discrete-logarithm relation look like any others. Parameters that are not derived from the
  label (`setup_with_params`) are accepted only against parameters the receiver derived itself
  (`from_public_parameters_with_params`).

### Parameters that depend on the helper's key (IETF BBS)

Not part of the paper. `pcreds::pairing::ietf` derives the generators of `Σ-BBS` as the IETF
ciphersuite BLS12-381-SHA-256 does, `h_0 = P_1 · Q_1^{domain}` with `domain` a hash over the
helper's key, the generators and a header, so that a credential `(A, e)` is an IETF BBS signature
on `(usk, ρ)`. Such a deployment exists only after the helper's key: `BBSParams::ietf(interface,
&hvk, header)`, `Protocol::setup_with_params`, the helper from its key pair
(`Protocol::helper_from_key_pair`, which checks the pair and binds it to the deployment), and
receivers recompute the parameters for `from_public_parameters_with_params`. The parameters stay
transparent: every point is a hash-to-curve output of fixed strings or the constant `P_1`, and a
discrete-logarithm relation among `(h_0, h_u, h_r)` is one among `(P_1, Q_1, h_u, h_r)`, which
depend on neither the key nor the header (module docs, "Transparency"). Not claimed: the paper's
lemma on `Σ-BBS` takes `pp` before the key, while here `h_0` is a function of it. Presentations
are not interoperable: the possession proof of `Σ-BBS` has the third clause `D = B̄^u Ā^v` and its
own challenge and layout ([Encodings](./encodings.md)).

## The issuance record: `BlindIssue`, then one test-and-set

The protocol box keeps "the set of issued identifiers `I`": the helper replies `issued` if
`id_Q ∈ I`, "otherwise it adds `id_Q` to `I` and replies `(ssid, σ̂)`", and "an honest helper
records its first issuance to an identifier before releasing the response" (Remark
"Concurrency"). `respond` keeps both rules, in this order:

1. `issued` if `IssuanceStore::contains` knows `id_Q`, before any signature is computed;
2. `σ̂ ← BlindIssue(sk, Ĉ)`;
3. `IssuanceStore::record(id_Q)`, ONE atomic test-and-set: `Ok(true)` only if the identifier was
   absent and is now recorded, durably. An implementation on storage shared by several helper
   processes makes it an insert-if-absent, so that two processes cannot both see an identifier
   as new; the `contains` of step 1 is a shortcut only, which two processes can both pass;
4. `σ̂` only if step 3 returned `Ok(true)`; `issued` if it returned `Ok(false)` (another process
   recorded `id_Q` in between, and this `σ̂` is discarded unreleased); the error, releasing
   nothing, if the store failed: a store that cannot answer must fail rather than forget.

`BlindIssue` runs before the record because it can refuse: the lattice key refuses at its
issuance cap (`Error::IssuanceCapReached`), and a record written first would leave the
identifier spent without a credential. In this order an identifier is recorded only for a
pre-credential that exists, and nothing leaves the helper before its identifier is recorded. A
reply lost after the record was written still leaves the identifier spent; re-delivery is the
deployment's ([Operating a helper](./operating-a-helper.md)). The earlier order (the record,
then `BlindIssue`) relied on `BlindIssue` never failing on an evaluated request, which holds for
the pairing bases only.

Identifiers enter the store as their canonical compressed encoding. The default
`IssuanceRecord` keeps `I` in memory and is canonically serializable, so that a helper can persist
it between runs.

## The number of attestations of a request

`Policy::threshold(k)` refuses `k = 0` ("The threshold policy `Pol_k` never accepts a first
request" holds only for `k ≥ 1`; root users are admitted by `Decision::Root`). `Pol_k` accepts
iff `|N''| ≥ k`, and a request may carry any number of attestations (protocol box: the helper
counts the valid ones among `att⃗`), so by default the helper evaluates every request, whatever
its length. The requester chooses that length and the helper verifies every attestation, so a
helper may set an operational limit (`Policy::with_max_attestations(max)`, `max ≥ k`):
`evaluate_request` then refuses a longer request before it verifies any attestation. The limit
is not part of `Pol_k`, and there is none by default: a default limit of `k` would turn "at
least `k`" into "exactly `k`" for long requests, the rule of the earlier construction (whose
`VerifyProof` took exactly `k` attestations), not of this protocol. The compact decoder never
allocates ahead of the input, and an attestation whose tag is already in `N''` is not verified
again.

## Contexts

The paper gives the contexts as tuples; the code encodes them as SHA-256 transcripts of framed
items, with the digest of `pp` first ([Encodings](./encodings.md), "Oracles and proof
contexts").

* **One oracle per proof.** `π_id`, `π_att`, `π_iss` and `π_prove` are transcripts of four
  different oracles (`/PCREDS-CTX-ID`, `-ATT`, `-ISS`, `-PROVE`), so a proof made for one role
  never verifies in another, whatever the statements are.
* **The paper's contexts.** `π_id` is bound to `(ssid, P̃)`, `π_iss` to `(ssid, att⃗)` with every
  attestation in full and their number first, `π_prove` to the message `m`, and `π_att` to no
  session ("its statement fixes the recipient through `x_Q`, and the attestation may be used in
  several credential requests").
* **Application contexts (implementation note for OpenVTC, not in the paper).** The paper's
  first remedy for replay (Remark "Attestations are standing endorsements") is a context in the
  attestation challenge. `attestation_context_in` appends the caller's bytes `app` as a last
  item of the context of `π_att`, and `issuance_context_in` appends, after the attestations, the
  context of each attestation (`att-app`, one per attestation, in order) and the request's own
  context (`app`) to the context of `π_iss`. The entry points `attest_in_context`,
  `check_attestation_in_context`, `verify_attestation_in_context`,
  `request_credential_in_context` and `evaluate_request_in_context` use them. The helper checks
  each attestation under its own context and `π_iss` under all of them, so a requester cannot
  have an attestation checked under one context and prove under another, and an attestation made
  under another context than the helper's does not count. The bytes are public data that every
  verifier supplies from its own copy, never from the prover. Without them each context is the
  paper's, byte for byte, and `Some(&[])` is a context of its own, distinct from none. Tags do not
  depend on the contexts, so one attester counts once whatever contexts its attestations carry.
  The proofs, their relations and the backends are unchanged: both backends take the context as
  opaque bytes, and binding more public, verifier-recomputed data into it only narrows the
  statements a proof verifies for (the standard argument for labelled proofs, not re-proven
  here). `tests/application_context.rs` checks these properties for both pairing bases.
* **`hvk` in the statement-bearing contexts.** `hvk` is part of the statements of `π_att`,
  `π_iss` and `π_prove` (`(hvk, σ*, t, x_Q)`, `(hvk, Ĉ, id_Q)`, `(hvk, σ*)`), so it enters their
  contexts. Fiat–Shamir absorbs every element and every coefficient of the relation (the strong
  transform, with the instance serialization of `draft-irtf-cfrg-sigma-protocols-04`), but that
  does not always cover the key: the clause of `Σ-BBS` for `Ĉ` is
  `C h_0^{-1} = h_u^usk h_r^ρ`, and none of its bases or targets depends on `hvk = X̃`. Without the
  item, an issuance proof of `Σ-BBS` would verify under every key of the deployment. The three
  possession clauses of `Σ-BBS` do not mention `X̃` either; there the public check
  `e(Ā, X̃) = e(B̄, g̃)` involves the key, and the item binds the proof itself as well. For `Σ-PS`
  the key occurs in the clauses (`Y` in `C = g_1^ρ Y^usk`; `X̃`, `Ỹ` in the pairing clause).
* **The verifier rebuilds every context** from public data and never takes one from the prover
  (a verifier that accepts such a context verifies a proof bound to nothing). The
  context functions are public because they are functions of public data, and because a test
  harness that plays a cheating prover needs the challenge an honest verifier will compute.
* **The counter `j_Q`** ("the least nonnegative counter for which `x_Q ≠ x_0`"):
  `recipient_point` recomputes with an incremented counter while the output equals the key's
  `x_0 = H_id(⟨hvk⟩)` (`Backend::same_point`; the lattice backend compares the matrices).

## Fiat–Shamir after the IETF drafts

The pairing proofs are the compact non-interactive arguments of
`draft-irtf-cfrg-sigma-protocols-04` over the duplex sponge of `draft-irtf-cfrg-fiat-shamir-04`
(module `sigma::fiat_shamir`, [Encodings](./encodings.md#the-fiatshamir-challenge-h_1)). The
choices that the drafts leave to the application, and what this crate does where they do not
reach:

* **The tag.** `PCS-V01-SIGMA04-CMPT-with-{suite}-ctx-{hex(ctx)}`. It contains the flavor marker
  and the ciphersuite identifier verbatim (Sigma -04 §5.1), names this crate, a version and the
  draft revision, and carries the protocol's context `ctx` as its last field, in hexadecimal,
  so that the tag stays US-ASCII and determines its fields (FS -04 §5.1).
* **Byte-exact where the draft applies.** A relation with `G_1` equations only (`π_id`, the
  proofs of `Σ-BBS`, `π_iss` of `Σ-PS`) is the draft's `LinearRelation` over `G_1` of BLS12-381
  under `sigma-proofs_Shake128_BLS12381`, and `tests/ietf_vectors.rs` reproduces the draft's
  vectors through the same builders the protocol uses.
* **An extension where it does not.** The draft covers one group, so a relation with a `G_T`
  equation (`π_att` and `π_prove` of `Σ-PS`) uses this crate's extension (module
  `sigma::relation`): the draft's layout per group, `G_T` bases as pairs of a `G_1` and a `G_2`
  element, and the identifier `pcs-sigma-pairing_Shake128_BLS12381`, which does not claim the
  draft's.
* **Every element in the instance.** The clauses write negated elements and sums with
  coefficients rather than as computed points (`C h_0^{-1}` is the image `(C, 1), (h_0, −1)`,
  the target `g_1 t^{-x}` of `Tag_DY` the image `(g_1, 1), (t, −x)`), as Sigma -04 §3.2 requires.
* **The witness length is the draft's.** A relation has as many responses as its largest used
  variable index plus one. A variable allocated after the last used one is not part of the
  instance. The relations of the protocol use every variable they allocate.
* **The masks** come from `Group.random_scalar` (§2.2): 48 bytes of the generator reduced modulo
  `p`, the reduction the draft recommends, which also lets the prover reproduce the draft's
  vectors from its seeded generator.

## The tags

* **`Tag_DY`'s generator is derived from the label.** §6.1.2 uses "a generator `g_1` of `G_1`
  that is sampled uniformly from `G_1 \ {1}` when the public parameters are generated,
  independently of all keys", and the proof of weak pseudorandomness (Lemma on `Tag_DY`, (ii))
  needs it to be a setup parameter: its reduction sets the tag generator to `h = ĝ^{f(α)}`,
  computed from the `(ℓ−1)`-DDHI instance. The earlier code used the standard generator of
  `G_1`, the same in every deployment (and the generator of the bases), which that reduction
  cannot set to its `h`. `ProtocolTag::setup` for `DY` now hashes `g_1` from the deployment label
  (`DY::derive`, oracle suffix `/DY-GENERATOR`): transparent, independent per deployment, and in
  the random-oracle model a reduction can program the oracle's answer at the label to `h`. That
  last step is our argument for the hashed generator; the lemma is stated for a sampled one.
  `DY::new()` (the standard generator) remains for stand-alone use of the tag, and
  `from_public_parameters` accepts only the derived generator.
* **`Tag_DDH` without a programmed point.** The earlier code programmed `htag(c_0) := g_1`
  (Remark "Identity point" of the earlier paper), so that `id = g_1^usk`; only `Σ-EQ`, whose
  helper builds its signed vector from `id`, needed it. With `Σ-EQ` gone, `Tag_DDH` is the box of
  §5.1.1: `htag` is the random oracle at every point, `x_0` included, and `id = htag(x_0)^usk`.
  The lemma of §5.1.1 treats `htag` as a random oracle onto `G_1 \ {1}` at every point, and
  `x_0 = H_id(⟨hvk⟩)` is a random-oracle output like any other point; a programmed value at `x_0`
  was outside that statement.
* **Degenerate parameters.** `Register` samples one key and fails if `Tag(usk, x_0) = ⊥`
  ("If `id_P = ⊥`, return `(RegisterFailed, ⊥)`"; under well-formed parameters with probability
  at most `1/p`), and under a degenerate tag instance (a `Tag_DY` whose generator is the
  identity, which only decoding without validation produces) every evaluation is `⊥`, so every
  registration would fail. A `Protocol` exists only for parameters that passed
  `Backend::check_params`, which refuses such an instance (`ProtocolTag::is_well_formed`).
  `PrepareIssue` likewise samples one `τ` and ends the call on `⊥`.

## The bases

A credential certifies `usk` alone, with no attribute (Remark "Additional attributes" describes
the extension; it is not implemented).

* **`Σ-PS`**: the request is `C = g_1^ρ Y^usk`, and a show is blinded by a fresh offset,
  `σ* = (σ_1^r, (σ_2 σ_1^t)^r)`, so that it is a uniform pair; the possession proof has responses
  for `usk` and `t`. Only `x` of `sk = (x, y)` is kept, since only `x` is needed to issue.
* **`Σ-BBS`**: the helper signs `B(usk, ρ) = h_0 h_u^usk h_r^ρ` directly, the credential
  `(A, e, ρ)` keeps `ρ`, and a show is `(Ā, B̄, D)` with the three possession clauses of the paper,
  the third being `D = B̄^u Ā^v`; the generators are hashed from the label.
* **`Unblind` fails closed, once.** `Σ-BBS`'s `Unblind` verifies, as in the paper
  (`Base::UNBLIND_VERIFIES`); for `Σ-PS` the backend runs `Verify` on the unblinded credential.
  Either way an answer of the helper that does not give a valid credential is noticed at issuance
  (`Error::InvalidPreCredential`), not at the first attestation.

## Received objects are re-validated

The messages have public fields, and arkworks offers unvalidated and uncompressed decoding, so a
value of type `E::G1` is a group element only if its producer made sure. Every check of the
backend therefore re-validates what it is given (curve and prime-order subgroup of every group
element, `ark_serialize::Valid::check`) before anything is computed from it, and the protocol
checks `t ∈ T` for every identifier and tag it receives. This is load-bearing: pairing equations
do not see a component of small order in a `G_1` argument, and the cofactor of BLS12-381 `G_1` is
divisible by 3, so without the check a tag shifted by a point of order 3 would be a "distinct" tag
and one source could count as several. The verifiers also impose what the algebra drops
("Verification must re-impose what the algebra drops", §7.3): `σ'_1 ≠ 1` for `Σ-PS`,
`Ā ≠ 1 ≠ D` for `Σ-BBS`, `t ≠ 1` for every tag.

## What was removed, and why

| removed | what it was | why |
|---|---|---|
| `Σ-EQ` (`cred::EQ`), `Σ-MAC` (`cred::MAC`) | the SPS-EQ base and the designated-verifier base of the earlier construction | not in the current paper: §6.2 has `Σ-PS`, `Σ-BBS` and `Σ-vSIS`, and the appendices on `Σ-EQ` and `Σ-MAC` are no longer part of it |
| predicates `f = (k, label)`, `EncPred`, attribute policies (`AcceptAll`, `AllowList`) | credentials certified `(usk, φ = EncPred(f))`, attestations disclosed `φ`, and a requester's proof named its predicate | `Π_PCreds` certifies `usk` alone and its policy `Pol_k` is the helper's input; attributes are Remark "Additional attributes". The lattice instantiation kept them until its port (below) |
| the self-exclusion tag `T_0 = Tag(usk, H_0(id))` | proved that the requester was not among its own attesters | `Π_PCreds` has none: its helper counts distinct tags and keeps the set `I`, issuing at most once per identifier, and an identifier without a credential has nothing to attest with |
| root requests (`root_request`, `issue_root`, `f_root`, `ctx_root`) | a separate admission path with its own proof | `Π_PCreds` admits root users by the helper's decision `d = root` on an ordinary request (Remark "Root users and chaining") |
| `kiprf::PCSTag` (`setup(domain, c_0)`, `IDENTITY_IS_DLOG`, `identity_is_dlog`) | the tag interface of the earlier construction, with the programmed identity point | replaced by `ProtocolTag` (`setup(label)`, `NAME`, `is_well_formed`); the programming it served went with `Σ-EQ` |
| `hash::h0_id` (`s = H_0(⟨id⟩)`) | the evaluation point of the attestation tags | replaced by the recipient point `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)` (`Protocol::recipient_point`), which also binds the point to the helper key |
| `hash::h0_identity_point` (`x_0 = H_0("identity")`, in `pp`) | the identifier point of a deployment | replaced by `x_0 = H_id(⟨hvk⟩)`, one per helper key (`Protocol::identifier_point`, `HelperKey::identifier_point`); `pp` carries no `x_0` |
| `pcs::PCS` with `pcs::{construction, context, codec}`, `cred::{PS, BBS}`, `cred::conformance`, `cred::bbs::ietf` | the earlier pairing construction, its bases, their conformance flows and the IETF generators of its `Σ-BBS` | replaced by `pcreds` and `pcreds::pairing` (the IETF generators by `pcreds::pairing::ietf`, for the two values `(usk, ρ)`); the tests now drive the protocol through its public API |
| `benches/cred.rs`, `benches/pcs.rs` | benchmarks of the earlier bases and construction | replaced by `benches/pcreds.rs` |
| `pcs::lattice::LatticePCS` with `pcs::lattice::{relations, context, codec, types}`, `pcs::{predicate, types}` and the trait `PredicateCredentialSystem` | the lattice instantiation of the earlier construction and its game-based interface; the last commit with it is tagged `pcs-final` | the backend `pcreds::lattice::LatticeBackend` under the one `Protocol` ([below](#the-lattice-instantiation-feature-lattice)) |
| `cred::VSIS` | `Σ-vSIS` of the earlier construction: `Sign` and `BlindIssue(sk, C, φ)`, on messages `(usk, φ)` | `pcreds::lattice::base::VSIS`, the box of the current paper, which certifies `usk` alone (`BlindIssue` on `Ĉ = b_u usk + B_r x_0`) |
| `lattice::ring::BinaryPoly`, the oracle `/LATTICE-PREDENC`, the column `b_φ` of `pp_Σ`, `hash::h0_predicate` | `φ = EncPred(f)` as a binary polynomial, and its share of the credential equation | `Π_PCreds` certifies `usk` alone |
| the Jali sets of `R_issue` and of root requests (`params-issue-beta439.json`, `params-issue-root-beta439.json`) | the issuance proof `π_0` of the earlier construction: the opening of `C`, the requester's identifier and its self-exclusion tag | `π_iss` proves `R_iss` (the opening of `Ĉ` and the identifier, nothing else); new sets for `R_Tag`, `R_iss` and `R_Possess` |
| the errors `InvalidAttestation`, `WrongAttestationCount`, `DuplicateAttester`, `SelfAttestation`, `PolicyRejected`, `NotARootPredicate` | the refusals of the earlier `VerifyProof` and of its root path | the helper counts the distinct tags of the valid attestations instead of refusing a request, and admits root users by its decision |

## Limitations

* **Plain Fiat–Shamir in the random-oracle model.** The theorem assumes an online
  simulation-extractable NIZK; Fiat–Shamir with its rewinding extractor does not give it. Of the
  two routes the paper names (§3.3, "Instantiating the definition"), the crate implements the
  proofs of the second, plain Fiat–Shamir of Schnorr protocols, whose online extractor the paper
  takes from the algebraic group model with random oracles; it does not implement Fischlin's
  transform. That the algebraic-group-model argument covers the relations of this crate, which
  include equations in `G_T`, is not shown here. The interactive protocol, its simulator and its
  extractor are exposed so that tests can exercise them; tests show algebraic facts on sampled
  instances, not the theorem.
* **Secrets in memory.** Secrets owned by this crate are wiped on drop, but field elements are
  `Copy` and temporaries may remain on the stack.
* **One helper key.** The verifiers take one `hvk`; rotation, threshold issuance, revocation and
  expiry are not implemented.
* **`parallel`** speeds up arkworks internals and verifies the attestations of a request in
  parallel (`evaluate_request`, in rounds and in batches no wider than the rayon pool; the same
  `N''` as without the feature).
* **The issuance record** is as durable as the store the deployment gives it.
* arkworks' `DefaultFieldHasher` differs from RFC 9380 `hash_to_field` when hashing to the scalar
  field (zero-padding length). It is used as a random oracle only and does not interoperate with
  RFC 9380 hashers.

## The lattice instantiation (feature `lattice`)

`pcreds::lattice::LatticeBackend` is the post-quantum instantiation of `Π_PCreds` (§6.2.3 with
§6.1.3; Corollary "cor:pcs-instantiations" (iii)) and the second backend of the one `Protocol`
(`LatticeProtocol = Protocol<LatticeBackend>`): the credential base `Σ-vSIS`
(`pcreds::lattice::base`, on an NTRU trapdoor from the crate `ntru-trapdoor`), the short-key
`Tag_LWR` (`kiprf::lwr`), and Jali proofs (the LNP22 design, in Jali's straight-line extractable
mode, or with the feature `lattice-plain` compiled with plain Fiat–Shamir) for the four
relations of the protocol. What the sections above say of `Protocol` holds for it as
written: the state machine, the type-state values, the binding to a deployment, the issuance
record, the contexts and the count of distinct tags are the protocol's, not the backend's.

| `Backend` | `LatticeBackend` |
|---|---|
| `Params` | `LatticeParams`: the deployment label, `pp_Σ = (v, b_u, B_r)` and Jali's public seed, all derived from the label; the statement constants, the four parameter sets and the identifier point with its rows, built once and shared by clones |
| `UserKey`, `Tag`, `Point` | `Ternary` (`usk`), `LWRTag` (168 entries below `p = 2^16`), `LatticePoint` |
| `VerificationKey`, `SigningKey` | `VSISVerificationKey` (`h`), `VSISSigningKey` (the trapdoor and the issuance count) |
| `Request`, `IssuanceTape` | `Rq` (`Ĉ`), `VSISTape` (the base's issuance randomness `x_0`: `ℓ_r = 3` ternary elements; not the identifier point `x_0` of the protocol) |
| `PreCredential`, `Credential` | `VSISPreCredential` (`σ̂ = (s, x_1)`), `VSISCredential` (`σ = (s, x_1, x_0)`) |
| `Show`, `Proof` | `()` (`ReRand` "outputs the empty encoding"), `LatticeProof` (Jali's proof bytes) |

* **One parameter set.** Ring degree 1024, `q = 2^20 − 3`, NTRU width 2, `ℓ_r = 3`, all short
  messages ternary (`β_u = β_x = β_r = 1`), `⌊β_s²⌋ = 90,803,788,942`, and the tag set
  `(γ, p, q_t, m) = (15, 2^16, 983,040, 168)` with rounding errors in `[−7, 7]`, at proof degree
  128 (`crate::lattice`). The encoding of `LatticeParams` carries these constants as sixteen
  words, led by a format version (3; version 1 was the earlier construction, version 2 the first
  port, with `ℓ_r = 2`), and its decoder refuses any other value.
* **The hiding of the request.** `x_0` is uniform on `({−1, 0, 1}^d)^3`. lem:base-vsis (b)
  needs the request `Ĉ = b_u usk + B_r x_0` to be pseudorandom: the knapsack form of
  `MLWE_{ℓ_r,q,D_r}`, which after a division by `B_r[0]` is module LWE with one sample, a ternary
  secret of rank 2 and a ternary error. lattice-estimator prices it at `2^344.9` in rough mode,
  and two components at `2^130.8`, under three bits above 128 before the factor `2 Q_iss` of the
  theorem ([`tools/lattice/sets/README.md`](../tools/lattice/sets/README.md), "The hiding of the
  request"). The paper's issuance simulatability is computational (`≈_c`) and its theorem uses it
  only through `Adv^iss`, so computational hiding suffices; it is the hiding of BLNS23 (Thm. 8.2),
  whose `ℓ_r = 2` DKLW25 follow. The paper first asked for the statistical regularity bound
  `ε_reg = Δ((B_r, B_r x_0), (B_r, U)) = negl`, and an earlier version of this backend met it
  with 13 components (twelve cannot work: the entropy of `x_0` must exceed `d log_2 q`): 208
  binary rows at proof degree 128 instead of 48, and proofs that carry `x_0` 1.6 to 2.1 times
  larger (the estimates of their sets) and 2.6 to 3.7 times slower than now.
* **`s ≠ 0`.** `Π_Possess` proves `1 ≤ ‖s‖² ≤ β_s²`, and the argument system must extract
  `s ≠ 0` exactly. `R_att` and `R_Possess` bound `s` with Jali's two-sided exact norm
  `Norm::L2SquaredRange { min: 1, max: ⌊β_s²⌋ }` (`relations::S_NORM`): the upper bound is Jali's
  exact-norm proof, and for the lower bound Jali commits one more binary polynomial `y` and
  proves `ct(Σ_c σ(s_c) s_c) − Σ_b c_b y_b − 1 = 0` at the proof modulus, with weights whose
  subset sums are exactly `[0, ⌊β_s²⌋ − 1]` (Jali's protocol notes, "Two-sided Euclidean
  bounds"). A unit test builds `pp_Σ` for which `s = 0` satisfies the possession equation and
  shows that the relation refuses it.
* **`V_pp`.** §5.2.3 makes the admissible key domain of
  `Σ-vSIS` the whole key space, and this code takes `V_pp = R_q`, every canonically encoded `h`
  (a wiped one is refused): issuance simulatability holds for every verification key
  (lem:base-vsis (b)), and the simulators of the corollary need nothing more of the key.
* **Four relations, four Jali parameter sets.** `R_Tag` (`π_id`), `R_att` (`π_att`), `R_iss`
  (`π_iss`) and `R_Possess` (`π_prove`) are Jali statements (`pcreds::lattice::relations`) that
  share the coefficient vector of `usk` across their clauses; their tag clauses are the relation
  of `Tag_LWR` (§6.1.3), one constant-coefficient constraint per row of the point, over the tag
  ring, with the rounding errors as blocks of the subring of the proof degree. A Jali parameter
  set is valid for exactly one statement layout (block names and order, exact norms, placements,
  the shape of the constraints), and Jali's `compile` refuses any other: every set was derived
  for its statement by Jali's parameter tool, `R_Tag`'s for the first port and identically
  again at Jali 5ee737b, whose library code the release 0.1.0 has (a unit test compiles each
  statement against its own set and no other). The release 0.1.1 left the plain mode, its
  parameter check and its proofs as 0.1.0 had them. The release 0.2.0 changed every proof
  and its encoding, and its parameter check still accepted each set for its statement (the same
  unit test), so the sets carried over unchanged. The pinned release 0.3.0 keeps the proofs,
  transcripts and parameter check of 0.2.0. Jali
  derives bounds such as the largest
  integer coefficient from the constants of a statement, so the sets were derived at the
  worst-case public data; the
  derivation, its policy (block sizes of at least 439, 443 for `R_Tag`; lattice-estimator at 128
  bits; the moduli proven prime) and how to reproduce it are in
  [`tools/lattice/sets/README.md`](../tools/lattice/sets/README.md). The sets are embedded,
  pinned by SHA-256, and loaded with Jali's strict decoder and `check()`.
* **Two builds, one switch.** With the feature `lattice-plain` the backend proves with plain
  Fiat–Shamir. Without it (the default), every proof is a proof of Jali's straight-line extractable mode
  (Katsumata's transform, CRYPTO 2021): besides the opening proof it commits to the final
  opening's witness with an extractable linear homomorphic commitment (LinHC, the MLWE
  construction), under a key that the random oracle outputs on the parameters, the extraction
  set, the context and the statement. Each parameter set takes an extraction set, the LinHC's
  rank and modulus, derived by Jali's parameter tool under the set's own policy and gated by
  lattice-estimator at 128 bits on the commitment's hiding instance
  ([`tools/lattice/sets/README.md`](../tools/lattice/sets/README.md#extraction-sets)). Both
  builds load and check the extraction sets. The switch is `lattice::STRAIGHT_LINE`, and only
  the relations' prove and verify calls, the bounds on proof lengths and the encoding of the
  parameters depend on it. The pairing backend keeps plain Fiat–Shamir.
* **`pp` covers Jali.** The digest of `pp` covers the encoding of `LatticeParams`: besides `pp_Σ`
  and the label (which stands for the oracles `H_mat`, `H_id` and `H_req`), the constants, Jali's
  public seed (derived from the label, never chosen by the helper), the pins of the four sets,
  the Jali revision (Jali promises no stability of its proof encoding or its transcripts) and the
  placement of `s` in `R_att` and `R_Possess`, and in the extractable build the argument system
  and the pins of the four extraction sets, so that a plain and an extractable deployment never
  share a `pp`. Every proof context starts with that digest, and
  `Protocol::from_public_parameters` compares `pp_Σ` and the seed with what the label derives.
* **Points by their oracle input.** A point of `Z_{q_t}^{168×1024}` has 172,032 entries, so a
  `LatticePoint` is the input of `H_mat` that defines it: the identifier point
  `x_0 = H_mat("hid" ‖ d)` of a helper key, or a recipient point `x_Q = H_mat("req" ‖ d)`, for the
  32-byte digest `d` of the protocol's transcript of that oracle (`Backend::identifier_point`,
  `Backend::request_point`). The matrix is derived when a tag is evaluated or a statement built.
  Points compare by their inputs, and the rule `x_Q ≠ x_0` compares the matrices
  (`Backend::same_point`); two distinct inputs give one matrix only with probability
  `q_t^−172,032` in the random-oracle model, so the counter is `0` but on that event.
* **Issuance is the box of `Σ-vSIS`.** `PrepareIssue` is `Ĉ = b_u usk + B_r x_0`. `BlindIssue`
  draws `x_1` until `v − x_1` is a unit (at most 128 times) and samples `s ← SampPre(td, t)` at
  `t = (v − x_1)^−1 + Ĉ`, with fresh coins, under the issuance cap. `Unblind` verifies and fails
  closed. `Verify` checks `0 < ‖s‖² ≤ ⌊β_s²⌋` and the box's equation in product form,
  `(s_0 + h s_1 − b_u usk − B_r x_0)(v − x_1) = 1`: a product of two elements is `1` iff both are
  units and each is the other's inverse, so the product form accepts exactly what the box's
  equation together with "`v − x_1` is invertible" accepts, without an inversion.
* **Exact preimages.** `ntru-trapdoor`'s `SampPre` rounds a floating-point lattice point, exact
  with a measured margin, not by proof. The paper asks for `s ∈ Λ_t` "in integer arithmetic"
  (§6.2.3, "The implemented preimage sampler"), so the signing key checks `s_0 + h s_1 = t mod q`
  exactly, and the norm, before a preimage leaves it, and refuses a sample that fails (never
  observed).
* **The issuance cap `Q_max = 2^48`.** The signing key counts its `BlindIssue` calls: a call
  reserves a unit with a compare-and-swap before `SampPre` runs, so concurrent issuance through a
  shared key never exceeds the cap, and at the cap the key refuses (`Error::IssuanceCapReached`).
  `respond` records an identifier only after `BlindIssue` returned
  ([above](#the-issuance-record-blindissue-then-one-test-and-set)), so a key at its cap leaves no
  identifier recorded without a credential. The count is part of the key's encoding, and
  `Helper::to_bytes_reserving(n)` stores it advanced by `n`, for a helper that persists its key
  before it issues ([Operating a helper](./operating-a-helper.md)).
* **Bounded proofs.** A proof has at most twice the estimated size of its parameter set (58,336
  bytes for `π_id`, 282,832 for `π_att`, 196,264 for `π_iss`, 272,208 for `π_prove`); the compact
  decoders, the JSON decoders and every verifier refuse a longer one before any work on it.
  The honest proofs measured (twelve, from two seeded runs) have 0.952 to 0.965 times the
  estimate, so no honest verdict changes; garbage of up to Jali's own limit (16 MiB) would
  otherwise be decoded, hashed into a context and handed to a statement compile.
* **Honest provers check their witness first.** A credential that does not verify, a tag that the
  key does not give at the point, or a request that `PrepareIssue` does not give on the witness is
  refused (`Error::WitnessDoesNotSatisfyRelation`) before Jali compiles anything; Jali's prover
  would refuse the witness too, later.
* **Fresh randomness everywhere.** Jali and `ntru-trapdoor` take 32-byte seeds; each proof, each
  `SampPre` call and each `TrapGen` gets a fresh seed from the caller's RNG
  (`lattice::fresh_seed`), never reused. A Jali `RestartLimit` is retried with a new seed (3
  attempts).
* **Types that cannot hold what the relations do not check.** Jali binds public constants modulo
  the modulus of their constraint: since `γ p = q_t`, a non-canonical tag `T + p z` has exactly
  the witnesses of `T`. `LWRTag` stores entries below `p`, so no such tag can be represented, and
  the backend evaluates `ValidTag` on every tag all the same. A unit test shows the effect on the
  relations themselves.
* **Parallel attestation verification** (feature `parallel`) is the protocol's, not the
  backend's: `evaluate_request` verifies the attestations of a request in rounds, each round the
  next untried attestation of every tag that has not counted yet, so each attestation is verified
  at most once and none of a tag already counted, and `N''` lists the tags in the order of the
  attestations that made them count. With the feature, a round runs on the rayon pool of the
  calling thread in batches no wider than the pool; `N''` is the same as without it, for every
  input, and only the time changes. The batches bound the memory (an `R_att` verification holds
  up to about 0.7 GB): with one parallel iterator over a whole round, rayon lets a thread that waits
  inside one verification (Jali parallelizes inside each one, on the same pool) start another.
  The equality of the two builds rests on the backend's `check_*` functions never panicking, as
  the trait requires.
* **Caches.** The parameter sets, the statement constants (`pp_Σ` lifted to Jali's rings) and the
  identifier point with its rows are built once per `LatticeParams` and shared by its clones; a
  recipient point and its rows are derived once per proof or verification. Compiled statements
  cannot be cached: every proof has its own constants, and Jali has no shape-level compilation.

### What the lattice instantiation does not meet

* **No security theorem covers this code yet.** Corollary "cor:pcs-instantiations" (iii) is
  stated for parameters as in lem:base-vsis and lem:tag-lwr-short, with an online
  simulation-extractable NIZK. The parameters now meet lem:base-vsis as the paper revises it
  (the request pseudorandom under MLWE, the extraction of `s ≠ 0`, above), and three things
  remain:
  * **The NIZK.** In the plain build Jali's proofs are Fiat–Shamir with extraction by rewinding,
    and Jali's knowledge soundness under Fiat–Shamir is not written out. This is the gap of the
    pairing backend ([Limitations](#limitations)), without its algebraic-group-model route. In
    the default build the proofs are Jali's straight-line extractable proofs.
    Jali's target for them has the form of Def. `def:nizk` with the context in the statement: in
    the classical random-oracle model, an extractor that neither rewinds nor queries the oracle
    itself recovers, after simulated proofs of true or false statements, a witness for every
    accepted proof whose statement and context received no simulated proof. Jali proves the
    decryption step, cites Katsumata and LNP22 for the extraction from three transcripts, and
    gives the steps for the earlier rounds and for simulated proofs as outlines, so the
    hypothesis is targeted but not established. Neither build claims anything in the quantum
    random-oracle model. In both, the exactness of the extracted norms
    (`Compiled::extraction_bound`) is a property of Jali's design, not a proven theorem.
  * **The assumptions at these parameters.** One-more unforgeability rests on `IntGenISIS_f` (or
    the one-more vSIS assumption) with `k = 1 + ℓ_r = 4` columns of `B` and message bound 1, and
    neither the paper nor this code estimates the assumption at these values.
  * **The paper's text.** The paper's revision that states the MLWE hiding of lem:base-vsis (b),
    `V_pp` as the whole key space and the argument for the lower bound on `‖s‖²` is pending
    review (marked in its sources).
* **The tag's hardness** is decisional LWR with a short (ternary) key and any number of samples,
  which the paper assumes directly. Read as LWE with a uniform error on `[−7, 7]`,
  lattice-estimator prices it at `2^151.7` in rough mode and `2^175.5` with its default attacks,
  and the Arora–Ge attack at `2^219.8`
  ([`tools/lattice/sets/README.md`](../tools/lattice/sets/README.md), "The tag's own hardness").
* **Key rotation at the cap** ("the helper must accept attestations under each of its keys") is
  outside the single-key model of the protocol and not implemented: a helper at the cap issues
  nothing more under its key. Restoring an old key encoding rolls the issuance count back, and
  two live copies of one stored key count separately (one live instance per stored key;
  [Operating a helper](./operating-a-helper.md)).
* **Variable time** in Jali, `SampPre` (floating point, rejection), `TrapGen` and the rejection
  sampling of ternary polynomials.
* **Memory**: up to about 0.7 GB per proof or verification of `R_att` or `R_Possess`, and with the
  feature `parallel` up to `n` attestation verifications at once per `evaluate_request` on a pool
  of `n` threads; bound it with `RAYON_NUM_THREADS` or a rayon pool of your own ([Operating a
  helper](./operating-a-helper.md)).
* **Out of scope**: the private credential requests of the paper's appendix.
* **Platforms**: only aarch64 (Apple M4) was measured. `SampPre` computes in floating point, so
  the exact preimages may differ across platforms (their validity is checked exactly before
  release); the tests assert proof lengths against their bounds, not exactly.
* **CI**: every dependency comes from crates.io, Jali and `ntru-trapdoor` included (pinned to one
  release each), so a checkout of this repository alone builds, as in `.github/workflows/pcs.yml`,
  whose job `lattice` runs the flow at `k = 1` with real proofs in release. The other heavy suites are run by hand
  ([Testing and benchmarks](./testing-and-benchmarks.md)).
