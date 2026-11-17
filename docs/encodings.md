# Encodings and Interoperability

The byte and text forms of the objects of `pcreds`, derived from the code (`pcreds::codec`,
`pcreds::types`, `serialization`, `hash`, `pcreds::context`) and checked against it: the sizes
below are asserted by `tests/pcreds.rs` (`sizes_match_the_paper`) or were measured on seeded
instances of all four base/tag pairs when this page was written. The lattice backend (feature
`lattice`) has its own objects, oracles and proof format under the same messages and contexts:
see [Lattice instantiation](#lattice-instantiation-feature-lattice) at the end.

There are three representations:

* **The compact fixed format** of the messages (`pcreds::codec`: `to_compact_bytes`,
  `from_compact_bytes`, `size`, `compact_size`): the encoding whose sizes are those of the paper's
  Table "Sizes" (§7.1). A proof is written without a length: the number of its responses is a
  constant of the backend and of the proof's kind, never a number read from the wire.
* **The canonical encoding** of every object (`serialization::{to_bytes, from_bytes}`, the
  blanket trait `WireFormat`): the compressed arkworks encoding, derived field by field
  (`CanonicalSerialize`), except for a proof, which is its number of responses and its NARG
  string. For the messages it is self-describing (vectors carry their length) and a few bytes
  longer than the compact format. For everything else it is the only byte form.
* **JSON** (feature `serde`): a canonical encoding as one multibase base58btc string, and the
  messages as JSON objects whose leaves are such strings.

Every decoder of this crate validates: points must be on the curve and in the prime-order
subgroup, scalars canonical (`< p`), the encoding compressed, and nothing may follow the value
(`Error::TrailingBytes`). Validation accepts the identity point and the zero scalar; wherever the
paper requires a non-identity element, the verifier of the relation checks it. Decoding says
nothing about the validity of an object: the verifiers decide that, and they re-validate what they
are given, however it was built.

Every accepted byte string is therefore the unique encoding of the value it decodes to. This
includes `IssuanceRecord`, whose decoder requires the identifiers in strictly increasing order,
which is how it encodes them: the decoder of a set in arkworks would accept them in any order and
repeated (checked: a 120-byte encoding that lists one identifier twice is refused, as is one with
two identifiers out of order).

## Elements over BLS12-381

| value | bytes |
|---|---|
| `Z_p` (`Fr`) | 32, little-endian, canonical |
| `G_1` | 48: the big-endian `x`-coordinate with three flags in the top bits of the first byte (bit 7 compressed, bit 6 identity, bit 5 the larger `y`); the identity is `0xc0` followed by 47 zero bytes |
| `G_2` | 96: `x = (x_1, x_0)` over `F_{p^2}`, big-endian, with the same flags |
| `Vec<T>`, `BTreeSet<T>` | `LE64(count)` followed by the items |
| `[u8; 32]` (a digest) | the 32 bytes |
| `()` and marker types | nothing |
| a label `Vec<u8>` | `LE64(len) ‖ bytes` |

The point format is the one of the ZCash / IETF BLS12-381 serialization, specified in §5.3 and
§5.4 of `draft-irtf-cfrg-pairing-friendly-curves-15`, with vectors in its Appendix D.1. The
scalars of the canonical encodings are little-endian (§5.2 of that draft and IETF BBS write them
big-endian). The scalars of a proof are the exception: a proof is the NARG string of
`draft-irtf-cfrg-sigma-protocols-04`, whose scalars are big-endian (`I2OSP`, 32 bytes), in the
compact format and in the canonical encoding alike.

## The compact fixed format (`pcreds::codec`)

`k` is the number of attestations of a request. A proof `π = (c, z_1, …, z_n)` is
`c ‖ z_1 ‖ … ‖ z_n`, 32 bytes each, big-endian: the compact NARG string
`Scalar.serialize([c]) ‖ Scalar.serialize(z)` of `draft-irtf-cfrg-sigma-protocols-04` (§5.5),
with the responses in the variable order of its relation (`usk` first, then the variables of
the base in the order its clauses allocate them). Its decoder takes exactly that many scalars and
refuses a scalar `≥ p`.

| proof | relation | scalars | bytes |
|---|---|---|---|
| `π_id` | `R_Tag` at `(id_Q, x_0)` | `c, z_usk` | 64 |
| `π_att` (`Σ-PS`) | `R_att`: the clause of `Π_Possess` and the tag clause | `c, z_usk, z_t` | 96 |
| `π_att` (`Σ-BBS`) | `R_att`: the three clauses of `Π_Possess` and the tag clause | `c, z_usk, z_ρ, z_{r_1}, z_e, z_{r_3}, z_u, z_v` | 256 |
| `π_iss` | `R_iss`: the clause of `Π_PrepareIssue` and the tag clause at `(id_Q, x_0)` | `c, z_usk, z_ρ` (the witness of `ρ` is `τ`) | 96 |
| `π_prove` | `R_Possess` | as `π_att` | 96 / 256 |

The messages:

| object | layout | `Σ-PS` | `Σ-BBS` |
|---|---|---|---|
| `AttestationRequest` | `id_Q ‖ π_id` | 112 | 112 |
| `Attestation` (`size()`, the paper's `\|att\|`) | `t ‖ σ* ‖ π_att`; `σ* = (σ'_1, σ'_2)` (96) or `(Ā, B̄, D)` (144) | 240 | 448 |
| `CredentialRequest` | `id_Q ‖ LE32(k) ‖ att_1 ‖ … ‖ att_k ‖ Ĉ ‖ π_iss` | `52 + 240k + 144` | `52 + 448k + 144` |
| … its `size()`, the paper's `\|π\|` | the attestations, `Ĉ` (48) and `π_iss` (96), without `id_Q` and the count | `240k + 144` | `448k + 144` |
| `MembershipProof` | `σ* ‖ π_prove` | 192 | 400 |
| `Reply` | `0x00` (`Fail`), `0x01` (`issued`), or `0x02 ‖ σ̂` | 1, 1, 97 | 1, 1, 81 |

At `k = 5` a credential request has 1344 / 2384 bytes by the paper's count (`size()`) and 1396 /
2436 bytes on the wire (`compact_size()`). The tag does not change any size: `Tag_DDH` and
`Tag_DY` tags are both one `G_1` element. `σ̂` is `(σ̂_1, σ̂_2)` (96) for `Σ-PS` and `(A, e)`
(80) for `Σ-BBS`.

The one length on the wire is the count `k` of a credential request, which the requester
chooses. The decoder never allocates ahead of the input (every attestation it reads consumes
input); a helper that set a limit on the attestations of a request refuses a longer one before it
verifies any (`Policy::with_max_attestations`, `Error::TooManyAttestations`; no limit by
default).

## The canonical encodings

| object | layout | bytes |
|---|---|---|
| `FSProof` (any proof) | `LE64(n) ‖ c ‖ z_1 ‖ … ‖ z_n`: the number of responses, then the NARG string (big-endian scalars) | `40 + 32n` |
| `AttestationRequest` | `id_Q ‖ π_id` | 120 |
| `Attestation` | `t ‖ σ* ‖ π_att` | 248 / 456 |
| `CredentialRequest` | `id_Q ‖ LE64(k) ‖ att_1 ‖ … ‖ att_k ‖ Ĉ ‖ π_iss` (attestations canonical) | `160 + 248k` / `160 + 456k`, i.e. 1448 / 2488 at `k = 5` |
| `MembershipProof` | `σ* ‖ π_prove` | 200 / 408 |
| `Reply` | as the compact format (`Reply::to_compact_bytes` IS the canonical encoding) | 1, 1, 97 / 81 |
| `PublicParameters` | `LE64(len(L)) ‖ L ‖ pp_Σ ‖ pp_Tag`; `pp_Σ` is empty (`Σ-PS`) or `h_0 ‖ h_u ‖ h_r` (144, `Σ-BBS`); `pp_Tag` is the oracle's label `LE64(len(L)) ‖ L` (`Tag_DDH`) or `g_1` (48, `Tag_DY`). No identifier point: `x_0 = H_id(⟨hvk⟩)` is the helper key's | `Σ-PS`: `16 + 2·len(L)` with `Tag_DDH`, `56 + len(L)` with `Tag_DY`; `Σ-BBS`: `160 + 2·len(L)`, `200 + len(L)` |
| verification key `hvk` | `Σ-PS`: `X̃ ‖ Ỹ ‖ Y`; `Σ-BBS`: `X̃` | 240 / 96 |
| `Helper::to_bytes` (SECRET) | `pp digest ‖ hvk ‖ sk` | 304 / 160 |
| `IssuanceRecord` | `LE64(n) ‖ (LE64(48) ‖ id)…`, the identifiers in strictly increasing lexicographic order (the decoder refuses any other) | `8 + 56n` |
| `User::to_bytes` (SECRET) | `usk ‖ id ‖ pp digest ‖ helper fingerprint` (the `/PCREDS-HELPER` digest of the key the user registered with) | 144 |
| `Credential::to_bytes` (SECRET) | `(σ_1, σ_2)` or `(A, e, ρ)` | 96 / 112 |
| `IssuanceState::to_bytes` (SECRET) | `τ ‖ id ‖ pp digest` | 112 |

`HelperKey`, `PendingAttestation` and `EvaluatedRequest` have no encoding, deliberately: whoever
receives `hvk` checks it (`Protocol::helper_key`), an attester that answers later keeps the
`AttestationRequest` and receives it again, and a helper that answers later keeps the
`CredentialRequest` and evaluates it again. A `Protocol` is rebuilt from its `PublicParameters`
(`Protocol::from_public_parameters`). The secrets' own `to_bytes` methods return a buffer that is
wiped on drop (the blanket `WireFormat::to_bytes` would return the same bytes in a plain
`Vec<u8>`); the way back is `WireFormat::from_bytes`, then `Protocol::check_user` /
`Protocol::verify_credential` for a value read from storage, or `Protocol::restore_helper`.

## Oracles and proof contexts

Every oracle but `H_1` is a SHA-256 transcript of framed items (module `hash`): an item is
`LE64(len(label)) ‖ label ‖ LE64(len(data)) ‖ data`, the first item is `("dst", DST)` with
`DST = "PCS-V1" ‖ suffix`, values enter in their canonical encoding, and integers as `LE64`. A
scalar output is `hash_to_field(DST, digest)` with arkworks' `DefaultFieldHasher<Sha256, 128>`
(not RFC 9380 `hash_to_field` when hashing to `Z_p`; module `hash`).

| digest / oracle | suffix | items after `dst`, in order |
|---|---|---|
| digest of `pp` | `/PCREDS-PP` | `label`, `backend` (`"PS+DDH"`, `"PS+DY"`, `"BBS+DDH"`, `"BBS+DY"`, `"vSIS+LWR"`), `params` (`pp_Σ ‖ pp_Tag`; the encoding of `LatticeParams`) |
| context of `π_id` | `/PCREDS-CTX-ID` | `pp` (the digest), `ssid`, `contact` |
| context of `π_att` | `/PCREDS-CTX-ATT` | `pp`, `hvk`, then, with an application context (OpenVTC, `attest_in_context`), `app` |
| context of `π_iss` | `/PCREDS-CTX-ISS` | `pp`, `hvk`, `ssid`, `count` (`LE64(k)`), then one item `att` per attestation, in order, each in its canonical encoding, then, with application contexts (OpenVTC, `request_credential_in_context`), one item `att-app` per attestation, in order, and `app` |
| context of `π_prove` | `/PCREDS-CTX-PROVE` | `pp`, `hvk`, `message` |
| `x_0 = H_id(⟨hvk⟩)`, the identifier point of a helper key | `/PCREDS-HID` | `pp`, `hvk`; the scalar of the transcript (the lattice backend: `H_mat(hid ‖ d)` for its digest `d`) |
| `x_Q = H_req(⟨pp, hvk, id_Q, j_Q⟩)` | `/PCREDS-HREQ` | `pp`, `hvk`, `id`, `counter` (`LE64`, from 0, incremented while the output equals `x_0` of the same key; the lattice backend compares the matrices); the scalar of the transcript (the lattice backend: `H_mat(req ‖ d)` for its digest `d`) |
| the helper fingerprint, which binds a `User`, a `PendingAttestation` and an `EvaluatedRequest` to a key | `/PCREDS-HELPER` | `pp`, `hvk` |

The context digest (32 bytes) is the `ctx` of `H_1` (next section). The hash-to-group oracles (`htag = H_2`,
the generators) run the RFC 9380 suite `BLS12381G1_XMD:SHA-256_SSWU_RO_` with
`DST = "PCS-V1" ‖ suffix` on the framed input `("deployment", L) ‖ ("counter", LE64(i)) ‖
("msg", m)`, `i = 0` unless the output was the identity: `htag(x)` under `/H2` with `m` the 32
bytes of `x`; the generators `h_0, h_u, h_r` of `Σ-BBS` under `/PCREDS-BBS-GENERATORS` with
`m = LE64(0), LE64(1), LE64(2)`; the generator `g_1` of `Tag_DY` under `/DY-GENERATOR` with
`m` empty. Every proof context starts with the digest of `pp`, which covers the deployment label
and the name of the backend, and each of the four proofs has its own oracle, so a proof made for
one role does not verify in another.

## The Fiat–Shamir challenge `H_1`

`H_1` follows the IETF CFRG drafts `draft-irtf-cfrg-sigma-protocols-04` ("Sigma -04") and
`draft-irtf-cfrg-fiat-shamir-04` ("FS -04"), compact flavor (module `sigma::fiat_shamir`):

1. The tag of a proof under the context `ctx` is the US-ASCII string
   `PCS-V01-SIGMA04-CMPT-with-{suite}-ctx-{hex(ctx)}`: this crate, the version of the tag format,
   the revision of the drafts, the flavor marker `CMPT` of compact NARG strings (Sigma -04 §5.1),
   the ciphersuite identifier of the relation, and the context in lower-case hexadecimal, two
   digits per byte. The session identifier is `DeriveSessionID(tag)` (FS -04 §5.1).
2. The SHAKE128 duplex sponge (FS -04 §4.2, §9.1) is initialized with the session identifier,
   absorbs the serialized instance and then the serialized commitment, and the challenge is
   `DecodeField(Squeeze(48), p, 1)`: 48 bytes read as a little-endian integer and reduced modulo
   `p` (`DeriveChallenge`, Sigma -04 §5.2).
3. The verifier rebuilds the instance, checks the exact length and the canonical scalars of the
   NARG string, recomputes the commitment from `(c, z)` and accepts iff its challenge is `c`
   (`VerifyCompact`, Sigma -04 §5.5).

| relation | ciphersuite identifier | instance | commitment |
|---|---|---|---|
| `G_1` equations only (`π_id`, every proof of `Σ-BBS`, `π_iss` of `Σ-PS`) | `sigma-proofs_Shake128_BLS12381` (Sigma -04 §8.2) | `SerializeLinearRelation` (Sigma -04 §3.6) | the `G_1` elements, 48 bytes each |
| with a `G_T` equation (`π_att` and `π_prove` of `Σ-PS`) | `pcs-sigma-pairing_Shake128_BLS12381` (this crate's extension) | the extension's serialization below | the `G_1`, `G_2` and `G_T` elements (48, 96 and 576 bytes), in that order |

`SerializeLinearRelation` writes `LE32(number of equations)`, then per equation
`LE32(number of image terms)`, per image term `LE32(element index) ‖ coefficient`,
`LE32(number of terms)` and per term `LE32(scalar index) ‖ LE32(element index) ‖ coefficient`,
and at the end the elements (index 0 is the identity and index 1 the generator, both implicit,
and the listed elements have the indices 2, 3, …). Coefficients are 32-byte big-endian scalars. The
statements write negated elements and sums with coefficients (the image `(C, 1), (h_0, −1)` of
the issuance clause of `Σ-BBS`, the image `(g_1, 1), (t, −x)` of the clause of `Tag_DY`), so that
every element the verifier uses is in the instance.

The extension (module `sigma::relation`, "The pairing extension") keeps that layout per group:
the `G_1` equations, the `G_2` equations, then `LE32(number of G_T equations)` and per `G_T`
equation `LE32(number of image terms)`, its image terms `LE32(g1 index) ‖ LE32(g2 index) ‖
coefficient`, `LE32(number of terms)` and its terms
`LE32(scalar index) ‖ LE32(g1 index) ‖ LE32(g2 index) ‖ coefficient` (a pair of indices stands
for the pairing `e(P, Q)` of the two elements), then `LE32(count) ‖ G_1 elements` and
`LE32(count) ‖ G_2 elements`. No `G_T` element is part of an instance. A `G_T` commitment is
written as `SerializeField(a, q, 12)` of FS -04 Appendix A.2.4: its 12 coordinates over `F_q` in
arkworks' tower basis, each 48 bytes little-endian.

`tests/ietf_vectors.rs` runs the draft vectors (`kat/ietf/`) against this code.

## JSON (feature `serde`)

Two shapes (module `serialization`, "Text forms"):

* **Opaque.** A value with a canonical encoding is ONE string: `z` followed by the base58btc text
  of its canonical bytes (multibase base58btc, the convention of a W3C Data Integrity
  `proofValue`). Keys, shows, requests, pre-credentials, proofs (`FSProof`), public parameters,
  tag parameters, `IssuanceRecord` and the secrets are opaque.
* **Structured.** The messages are JSON objects with camelCase members whose leaves are opaque
  strings, so that an application can read, say, the tags of a request without decoding group
  elements:

```text
{ "id": "z…", "proof": "z…" }
{ "tag": "z…", "show": "z…", "proof": "z…" }
{ "id": "z…", "attestations": [{ "tag": "z…", "show": "z…", "proof": "z…" }], "request": "z…", "proof": "z…" }
{ "show": "z…", "proof": "z…" }
"fail"
"issued"
{ "preCredential": "z…" }
```

These are, in order, `AttestationRequest`, `Attestation`, `CredentialRequest`,
`MembershipProof` and the three forms of `Reply` (checked against the code for all four pairs).
The leaves are the CANONICAL encodings (a proof leaf carries its `LE64` number of responses in
front of its NARG string), not the compact ones. base58btc expands bytes by a factor `log 256 / log 58 ≈ 1.366`, and a credential request at
`k = 5` came to about 2.2 KB of JSON for `Σ-PS` and 3.6 KB for `Σ-BBS` on seeded instances (the
text length varies by a byte or two with the values).

Decoding is strict: base58btc only (any other multibase prefix is an error), validated canonical
bytes, no trailing bytes, a message only as a JSON object with exactly its members, each once (not
as the array of its members, which the derived decoders of `serde` would also take), and a reply
only as `"fail"`, `"issued"` or `{"preCredential": …}` (not `{"fail": null}`). One message has one
JSON form, as it has one binary form. base58btc decoding takes time quadratic in the length of a
string, so the decoders refuse a leaf of a message before they decode it if it is longer than the
multibase text of the longest valid leaf of its role (`Backend::max_leaf_bytes`, one bound per
role: `pairing::MAX_LEAF_BYTES` = 4096 bytes for every pairing-based leaf, whose largest is the
264-byte attestation proof of `Σ-BBS`; `serialization::max_multibase_len` turns bytes into
characters). Parsing a message then costs time linear in its length; bound the length of the
whole text at the transport, as for any input.

**Secrets.** `User`, `Credential`, `IssuanceState` and the signing keys of the bases (and
`BBSCredential`) serialize through the adapter `serialization::secret`, which wipes the buffers
it owns. Their text form IS the secret: write it only into protected storage, never into logs or
messages; copies made inside `serde`, `multibase` or the chosen data format are out of the
crate's reach. Serialize a `Σ-PS` credential as the `Credential` wrapper: the base type `PSPair`
is also the type of shows and pre-credentials and uses the plain `canonical` adapter. The helper's
key has no JSON form; it has its own wiped encoding (`Helper::to_bytes`).

**Generic code.** The `Serialize` / `Deserialize` impls of keys, credentials and the like exist
per type (`PSVerificationKey`, `BBSPreCredential`, …), not on the associated types of
`pcreds::Backend`. Code that is generic over the backend uses the adapters
`#[serde(with = "predicate_credential_system::serialization::canonical")]` (and `secret` for
secrets), which work for anything with a canonical encoding.

## Interoperability with IETF BBS (`pcreds::pairing::ietf`)

Not part of the paper. `Σ-BBS` signs `B(usk, ρ) = h_0 h_u^usk h_r^ρ` with `A = B^{1/(x+e)}` and
verifies with the pairing check of IETF BBS (`e(A, PK · BP_2^e) = e(B, BP_2)`, ciphersuite
BLS12-381-SHA-256). `BBSParams::ietf(interface, &hvk, header)` derives the generators as the IETF
ciphersuite does, `h_0 = P_1 · Q_1^{domain}` with `domain` over the helper's key, the generators
and the header, and `(h_u, h_r)` the generators of the two signed values; under these parameters
a credential `(A, e)` and an IETF BBS signature on `(usk, ρ)` are the same object (module docs of
`pcreds::pairing::ietf`, "The mapping"):

| `Interface` | `usk` | `ρ` |
|---|---|---|
| `Core` (`Sign` / `Verify`) | message 1, `H_1` | message 2, `H_2` |
| `Blind` (`Commit` / `BlindSign` / `BlindVerify`, no signer message) | the committed message, `J_1` | `secret_prover_blind`, `Q_2` |
| `BlindPseudonym` (`NymCommit` / `BlindSignWithNym` / `BlindVerifyWithNym`) | the `nym_secret`, `J_1` | `secret_prover_blind`, `Q_2` |

Because `h_0` depends on the helper's key, the key exists before `pp` (module docs, "Setting up
a deployment"): generate it (or take an IETF secret key, `BBSSigningKey::from_ietf_bytes` and
`BBSSigningKey::verification_key`), derive
`PairingParams { base: BBSParams::ietf(interface, &hvk, header)?, tag: T::setup(label)? }`, set up
with `Protocol::setup_with_params(label, params)`, build the helper from the key pair with
`Protocol::helper_from_key_pair(vk, sk, policy, store)` (which checks that `sk` belongs to `hvk`
and binds the helper to this deployment; from then on it is stored and restored like any other
helper), and receive `pp` with `Protocol::from_public_parameters_with_params` after recomputing
the parameters (`from_public_parameters` refuses them: they are not derived from the label
alone). The bytes
agree with IETF BBS except for the endianness of scalars: points are the same compressed 48 / 96
bytes, scalars are big-endian (`I2OSP`) there and little-endian here. The bridges are
`to_ietf_bytes` / `from_ietf_bytes` on `BBSVerificationKey` (96 bytes), `BBSSigningKey` (32 bytes,
in a wiped buffer) and `BBSCredential` (`A ‖ I2OSP(e, 32)`, 80 bytes; `ρ` is passed separately,
it is not part of an IETF signature).

Not covered, so that an attestation or a membership proof of this crate is not an IETF BBS proof
and an IETF proof is not a proof of this crate: the presentation (the show is the IETF/TZ show
`(Ā, B̄, D)`, but the possession proof has the third clause `D = B̄^u Ā^v`, two more responses,
another challenge and another byte layout), the tags (`Tag_DDH` is not the IETF per-verifier
pseudonym), messages as byte strings (this crate certifies the scalars `(usk, ρ)` themselves), a
non-zero `signer_nym_entropy` (the certified key would be `usk + entropy`), and selective
disclosure. Not claimed: the paper states the security of `Σ-BBS` for parameters sampled before
the key, and here `h_0` is a function of the key (module docs, "Transparency"). A bridge keeps
this crate's own checks (`hvk ∈ V_pp`, the public checks of `Π_Possess`, subgroup validation) on
everything it receives.

`tests/bbs_ietf_interop.rs` runs the bridges against `affinidi-bbs` 0.3.3, the BBS crate of the
Affinidi / OpenVTC stack, a pinned dev-dependency that is never part of a build of the library.
According to that suite (its module docs list what it shows): under `Blind` and
`BlindPseudonym`, a credential issued through the protocol passes THEIR `blind_verify` /
`blind_verify_with_nym`, and a signature they issued on `(usk, ρ)` is accepted as a credential of
the protocol (`Protocol::credential`), whose holder then attests and proves membership; under
`Core`, whose IETF `Verify` takes byte messages only while `ρ` from `PrepareIssue` is uniform, it
compares their `B` for the two scalars with ours byte for byte instead; and presentations do not
cross: a `Σ-BBS` membership proof of this crate has 400 bytes, an IETF BBS proof with two
undisclosed messages 336 (`3 · 48 + 6 · 32`: `Ā, B̄, D`, the responses for `e, r_1, r_3` and the
two messages, and the challenge): the 64 bytes are the two responses of the third clause, and the
challenge and the layout differ as well.

## Lattice instantiation (feature `lattice`)

Normative bytes of the backend `pcreds::lattice::LatticeBackend`. Its digest of `pp`, its
contexts and its `H_req` transcript are the protocol's ("Oracles and proof contexts" above, with
`backend = "vSIS+LWR"`); what the backend adds is its own oracles, objects and proof format. The
paper fixes the inputs of the oracles (§6.1.3, "Random oracles"); the bytes are this crate's,
and the proof sizes and costs do not depend on them. Every integer is little-endian.

### Framing and sampling

* **Items.** `frame(label, data) = LE64(|label|) ‖ label ‖ LE64(|data|) ‖ data`, as in the
  module `hash`. An oracle input is `frame("dst", "PCS-V1" ‖ suffix)` followed by the items of the
  table below, hashed with SHAKE128.
* **Uniform values below a modulus** `m` (`q = 1,048,573` or `q_t = 983,040`, both with
  `bitlen(m − 1) = 20`): the SHAKE128 output is read as a little-endian bit string and cut into
  consecutive 20-bit chunks, each little-endian (five bytes are two chunks); a chunk is accepted
  iff it is below `m`, and the accepted values fill the output in order (row-major for a matrix).

| oracle | suffix | items | output |
|---|---|---|---|
| element `name` of `pp_Σ` (`v`, `b_u`, `B_r[0]` to `B_r[2]`, the index in decimal) | `/LATTICE-PP` | `("deployment", L)`, `("element", name)` | 1024 values below `q` |
| Jali's `pp_seed` | `/LATTICE-JALI-SEED` | `("deployment", L)` | the first 32 bytes |
| `H_mat(y)` | `/LATTICE-HMAT` | `("deployment", L)`, `("input", y)` | 168 × 1024 values below `q_t`, row-major |
| the identifier point `x_0 = H_id(⟨hvk⟩)` of a helper key | | `y = hid ‖ d`, for the 32-byte digest `d` of the `/PCREDS-HID` transcript | |
| a recipient point `x_Q` | | `y = req ‖ d`, for the 32-byte digest `d` of the `/PCREDS-HREQ` transcript | |

`L` is the deployment label. The labels `hid` and `req` have one length, so the inputs of the
identifier points and of the recipient points never coincide; the rule `x_Q ≠ x_0` compares the
matrices. The oracle `H_subj` of the PRC appendix is not implemented.

### Objects

| object | bytes | size |
|---|---|---|
| element of `R_q` (`h`, `Ĉ`, the elements of `pp_Σ`) | the 1024 coefficients in `[0, q)` at 20 bits each, little-endian bit packing | 2560 |
| ternary polynomial (`usk`, `x_{0,0}` to `x_{0,2}`, `x_1`) | coefficient `i` as the 2-bit two's-complement code at bits `2i, 2i+1` (`0 → 00`, `1 → 01`, `−1 → 11`; `10` is rejected) | 256 |
| tag (`id_Q`, `t`) | 168 × LE16; every byte string is a canonical tag (`p = 2^16`) | 336 |
| `s = (s_0, s_1)` | 2048 coefficients at 20 bits, two's complement, little-endian bit packing; `−2^19` is rejected | 5120 |
| `pp_Σ` (`VSISParams`) | `v ‖ b_u ‖ B_{r,0} ‖ B_{r,1} ‖ B_{r,2}` | 12,800 |
| `hvk` (`VSISVerificationKey`) | `h` | 2560 |
| signing key (`VSISSigningKey`, SECRET) | `ntru-trapdoor`'s secret key (header `0xAA`, `f, g` at 10 bits, `F, G` at 13 bits; 5889) ‖ `LE64(issued)`, the issuance count | 5897 |
| `τ` (`VSISTape`, SECRET) | `x_{0,0} ‖ x_{0,1} ‖ x_{0,2}` | 768 |
| `σ̂` (`VSISPreCredential`) | `s ‖ x_1` | 5376 |
| `σ` (`VSISCredential`, SECRET) | `s ‖ x_1 ‖ x_{0,0} ‖ x_{0,1} ‖ x_{0,2}` | 6144 |
| `σ*` | `()`, the empty encoding | 0 |
| point (`LatticePoint`) | `00 ‖ d` for an identifier point, `01 ‖ d` for a recipient point, `d` the 32-byte digest of the oracle's transcript | 33 |
| Jali proof (`LatticeProof`) | `LE32(len) ‖` the bytes of `Compiled::prove_bytes_with_seed` | `4 + len` |
| `LatticeParams` | `LE64(len(L)) ‖ L`; `format`, 16 × `LE64` (3, `d` = 1024, `q`, `γ` = 15, `p` = 65,536, `q_t`, `m` = 168, `⌊γ/2⌋` = 7, `e_deg` = 128, `β_u` = `β_x` = `β_r` = 1, `ℓ_r` = 3, `⌊β_s²⌋` = 90,803,788,942, the proof degree 128, `Q_max` = 2^48); `pp_Σ`; `pp_seed` (32); the SHA-256 of the `tag`, `att`, `iss` and `possess` parameter files (128); `LE64(5) ‖` the Jali version (`0.3.0`, ASCII); `LE64(31) ‖ R_att:s=bdlop;R_Possess:s=bdlop`, then, in the default extractable build and not in the plain build of the feature `lattice-plain`, `LE64(20) ‖ jali-extractable:rom` and the SHA-256 of the four extraction files in the same order (128) | `13,304 + len(L)`, plain build `13,148 + len(L)` |

Every decoder checks canonicity whatever `Validate` flag it is given, so a non-canonical tag
`T + p z` cannot be represented. The decoder of `LatticeParams` refuses every item but the label,
`pp_Σ` and `pp_seed` unless it is this build's, and `Protocol::from_public_parameters` compares
those three with what the label derives. Decoding the signing key validates the trapdoor
(`fG − gF = q`, `f` invertible).

**Messages** (`pcreds::codec`, with each proof as `LE32(len) ‖ bytes`):

| object | layout | bytes |
|---|---|---|
| `AttestationRequest` | `id_Q ‖ π_id` | `340 + len(π_id)` |
| `Attestation` (`size()`, the paper's `\|att\|`) | `t ‖ σ* ‖ π_att` | `340 + len(π_att)` |
| `CredentialRequest` | `id_Q ‖ LE32(k) ‖ att_1 ‖ … ‖ att_k ‖ Ĉ ‖ π_iss` | `340 + Σ size(att_j) + 2564 + len(π_iss)` |
| … its `size()`, the paper's `\|π\|` | the attestations, `Ĉ` and `π_iss` | `Σ size(att_j) + 2564 + len(π_iss)` |
| `MembershipProof` | `σ* ‖ π_prove` | `4 + len(π_prove)` |
| `Reply` | `0x00` (`Fail`), `0x01` (`issued`), or `0x02 ‖ σ̂` | 1, 1, 5377 |

A proof's length is bounded by its kind: twice the estimated size of its parameter set, 58,336
bytes for `π_id`, 282,832 for `π_att`, 196,264 for `π_iss` and 272,208 for `π_prove`
(`lattice::sets`). The encoders refuse a longer proof, the decoders refuse its length before they
read it (and allocate only as the input arrives), and the verifiers refuse it before any work; a
stand-alone `LatticeProof` decodes up to Jali's own limit of 16 MiB. Jali proofs vary in length
by tens of bytes with the proof seed, hence the length prefix; Jali's decoder is strict, so a
valid proof has exactly one encoding. Measured sizes: [Testing and
benchmarks](./testing-and-benchmarks.md).

**Canonical and stored encodings.** The canonical encodings of the messages are the compact ones
with `LE64(k)` in place of `LE32(k)` (a proof has the same bytes in both). `PublicParameters` is
`LE64(len(L)) ‖ L ‖ LatticeParams` (`13,156 + 2·len(L)` bytes, `13,312 + 2·len(L)` in the extractable build); `Helper::to_bytes` (SECRET) is
`pp digest ‖ hvk ‖ signing key` (8489), and `Helper::to_bytes_reserving(n)` writes the count as
`min(issued + n, Q_max)`; `User::to_bytes` (SECRET) is `usk ‖ id ‖ pp digest ‖ helper fingerprint` (656);
`IssuanceState::to_bytes` (SECRET) is `τ ‖ id ‖ pp digest` (1136); `Credential::to_bytes`
(SECRET) is `σ` (6144); `IssuanceRecord` is `LE64(n) ‖ (LE64(336) ‖ id)…` (`8 + 344n`). The
signing key's last eight bytes are the issuance count: store the key after issuing, or before
issuing with `to_bytes_reserving(n)` ([Operating a helper](./operating-a-helper.md)).

### Known answers

For the deployment label `PCS-LATTICE-KAT`, pinned by unit tests and reproduced by independent
Python references (hashlib; `tools/lattice/ref_oracles.py`, `ref_tag.py` and `ref_contexts.py`):

| value | |
|---|---|
| `v`: first four coefficients, last, sum mod 2^32 | 770406, 508595, 476174, 818112; 192742; 537406709 |
| Jali's `pp_seed` | `2f7422b974aa61558962998657ba3c3a92e47a919c5def8f057821d7c701d01a` |
| `H_mat(hid ‖ d)` for `d` = SHA-256 of `x_0 of the known answers`: first four entries, last entry, sum mod 2^32, SHA-256 of its 430,080-byte packing (20 bits per entry, row-major) | 496402, 514285, 814601, 373056; 159920; 2864530562; `83c01a4e4e6c40c17e20fbd030a2bfe853def93ca4d74d9cbcecf411bae4cb03` |
| `H_mat(req ‖ 00 01 … 1f)`: the same | 428025, 418361, 942340, 678679; 615441; 2927140858; `79f2ea330ea17730f898ebf167ab8aed56ec61870aac328a71b7ff534e74b9cf` |
| `Tag(K, x_0)` at that point, for `K_i = ((i · 0x9E3779B1 mod 2^32) >> 16) mod 3 − 1`: first entries, SHA-256 of its encoding | 40124, 45340, 45497, 37072; `8be2ced09c3f47fadf4110f242dd1c0aa7bd4ea01f53022ff836e210c2daf227` |
| the encoding of `LatticeParams`: length, SHA-256 | 13,319, `dc88a6b25cc276ff679d826a34501fa1fcd86f3709e100f79a55b61e0969e901` |
| digest of `pp` | `8da1f24b0fd228f2d91355d4000d8f80a7319a8bedf78d73606abcb8ba67a8c6` |
| `d` of the identifier point for `hvk` = (5, …, 5) | `1863d36961913c03444e2a54ba10090f1c33db0ba05d4eeba996a2b0a1727628` |
| `d` of the recipient point for that `hvk` and `id` = bytes 0..255 then 80 zero bytes (counter 0) | `605e2b468a168d41b20511d4831b49dd34134e891d396f8802b66f2a939c5761` |

The last four values are those of the default, extractable build with Jali 0.3.0, whose version the encoding of `LatticeParams` holds. In the plain build
(feature `lattice-plain`, `ref_contexts.py --plain`) they are 13,163 and
`da6a6903e9113c4e683154190cd73d0dec1e869d4a3ba4c8fd2db7e83fad4373`,
`41713d9df7435f52f92385e25eb0f07085b8e8d44301fde19395745c1ac7aaf3`,
`d8d8b3a1e46327596631a2afa95a7469f2bb5d4318fb2ec66fc08610736e3538` and
`adf57807ac7426481b307f96d020eadf00af83ee7e862aced4dea03f7bf97df2`.

The parameter sets are pinned by SHA-256 (`lattice::sets`): `tag` `aa598dab…b430`, `att`
`b7f5fd92…c736`, `iss` `99497d95…1db3`, `possess` `18ad0181…df45`. So are their extraction sets:
`tag` `355b5f5a…187a`, `att` `796c2cd6…9e4b`, `iss` `d51e5f21…957b`, `possess` `5c647553…8254`.

### JSON

With the features `lattice` and `serde`, the lattice objects are opaque strings like every other
leaf (the secrets `usk`, `τ`, `σ` and the signing key through the adapter `secret`), and the
messages have the structured shapes above. The texts are about 1.37 times as long as the
canonical bytes, and base58btc takes time quadratic in the length of a string (multibase 0.9,
through `base-x`), which these strings make expensive: an attestation with a proof of 87,500
bytes is 119,993 bytes of JSON and took 0.94 s to encode and 0.67 s to decode; a credential
request at `k = 5` (five such attestations and a `π_iss` of 44,400 bytes) is 664,618 bytes and
took 4.8 s and 3.5 s (2026-10-18, release, the machine of [Testing and
benchmarks](./testing-and-benchmarks.md); `cargo test --release --features lattice --test
serde_json -- --ignored --nocapture lattice_json_cost`). Prefer the compact format for lattice
messages. The decoders refuse an over-long leaf before decoding it (above), so a forged text
costs no more per byte than an honest one.
