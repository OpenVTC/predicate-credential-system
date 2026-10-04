# Encodings and Interoperability

The canonical wire format is the compressed arkworks encoding (module `serialization`), plus the
fixed-format compact codec of `pcs::codec` for attestations and issuance proofs, which reproduces
the byte sizes of the paper's comparison table. Two further representations exist. The lattice
instantiation (feature `lattice`) has its own byte formats, oracles and contexts: see
[Lattice instantiation](#lattice-instantiation-feature-lattice) at the end.

## JSON (`serde` feature)

The canonical wire format stays the compressed arkworks encoding (`serialization`, and the
fixed-format compact codec for `att` and `π`). With the `serde` feature every protocol object
also has a JSON form (module `serialization`, "Text forms"): a value with a canonical encoding is
one multibase base58btc string (`z…`, the convention of a W3C Data Integrity `proofValue`), while `Predicate`,
`Attestation`, `IssuanceProof` and `RootRequest` are objects with camelCase members, e.g.
`{"tag":"z…","shown":"z…","phi":"z…","proof":"z…"}`, so that a policy engine can read the `phi`
of each attestation. Decoding is strict (base58btc only, validated canonical bytes, no trailing
bytes, no unknown members). Secrets (`UserSecretKey`, `IssuanceState`, `Credential`, signing
keys) have a JSON form too, meant for protected storage only. `tests/serde_json.rs` runs a join
that travels as JSON end to end for every pair.

## Interoperability with IETF BBS (`cred::bbs::ietf`)

Not part of the paper. `BBSPublicParams::ietf(interface, vk, header)` derives the generators
of `Σ-BBS` as the IETF ciphersuite BLS12-381-SHA-256 does (`h_0 := P_1 + domain·Q_1`, and
`h_1, h_2, h_3` := the generators that carry `usk`, `φ`, `ρ` in the core, the blind or the
pseudonym interface). Under these parameters a credential `(A, e)` and an IETF BBS signature
are the same object; `to_ietf_bytes` / `from_ietf_bytes` convert keys and credentials
(big-endian scalars). Because `h_0` depends on the helper's key and on the header, such a
deployment is set up with `PCS::setup_with_base_parameters` and received with
`PCS::from_public_parameters_with_base`.

`tests/bbs_ietf_interop.rs` checks this in both directions against `affinidi-bbs` 0.3.3, the
BBS crate of the Affinidi / OpenVTC stack (on `bls12_381_plus`); that crate is a pinned
dev-dependency and never part of a build of the library.

Compatible, and tested in both directions: core signatures over three messages, blind issuance,
and the pseudonym interface with signer entropy `0` (with non-zero entropy the certified key is
`usk + entropy`, not the `usk` behind `id`); the show of this crate on a credential they
signed; and the whole construction under IETF parameters with a helper key from their `keygen`.

Deliberately NOT implemented, so an attestation or an issuance proof of this crate is not an
IETF BBS proof, and their verifier does not accept ours:

* **Challenge and proof layout.** IETF `ProofGen` proves the same relation as the `Σ-BBS` show,
  but its challenge is `hash_to_scalar` over a fixed field order with RFC 9380
  `expand_message_xmd`, and its proof bytes have their own order with big-endian scalars. This
  crate uses the strong Fiat-Shamir transcript of `sigma::fiat_shamir` and the compact `(c, z)`
  codec. Closing the gap means adding an IETF challenge function and codec next to the existing
  ones; the sigma layer would be reused unchanged.
* **Messages.** IETF BBS signs byte strings mapped by `messages_to_scalars`
  (`cred::bbs::ietf::message_to_scalar` reproduces the map); the construction certifies scalars,
  and `φ = EncPred(f)` comes from this crate's `H_0`. A credential issued by `PCS::issue` is a
  valid IETF signature, but their byte-oriented `blind_verify` cannot be asked to check it.
* **Tags.** The IETF per-verifier pseudonym is `OP^{nym_secret}` with `OP` hashed from context
  bytes under the IETF domain separator; `Tag_DDH` is `H_2(s)^{usk}` with this crate's oracle.
  `kiprf::DDH<G, H>` is generic over the oracle, so an oracle with their domain separator would
  make the two coincide; none is included.
* **Scope.** `BBSPublicParams::ietf` fixes three messages and one committed message; selective
  disclosure over `L` messages is not part of `Σ-BBS`. Only BLS12-381-SHA-256 is covered.

A bridge between the two stacks must keep this crate's own public checks
(`verify_possess_public`, subgroup validation) on everything it receives.

## Lattice instantiation (feature `lattice`)

Normative bytes of `cred::VSIS`, `kiprf::LWR` and `pcs::lattice::LatticePCS`. The paper fixes the
inputs of the oracles (construction.tex, "Random oracles of the lattice tag" and the predicate
encoding) and the tuples of the contexts; the bytes below are this crate's. They differ from the
validation harness the Jali parameter sets were checked with (its SHAKE128 prefix
`pcs-128-cost/v1`, labels such as `H_mat/<label>`, 64-bit words masked to 20 bits, no `tag` label
in `H_0`, `PredEnc` without `predicate ‖ ⟨f⟩`, contexts framed as `pcs-128-final/ctx/v1`); the
proof sizes and costs do not depend on these choices. Every integer is little-endian.

### Framing and sampling

* **Items.** `frame(label, data) = LE64(|label|) ‖ label ‖ LE64(|data|) ‖ data`, as in the
  module `hash`. An oracle input is `frame("dst", "PCS-V1" ‖ suffix)` followed by the items of the
  table below; the oracles hash with SHAKE128, the digests (`pp`, contexts) with SHA-256.
* **Uniform values below a modulus** `m` (`q = 1,048,573` or `q_t = 983,040`, both with
  `bitlen(m − 1) = 20`): the SHAKE128 output is read as a little-endian bit string and cut into
  consecutive 20-bit chunks, each little-endian (five bytes are two chunks); a chunk is accepted
  iff it is below `m`, and the accepted values fill the output in order (row-major for a matrix).

| oracle | suffix | items | output |
|---|---|---|---|
| element `name` of `pp_Σ` (`v`, `b_u`, `b_phi`, `B_r[0]`, `B_r[1]`) | `/LATTICE-PP` | `("deployment", L)`, `("element", name)` | 1024 values below `q` |
| Jali's `pp_seed` | `/LATTICE-JALI-SEED` | `("deployment", L)` | the first 32 bytes |
| `H_mat(y)` | `/LATTICE-HMAT` | `("deployment", L)`, `("input", y)` | 168 × 1024 values below `q_t`, row-major |
| `H_0(x) = H_mat("tag" ‖ x)` | | `y = tag ‖ x` (the label `tag` has length 3) | |
| `c_0 = H_0("identity")` | | `y = tagidentity` | |
| `s_i = H_0(⟨id_i⟩)` | | `y = tag ‖ ⟨id_i⟩`, the 336-byte tag encoding | |
| `EncPred(f)` | `/LATTICE-PREDENC` | `("deployment", L)`, `("input", "predicate" ‖ ⟨f⟩)` | the first 128 bytes; coefficient `i` of `φ` is bit `i mod 8` of byte `⌊i/8⌋` |

`L` is the deployment label of `SetupParams`, and `⟨f⟩ = LE32(threshold) ‖ LE64(|label|) ‖ label`
(`Predicate::canonical_bytes`). The tag encoding is fixed-length and never the 8-byte string
`identity`, so `c_0` is never an attester point (the paper's requirement on `⟨id⟩`). The oracles
`H_req` and `H_subj` of the PRC appendix are not implemented.

### Objects

| object | bytes | size |
|---|---|---|
| element of `R_q` (`h`, `C`, the elements of `pp_Σ`) | the 1024 coefficients in `[0, q)` at 20 bits each, little-endian bit packing | 2560 |
| ternary polynomial (`usk`, `x_{0,0}`, `x_{0,1}`, `x_1`) | coefficient `i` as the 2-bit two's-complement code at bits `2i, 2i+1` (`0 → 00`, `1 → 01`, `−1 → 11`; `10` is rejected) | 256 |
| `φ` | bit `i` (least significant first) is coefficient `i` | 128 |
| tag (`id`, `id_{j→i}`, `id_{i→i}`) | 168 × LE16; every byte string is a canonical tag (`p = 2^16`) | 336 |
| `s = (s_0, s_1)` | 2048 coefficients at 20 bits, two's complement, little-endian bit packing; `−2^19` is rejected | 5120 |
| Jali proof, stand-alone (`Proof`) | `LE32(len) ‖ bytes`, `len ≤ 2^24` (Jali's own limit) | `4 + len` |
| `hvk` | `h` | 2560 |
| `hsk` (`HelperSecretKey<VSIS>`) | `ntru-trapdoor`'s secret key (header `0xAA`, `f, g` at 10 bits, `F, G` at 13 bits; 5889) ‖ `LE64(issued)` ‖ `h` ‖ pp digest; `to_bytes_reserving(n)` writes `LE64(min(issued + n, Q_max))` | 8489 |
| `usk` | ternary | 256 |
| `cred` | `s ‖ x_1 ‖ x_{0,0} ‖ x_{0,1}` | 5888 |
| `ĉred` | `s ‖ x_1` | 5376 |
| `att_j` | `id_{j→i} ‖ φ_j ‖ LE32(len(π_j)) ‖ π_j`, `len(π_j) ≤ 171,216` | `468 + len(π_j)` |
| `π`, compact (`k` from the predicate) | `att_1 ‖ … ‖ att_k ‖ C ‖ id_{i→i} ‖ LE32(len(π_0)) ‖ π_0`, `len(π_0) ≤ 85,824` | `Σ len(att_j) + 2900 + len(π_0)` |
| `π`, canonical | `LE32(k) ‖` compact | `+ 4` |
| root request | `C ‖ id_{i→i} ‖ LE32(len(π_0)) ‖ π_0`, `len(π_0) ≤ 85,824` | `2900 + len(π_0)` |
| `st_iss` | `usk ‖ x_{0,0} ‖ x_{0,1} ‖ φ` | 896 |
| `c_0`, `s_i` (digests only; never on the wire) | the 172,032 entries at 20 bits, little-endian bit packing, row-major | 430,080 |

Every decoder checks canonicity whatever `Validate` flag it is given; a non-binary `φ` and a
non-canonical tag `T + pz` cannot be represented. Jali proofs vary in length by tens of bytes
with the proof seed (at proof degree 128, about 83.1 KB for `R_att` and 41.1 KB for `R_issue`),
hence the length prefix; Jali's decoder is strict, so a valid proof has one encoding. Inside an
attestation, an issuance proof or a root request a proof has at most twice the estimated size
of its parameter set (85,608 bytes for `R_att`, 42,912 for `R_issue`): 171,216 and 85,824
bytes (`lattice::sets::{ATT_PROOF_MAX_BYTES, ISSUE_PROOF_MAX_BYTES}`). The encoders refuse a
longer proof, the decoders refuse its length before reading it, and the verifiers refuse it
before any work; honest proofs have 0.95 to 1 times the estimate. The signing key's last eight
bytes are the issuance counter (`Q_max = 2^48`): store the key after issuing, or before
issuing with `to_bytes_reserving(n)`.

### The digest of `pp` and the contexts

SHA-256 transcripts of the framing above. The context handed to Jali is the 32-byte digest.

| digest | suffix | items, in order |
|---|---|---|
| `pp` | `/LATTICE-PP-DIGEST` | `label` (`L`); `format` (15 × LE64: 1, `d` = 1024, `q`, `γ` = 15, `p` = 65,536, `q_t`, `m` = 168, `⌊γ/2⌋` = 7, `e_deg` = 128, `β_u` = `β_x` = `β_r` = 1, `ℓ_r` = 2, `⌊β_s²⌋` = 90,803,788,942, proof degree 128); `pp-sigma` (`v ‖ b_u ‖ b_φ ‖ B_{r,0} ‖ B_{r,1}`, 12,800 B); `c0` (430,080 B); `jali-pp-seed`; `jali-sets` (the SHA-256 of the `att`, `issue` and `issue-root` parameter files); `jali` (the Jali revision, 40 ASCII hex digits); `placement` (`R_att:s=bdlop`) |
| `ctx_j` | `/LATTICE-CTX-ATT` | `pp` (the digest), `hvk`, `id`, `phi`, `T` (`id_{j→i}`), `cred*` (empty) |
| `ctx_0` | `/LATTICE-CTX-ISSUE` | `pp`, `hvk`, `f` (`⟨f_k⟩`), `id`, `C`, `T0`, then one `att` per attestation (its encoding above), in order |
| `ctx_root` | `/LATTICE-CTX-ROOT` | `pp`, `hvk`, `f` (`⟨f_root⟩`), `id`, `C`, `T0` |

The component `"root"` of the paper's `ctx_root = ("root", pp, hvk, f_root, id, C, id_{i→i})`
(construction.tex, Remark "Chaining and the base case") is realised by the oracle suffix
`/LATTICE-CTX-ROOT`, not by the bytes `root`: the three contexts are digests of three different
oracles, as in the pairing code (`/PCS-CTX-ROOT`). A wiped `hvk` or `C` (no element of `R_q`)
has an empty encoding and would enter a context as an empty item, which no element produces;
the verifiers refuse both before they compute a context. The parameter sets are pinned by
SHA-256: `att` `208ef25c…ad98`, `issue` `0322b83f…8c75`, `issue-root` `20aafab6…2dea`
(`lattice::sets`); `issue` and `issue-root` differ in their `id` and `estimator` strings only,
which Jali absorbs, so root requests and issuance proofs are separated by the set as well.

### Known answers

For the deployment label `PCS-LATTICE-KAT`, pinned by unit tests and reproduced by independent
Python references (hashlib; `tools/lattice/ref_oracles.py`, `ref_tag.py` and `ref_contexts.py`):

| value | |
|---|---|
| `v`: first four coefficients, last, sum mod 2^32 | 770406, 508595, 476174, 818112; 192742; 537406709 |
| Jali's `pp_seed` | `2f7422b974aa61558962998657ba3c3a92e47a919c5def8f057821d7c701d01a` |
| `c_0`: first four entries, last entry, sum mod 2^32 | 482358, 65488, 336476, 223542; 343167; 2804724483 |
| `EncPred(Predicate::new(5, "members"))`, first 16 bytes | `80602108a32f61e5cdc04e78eb3ba344` |
| digest of `pp` | `72c1d94fc0f63645ba250d0ddf9577d656d6624e794e174af05dd4093e4b9515` |
| `ctx_j` for `hvk` = (5, …, 5), `id` = bytes 0..255 then 80 zero bytes, `φ` = 128 × `5a`, `T` = 336 × `11` | `b91ef50e4f5141bf975a3b968a64d207fd0bb107879674423ba6512645865adc` |
| `ctx_0` for the same `hvk`, `id`, `f = (2, "members")`, `C` = (7, …, 7), `T_0` = 336 × `22`, one attestation (`T`, `φ`, proof `010203`) | `77502dd288188c7026193e009c0d45827cf6063fccbb1d5d81bca41043b8610d` |
| `ctx_root` for the same `hvk`, `id`, `C`, `T_0` and `f_root = (0, "founders")` | `93912252e35514603d2542daeb40afacb6e02581e8f1f7a7cb51bf37265dd1d7` |

No JSON forms exist for the lattice objects: base58btc is quadratic in the length, and an
issuance proof at `k = 5` has about 462 KB.
