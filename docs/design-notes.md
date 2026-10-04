# Design Notes

How the implementation is put together, and why. None of this changes what honest parties
compute. The code follows the paper's boxes step by step; the few places where it adds to them
are listed under [Relation to the paper](#relation-to-the-paper).

* Statements of proofs are linear relations over `G_1`, `G_2` and `G_T` with one shared variable
  space; a witness coordinate that occurs in several equations is one variable with one mask and
  one response (witness-preserving AND composition). `G_T` equations are kept in lazy
  pairing-product form, so proving and verifying cost one multi-pairing per equation and no
  exponentiation in `G_T`.
* Fiat-Shamir proofs are compact `(challenge, responses)` pairs. The challenge hashes the caller's
  context **and the complete statement** (every base and target) and the commitment; the test
  suite mounts the weak Fiat-Shamir attack (a tag or a shown credential chosen after the
  challenge) and checks that it fails.
* Decoding accepts the identity point and the zero scalar. Every non-degeneracy requirement of
  the paper is therefore an explicit check in the verifier of the corresponding relation. This
  includes verification KEYS: the possession verifier rejects a key under which its clauses do
  not depend on a certified value, and `CredentialBase::is_well_formed_key` is the membership
  test for the range of `KeyGen`, to be run once on a key received from elsewhere.
* The algorithms of `PCS` do not depend on how their inputs were built. `Attestation`,
  `IssuanceProof` and `RootRequest` have public fields, and arkworks offers unvalidated and
  uncompressed decoding; only validated compressed decoding (`from_bytes`, `from_compact_bytes`)
  guarantees that a value of type `E::G1` is on the curve and in the prime-order subgroup.
  Every algorithm that consumes an object of another party (`verify_attestation`,
  `verify_proof`, `issue`, the root path, `prove`, `attest`, `unblind`, `verify_cred`)
  therefore re-validates it first (`ark_serialize::Valid::check` on `hvk`, `id` and the whole
  object) and returns `Error::InvalidGroupElement` (`false`) otherwise. This is load-bearing:
  pairing equations do not see a component of small order in a `G_1` argument, and the Schnorr
  clause of a tag shifted by a point of order 3 (the cofactor of BLS12-381 `G_1` is divisible
  by 3) verifies after three attempts on average, so that without the check ONE attester
  passes the distinctness check as two and a requester passes self-exclusion with its own
  attestation. The regression tests mount both for every base. Decode with the validating
  decoders all the same; they reject such values at the door. (The stand-alone proofs of the
  lower layers, `kiprf::verify_tag` and `cred::verify_possess`, leave this check to
  their caller.)
* `H_1` has no deployment input: a Fiat-Shamir proof is bound to a deployment only through its
  context, which must contain (a digest of) the public parameters, as `ctx_j` and `ctx_0` of the
  construction box do. The stand-alone tag and possession proofs absorb their parameters.
* Proof sizes. The number of responses of an attestation proof and of `π_0` is a constant of the
  base (`POSSESSION_VARIABLES`, `ISSUANCE_VARIABLES`), which makes the compact encoding
  `FSProof::serialize_compact` decodable without a length prefix. The byte sizes of the paper's
  comparison table (§5.3) are those of this fixed format; the derived canonical encoding is 8
  bytes longer per proof and per vector.
* `PCSTag::IDENTITY_IS_DLOG` is a type-level promise about instances built by `PCSTag::setup`.
  Whether a given tag INSTANCE (assembled from parts, or decoded) satisfies `Tag(K, c_0) = g^K`
  is answered by `PCSTag::identity_is_dlog`; `check_compatibility` uses both.
* Restart loops run behind a well-formedness check. `UKeyGen` of the construction box restarts
  while a tag evaluation is `⊥`; under degenerate tag parameters (a `Tag_DY` instance whose
  generator is the identity) EVERY evaluation is `⊥` and such a loop never terminates. Validated
  decoding refuses that instance, and for one decoded without validation
  `PCSTag::is_well_formed` is `false` and `check_compatibility` / `check_dv_compatibility`
  return `Error::DegenerateInput("pp_Tag")`, for every base. The rule: a loop that restarts on
  `⊥` runs only under a tag instance that passed one of these checks. The loops of the
  conformance flows and of `PCS::user_keygen` are guarded this way and bounded on top.
* `Unblind` of every base follows its box and does not verify its result. The construction
  fails closed ONCE, in `PCS::unblind`: it runs `VerifyCred` on the unblinded credential and
  returns `InvalidPreCredential` if that fails, for every publicly verifiable base (module `pcs`,
  "Rules the construction has to keep"). The designated-verifier variant cannot do this: a user
  has no `dvk`.
* The construction follows the protocol box step by step (the step numbers are in the code).
  `R_att` and `R_issue` are built by the public functions `PCS::attestation_relation` and
  `PCS::issuance_relation` over ONE variable for `usk`, with the witness builders next to them,
  so that a harness can run the interactive protocol, its simulator and its extractor on exactly
  the relations the proofs use. The contexts `ctx_j`, `ctx_0` are public functions of public
  data as well; every verifier rebuilds its context and never takes one from the prover.
* Every Fiat-Shamir context starts with a digest of `pp` that covers the deployment label, and
  attestations, issuance proofs and root requests hash under three different labels.
* `VerifyProof` accepts EXACTLY `k = f.threshold` attestations, and `f` itself (not only
  `EncPred(f)`, a hash that does not reveal `k`) is part of `ctx_0`. The fixed-format decoder
  takes the number of attestations from `f` and the numbers of responses from the base; nothing
  is read from the wire.
* `VerifyAtt`, `VerifyProof`, `Unblind` and `VerifyCred` check that `hvk` consists of group
  elements and lies in the range of `KeyGen` (once per call). `Attest` does not (the holder
  checks a key once, when it receives it; `Unblind` has done so), and like the box it does not
  verify its own output: with the weak base
  `Σ-BBS`, `Attest` on a credential that does not belong to `(usk_j, f_j)` returns an attestation
  that `VerifyAtt` rejects, where `Σ-PS` and `Σ-EQ` return an error.
* Clause builders check the caller's variable before they allocate their own
  (`Error::UnallocatedVariable`, relation untouched): a foreign handle with the right index
  would otherwise alias a fresh variable, e.g. `ρ`, without any error.
* Randomized algorithms take an explicit `RngCore + CryptoRng` (rand 0.8, as re-exported by
  `ark_std::rand`). Tests are seeded and reproducible.

## Limitations

* **Secrets in memory.** Secrets owned by this crate are wiped on drop (the witness container
  also wipes a buffer it outgrows instead of leaving that to the allocator), but field elements
  are `Copy` and temporaries may remain on the stack.
* **Plain Fiat-Shamir in the random-oracle model.** Knowledge extraction is by rewinding; the
  interactive protocol, its simulator and its extractor are exposed so that the test harness can
  exercise them directly. The paper takes straight-line extractable proofs as its default
  instantiation and says: "With plain Fiat-Shamir the theorems still hold for sequential
  issuance and constant `k`, with the losses just described" (Remark "Concurrent issuance"). The
  crate does not enforce sequential issuance.
* **Attestations are standing endorsements** (Remark of that title): an attestation binds `id`
  and the attester's key, no session, epoch or predicate, and can be presented again for the
  same `id` under any predicate. Neither remedy of the Remark (a helper nonce in the attestation
  challenge; the helper recording the tag sets it has seen) is implemented.
* arkworks' `DefaultFieldHasher` differs from RFC 9380 `hash_to_field` when hashing to the
  scalar field (zero-padding length). It is used as a random oracle only and does not
  interoperate with RFC 9380 hashers.

## Relation to the paper

The algorithms follow the paper's boxes and remarks, including the key spaces of `Σ-PS` and
`Σ-MAC`, the transparently derived generators of `Σ-BBS`, thresholds `k ≥ 1`, the explicit input
checks of `VerifyProof`, and the root request of Remark "Chaining and the base case". What the
code adds, or fixes where the paper leaves a choice:

* **Sizes.** `|cred|` here is the size of the PCS credential `(cred_Σ, m_aux)`: 96 B for `Σ-PS`,
  112 B for `Σ-BBS` (`cred_Σ = (A, e)` has 80 B, `m_aux = ρ` another 32 B) and 192 B for `Σ-EQ`
  (`(Z, Y, Ỹ)`; its shown form `cred*` has 336 B). `|att|` and `|π|` are 240/1392, 416/2272 and
  480/2512 B over BLS12-381 at `k = 5`, in the fixed format without length prefixes.
* **`Σ-EQ` shows.** A re-randomized `cred'` verifies on the new representative `M' = M^r`
  (SPS-EQ verification is per representative), and `Unblind` returns `ĉred` unverified as in
  the box; the construction's `Unblind` verifies once for every base.
* **The policy `P`** is a field of `PCS` next to `pp` and is not hashed into the contexts: the
  verifier's policy decides, and a proof made under a laxer policy is rejected by `CheckAtts_P`
  of a stricter verifier.
* **Identity point.** `PCSTag::setup` programs `H_2(c_0) = g_1` for every base, following Remark
  "Identity point", so that `id = g_1^usk` whenever the tag is `Tag_DDH`.
* **`Setup` takes no RNG**: every parameter of the classical construction is derived by hashing
  the deployment label. **`UKeyGen` returns a `Result`**: the error case carries implementation
  failures and the exhaustion of its restart bound (`MAX_KEYGEN_ATTEMPTS = 64`, each restart
  having probability about `2/p` under well-formed parameters).
* **Additional checks.** `ValidTag(id, c_0)` is required in `Attest` and `VerifyAtt` as well;
  `Issue` compares its argument `hvk` with the copy inside `hsk`; `hsk` records the digest of
  its `pp` and refuses to issue under another one; received group elements are re-validated by
  every algorithm; received public parameters must EQUAL what `Setup` derives from their label
  (`PCS::from_public_parameters_with_base` compares `pp_Σ` with base parameters the caller
  derived itself, for the IETF parameters of `Σ-BBS`).

## The lattice instantiation (feature `lattice`)

The post-quantum instantiation of construction.tex (sec:pq-construction): the credential base
`Σ-vSIS` (`cred::VSIS`, an NTRU trapdoor from the crate `ntru-trapdoor`), the short-key
`Tag_LWR` (`kiprf::LWR`), and Jali proofs in place of the Fiat-Shamir-compiled sigma protocols,
as `pcs::lattice::LatticePCS`, which implements `PredicateCredentialSystem`.

* **Architecture.** A set of modules behind one cargo feature, without a refactor of the pairing
  code: `lattice` (constants, ring types, the SHAKE128 oracles, the embedded Jali parameter
  sets), `cred::vsis`, `kiprf::lwr` and `pcs::lattice`. The protocol logic of the box exists
  twice, in `pcs::construction` (generic over pairing-based bases and tags) and in
  `pcs::lattice` (for one base and one tag); the trait `PredicateCredentialSystem` is the common
  interface, and both follow the same rules (module `pcs`, "Rules the construction has to
  keep"). The traits `SigmaFriendlyCredentialBase` and `PCSTag` are tied to sigma protocols over
  groups and do not fit Jali's statements.
* **One parameter set.** Ring degree 1024, `q = 2^20 − 3`, NTRU width 2, `ℓ_r = 2`, all short
  messages ternary, `⌊β_s²⌋ = 90,803,788,942`, and the tag set `(γ, p, q_t, m) = (15, 2^16,
  983,040, 168)` at proof degree 128 (`lattice`). The three Jali parameter sets (`R_att`,
  `R_issue`, `R_issue` for root requests) were derived for exactly these values and for exactly
  the statement layouts of `pcs::lattice::relations`, a line-by-line port of the validated
  harness (block names and order, exact norms, `s` in the BDLOP part, the rounding errors as
  subring blocks of the proof degree). They are embedded, pinned by SHA-256, loaded with Jali's
  strict decoder and `check()`, and their digests enter the digest of `pp`.
* **One real helper key.** `HKeyGen` is `TrapGen`; `Issue` and `issue_root` sample preimages
  with `SampPre` at the target of `BlindIssue`, with fresh coins per call, under the issuance
  cap `Q_max = 2^48` (counted in the signing key, carried in its encoding;
  `HelperSecretKey::to_bytes_reserving` stores the count ahead of issuance). The validation
  harness solved a key per credential instead; nothing of that remains.
* **Exact preimages.** `ntru-trapdoor`'s `SampPre` rounds a floating-point lattice point, exact
  with a measured margin of about `2^26`, not by proof. The paper asks for `s ∈ Λ_t` "in integer
  arithmetic" (bb:864), so the signing key checks `s_0 + h s_1 = t mod q` exactly (one NTT
  product with the prepared `h`, about 20 µs, next to 161 µs for `SampPre`) and the norm before
  a preimage leaves it, and refuses a sample that fails (never observed).
* **Bounded proofs.** Inside an attestation, an issuance proof or a root request, a Jali proof
  has at most twice the estimated size of its parameter set (171,216 bytes for `R_att`, 85,824
  for `R_issue`); the decoders and the verifiers refuse a longer one before any work. Honest
  proofs have 0.95 to 1 times the estimate, so no honest verdict changes; garbage of up to Jali's
  16 MiB would otherwise be decoded, hashed into `ctx_0` and handed to a statement compile
  (0.2-0.3 s each).
* **Fresh randomness everywhere.** Jali and `ntru-trapdoor` take 32-byte seeds; each proof,
  `SampPre` call and `TrapGen` gets a fresh seed from the caller's RNG (`lattice::fresh_seed`),
  never reused. A Jali `RestartLimit` is retried with a new seed (3 attempts).
* **Types that cannot hold what the relations do not check.** Jali binds public constants
  modulo the modulus of their constraint: a non-canonical tag `T + pz` has the witnesses of `T`,
  and a non-binary `φ` admits a credential-free possession witness (`s = 0`). `LWRTag` stores
  entries below `p = 2^16` and `BinaryPoly` stores bits, so neither can be represented. The
  verifiers evaluate `ValidTag` on every tag all the same; `φ ∈ M_pub` holds by type and leaves
  nothing to evaluate (the verifier computes the constant `b_φ φ` from the bits itself). Unit
  tests show both effects on the relations themselves.
* **Order of the checks.** `VerifyProof` runs the cheap public checks first (threshold, count,
  key, `ValidTag`, canonical `C`, distinct tags, self-exclusion, policy), then the Jali
  verification of `π_0`, then the `k` attestation proofs (each about 3 s and 0.5-0.6 GiB): one
  after the other, or in parallel with the feature `parallel`. The verdict is the box's; only the
  reason reported for a proof that fails several checks can differ.
* **Parallel attestation verification** (feature `parallel`). The `k` attestation proofs of
  `CheckAtts_P` are independent, so `VerifyProof` (and `Issue`) and `Prove` verify them on the
  rayon pool of the calling thread, in batches of the pool's width `n`; each batch uses rayon's
  short-circuiting `all`, and no batch starts after a failure. The result is the sequential one
  for every input (`Ok`, or `InvalidAttestation` whichever attestations fail); only the time
  changes. This rests on `VerifyProofAtt` never panicking, as documented: were it to panic on
  some input, the two builds could differ only between that panic and `InvalidAttestation`
  (either build could be the one that panics), never in accepting. A verification that has
  started runs to its end even when another one fails, so a call whose first attestation fails
  can still cost up to `min(k, n)` verifications, where the sequential loop costs one. A call
  holds up to `min(k, n)` verifications at once. The batches are what bounds it:
  with one parallel iterator over all `k`, rayon lets a thread that waits inside one verification
  (Jali's own parallelism nests inside each one, on the same pool) start another; a model of the
  nesting held `n + 1` items at once on `n = 3` and `n = 4` threads, and never more than `n`
  with the batches. The verifying threads share only the policy-free parts of `LatticePCS` (a
  private borrowed view), so a custom policy need not be `Sync`; it runs once, on the calling
  thread, before any proof.
* **Contexts.** SHA-256 transcripts of the paper's tuples `ctx_j`, `ctx_0`, `ctx_root` under
  three oracle suffixes, led by a digest of `pp` that also covers what Jali's verification
  depends on and the paper's `pp` does not name: Jali's `pp_seed` (derived from the label, never
  chosen by the helper), the parameter-set digests, the Jali revision and the placement of `s`.
* **Caches.** The parameter sets, the rings, `pp_Σ` as Jali polynomials and the rows of `c_0`
  are built once per `LatticePCS`; `s_i = H_0(⟨id_i⟩)` and its rows once per call. Statement
  building, `H_0` and the rows of a tag matrix cost 8-17 ms per proof, against seconds in Jali; compiled statements
  cannot be cached (every proof has its own constants, and Jali has no shape-level
  compilation).
* **Unblind verifies once**, inside `Σ-vSIS.Unblind`, as the box of the base prescribes.

### Limitations of the lattice instantiation

* **No security theorem covers the code yet.** The paper states the post-quantum theorems
  through `thm:pq-security`, which it references but does not state, for an online-extractable
  argument system; Jali's proofs are Fiat-Shamir with extraction by rewinding, and the exactness
  of the extracted norms is a property of Jali's design (`extraction_bound`), not a proven
  theorem. By the paper's Remark "Concurrent issuance", plain Fiat-Shamir supports its theorems
  only for sequential issuance and constant `k`. A helper that serializes its `Issue` calls does
  not thereby meet that assumption: issuance is one message each way, and what a rewinding
  extractor needs constrained is when an adversary makes the random-oracle queries of its proofs
  relative to its other requests, which no helper controls. `Issue` therefore stays concurrent
  (performance first). Multi-proof zero knowledge is accounted linearly (2^-128 up to about 2^39
  proofs at proof degree 128).
* **Rotation across helper keys** is the helper's (the trait takes one `hvk`); restoring an old
  key encoding rolls the issuance counter back, and two live copies of one stored key count
  separately (one live instance per stored key; `docs/operating-a-helper.md`).
* **Variable time** in Jali, `SampPre` (floating point, rejection) and `TrapGen`.
* **Memory**: about 0.5-0.6 GiB per `R_att` proof or verification, and with the feature
  `parallel` up to `min(k, n)` attestation verifications at once per `VerifyProof`, `Issue` or
  `Prove` on a pool of `n` threads (2.0-2.5 GiB at `k = 5` on five threads or more); bound it with
  `RAYON_NUM_THREADS` or a rayon pool of your own ([Operating a helper](./operating-a-helper.md)).
* **Out of scope**: the private credential requests (PRC) of the paper's appendix, which need
  `Req` and a session context `χ` that the trait does not have; JSON forms for the lattice
  objects.
* **Platforms**: only aarch64 (Apple M4) was measured. `SampPre` computes in floating point, so
  the exact preimages may differ across platforms (their validity is checked exactly before
  release); the tests assert proof lengths within a band, not exactly.
* **CI**: Jali and `ntru-trapdoor` (https://github.com/etairi/ntru-trapdoor) are git
  dependencies pinned by revision, so a checkout of this repository alone resolves every
  dependency, as in `.github/workflows/pcs.yml`. Until 2026-10-04 `ntru-trapdoor` was a path
  dependency (`../ntru-trapdoor`), and without that sibling checkout every command that resolves
  dependencies failed, whatever the features.
