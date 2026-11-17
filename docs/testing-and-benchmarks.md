# Testing and Benchmarks

What the test suites cover, how to run them, the checks a change has to pass, and the benchmarks.
The tests are evidence on sampled instances: they check algebraic and structural facts (that
honest runs succeed, that each attack fails with the expected error, that extraction recovers a
witness), not computational indistinguishability and not the reductions of the paper.

## Test suites

### The protocol `Π_PCreds` (`pcreds`)

* **`tests/pcreds.rs`**: the end-to-end flow for each of the four pairing-based pairs (`Σ-PS`,
  `Σ-BBS` × `Tag_DDH`, `Tag_DY` over BLS12-381; `ps_with_ddh`, `ps_with_dy`, `bbs_with_ddh`,
  `bbs_with_dy`): five root members admitted with `Decision::Root`, attestation requests and
  responses through contact names (`π_id` refused under another `ssid` or contact name), too few
  distinct attesters answered `Fail`, a repeated attester counted once, `k = 5` distinct attesters
  issued once and then answered `issued`, attestations bound to their recipient, the new member
  attesting and proving membership, and tampered attestations and requests refused.
  `membership_proofs_are_bound_to_message_and_key`; `sizes_match_the_paper` asserts the sizes of
  the paper's Table "Sizes" (§7.1) for all four pairs (`att` 240 / 448, `π` at `k = 5` 1344 /
  2384, `cred` 96 / 112, membership proof 192 / 400, `id` 48 bytes);
  `inadmissible_keys_and_non_members_are_refused` (a `Σ-PS` key outside `V_pp`, a credential
  that does not verify, threshold 0).
* **`tests/common/mod.rs`**: the fixtures the protocol suites share, through the public API
  only: a `Deployment` (protocol, helper under `Pol_k`, the checked `hvk`, `k` root members),
  per-base hooks for random and degenerate shows (`BaseTest`), and random objects of the right
  shape.

The suites below were ported from the suites of the earlier construction (`pcs_*.rs`); each
file's module documentation is authoritative for what it covers and lists what was ported, what
was dropped (`Σ-EQ`, predicate labels and policies, the self-exclusion tag, the separate root
path) and why.

* **`tests/pcreds_correctness.rs`**: correctness through the public API for the four pairs and,
  for genericity, over BN254 (with the INSECURE test oracle `hash::testing` behind every
  hash-to-group oracle), with a map from the lines of the protocol box to the tests, and
  negatives that each hinge on one check: received public parameters, objects of another
  deployment, helper restarts and the issuance record, root admission, any number of
  attestations and the optional limit on them,
  counting distinct valid tags, the bindings of `π_id` and `π_iss`, membership proofs, a failing
  store and helper processes sharing one, delayed replies, and `Tag_DY` at its undefined point.
* **`tests/pcreds_adversarial.rs`**: every attack mounted against the real code and required to
  fail with the exact error of the check that stops it; where the honest algorithms refuse to
  build the offending object, the adversary builds it from the public relation builders, context
  functions and Fiat–Shamir prover, and the test asserts that the bare Fiat–Shamir verifier would
  accept it. The attacks named by the paper (§7.3: degenerate shows, a self-attestation, a proof
  over an unrelated context, the scalar sampler's bias; the `Σ-BBS` issued-`e` attack is in the
  soundness suite), and among others identity tags, components of order 3, off-subgroup points,
  malformed and garbage messages, objects of other deployments and helpers, the attestation
  cap, distinct counting, attestations for another identifier, a malicious helper's answer,
  inadmissible keys and received parameters that are not `Setup(label)`.
* **`tests/pcreds_soundness.rs`**: the interactive sigma protocol on exactly the relations of the
  four proofs, at the statements and under the contexts a verifier rebuilds: special soundness
  from a forked Fiat–Shamir run (the extracted `usk` is the user's, the extracted witness yields
  a credential), special HVZK (simulated transcripts verify interactively and are rejected as
  Fiat–Shamir proofs), the weak Fiat–Shamir attack, the binding of statements and contexts, the
  malleability of possession proofs under the issuing key, recipient-scoped linkability,
  proof-gated issuance, and the attempts of a `Σ-BBS` or `Σ-PS` helper to single out a source from
  its issuance records. It states that it does not establish the theorem's hypothesis of an
  online simulation-extractable NIZK.
* **`tests/serialization.rs`**: round trips of every object through the canonical and the compact
  encodings (secrets through their wiped encodings, the helper through `restore_helper`), the
  sizes counted slot by slot independently of the library, the strictness of the decoders
  (trailing bytes, truncation, non-canonical scalars, malformed points, unknown reply tags,
  hostile counts, proofs of the wrong shape, an issuance record listed out of order or twice),
  and regression vectors of the digest of `pp` and the proof contexts.
* **`tests/serde_json.rs`** (feature `serde`): the JSON shapes of the messages, round trips, a
  complete join in which every message travels as JSON, the secrets as opaque strings, and
  strict decoding (unknown, missing and repeated members, other multibase bases, malformed
  points and scalars, unknown reply variants), and one JSON form per object (a message is
  refused as the array of its members, a reply as `{"fail": null}`).
* **`tests/bbs_ietf_interop.rs`**: `Σ-BBS` under IETF parameters (`pcreds::pairing::ietf`)
  against the pinned dev-dependency `affinidi-bbs` 0.3.3: credentials issued through the
  protocol are IETF BBS signatures and the other way round, received IETF parameters, and proofs
  that do not cross over (see [Encodings](./encodings.md)).

### The layers

* **Unit tests** (`cargo test --lib`): the transcript framing and known answers of the oracles
  (reproduced by an independent Python re-implementation, `hash`), hash-to-curve for BLS12-381,
  `Tag_DDH` and `Tag_DY` (key uniqueness on samples, the undefined point and degenerate
  parameters of `Tag_DY`, the tag proofs), the sigma layer (relations and their serialization
  and validation, the ciphersuite identifiers, protocol, Fiat–Shamir with its tag, the compact
  codec and the pairing extension), the duplex sponge (`hash::duplex_sponge`), the strict byte
  decoding (`serialization`), the non-zero scalar sampler,
  and the IETF hashing of `pcreds::pairing::ietf` (RFC 9380 test vectors, fixtures of the BBS
  drafts as vendored by `affinidi-bbs` 0.3.3).
* **`tests/sigma_protocol.rs`**: the sigma layer on relations over `G_1`, `G_2`, `G_T` and
  mixtures of them, over BLS12-381 and BN254: completeness, simulated transcripts, special
  soundness with shared variables, and the Fiat–Shamir transform.
* **`tests/ietf_vectors.rs`**: the test vectors of the IETF CFRG drafts that the Fiat–Shamir
  transform follows (`kat/ietf/`, with the hashes of the draft texts): the 23 vectors of
  `draft-irtf-cfrg-fiat-shamir-04` for SHAKE128 and the suite-independent codecs (the duplex
  sponge, `DeriveSessionID`, `DecodeUint`, the codecs, the sumcheck example), and the 47 vectors
  of `draft-irtf-cfrg-sigma-protocols-04` for `sigma-proofs_Shake128_BLS12381`: every valid
  proof reproduced byte for byte with the draft's seeded generator in both flavors (from the
  serialized instance and through the value builders of `GroupRelation` and `PairingRelation`),
  every vector given its `Expected` decision, and every adversarial vector's baseline accepted.
  The TurboSHAKE128 and P-256 vectors are out of scope.
* **`tests/jali_backend.rs`** (feature `jali`): the re-export `predicate_credential_system::jali`
  proves and verifies a commitment opening; it checks the wiring, not the lattice protocols.

### The lattice instantiation (feature `lattice`)

`cargo test` compiles it through the dev self-dependency. The suites drive `LatticeProtocol`
(`Protocol<LatticeBackend>`) through the public API; a cheating prover uses the backend's public
associated functions. A Jali proof takes seconds and up to about 0.7 GB, so every test that makes
one runs in release builds only (`#[ignore]` or
`#[cfg_attr(debug_assertions, ignore)]`, with the command in the reason).

* Unit tests of the foundations (`lattice`: constants against `ntru-trapdoor` and
  lem:tag-lwr-short, the ring types and their canonical encodings, the documented panics of wiped
  values, the SHAKE128 framing and `H_mat` with known answers that independent Python references
  reproduce, the pinned Jali parameter sets in their documented order, a changed file refused),
  of `kiprf::lwr` (TagEval against the harness and the relation, rounding at the boundaries,
  every rounding error, determinism and its need for the exact error bound), of
  `pcreds::lattice::base` (every algorithm of the `Σ-vSIS` box with ONE real NTRU trapdoor: the
  exact norm bound and `s ≠ 0`, the exact check of every preimage before release, the
  distributions of the preimages and of `x_1`, the issuance cap under concurrency, the count
  stored ahead of issuance, strict codecs, wiped values refused), of `pcreds::lattice::relations`
  (each statement compiles against its own parameter set and no other; the committed exports are
  current; Jali's witness map accepts the honest witnesses and refuses false ones; `T + p` has
  the witnesses of `T`; `s = 0` under parameters crafted to satisfy the possession equation is
  refused by the lower bound on `‖s‖²`; real proofs verify and are bound to their statement and
  context, release only) and of `pcreds::lattice` (the encoding of the parameters, the digest of
  `pp` and a recipient point, with known answers that `tools/lattice/ref_contexts.py` reproduces).
* `tests/lattice_vsis.rs`, `tests/lattice_tag.rs` (fast): the base and the tag through the public
  API: the issuance flow over the wire, the sizes of the base objects, the count carried by the
  helper's key, a key restored near the cap, sixteen threads issuing through one key with ten
  calls left (exactly ten succeed), decoders fed arbitrary bytes; the tags of an issuance, and
  the tag clauses of `R_Tag` and `R_iss` in independent re-implementations against Jali's witness
  check (`T + 1` refused, `T + p` accepted by the relation alone).
* `tests/lattice_protocol.rs`: the flow at `k = 1` with every message over the wire
  (`quick_end_to_end_k1`, release only; the CI job `lattice` runs it), a helper at its
  cap that records nothing (`#[ignore]`), and the checks that need no proof: a transparent
  `Setup` and strictly checked received parameters, recipient points bound to `hvk` and `id_Q`,
  helper keys bound to one deployment and stored with their count, users, oversized proofs
  refused before any work, decoders that never panic, the sizes of the stored objects.
* `tests/lattice_flows.rs` (`#[ignore]`): `Pol_3` with three roots: a newcomer issued on three
  attestations, chaining (the newcomer attests for a second one), membership proofs, `Fail` on two
  valid attestations (and `issued` under `d = root`), `issued` for an identifier issued before,
  and one source counted once.
* `tests/lattice_adversarial.rs` (`#[ignore]`): tampered and misdirected messages (an attestation
  with another tag, flipped, truncated or extended proof bytes, for another requester, under
  another helper key or in another deployment; a credential request with another `ssid`, order or
  selection of attestations, `Ĉ` or identifier; a membership proof on another message, under
  another key or flipped; an identifier proof for another sub-session, contact or identifier),
  each refused with the documented reason, and the honest provers' refusal of false witnesses.
* `tests/lattice_attacks.rs` (`#[ignore]`): a cheating prover with real Jali proofs: proofs under
  the context of another role, key or sub-session, proofs of one role presented in another,
  attestations that do not count (another requester, another helper key, one source twice), and a
  member attesting for itself (answered `issued`).
* `tests/lattice_sizes.rs` (`#[ignore]`): the sizes at `k = 5`, printed as a table, every proof
  within its bound.
* `tests/lattice_parallel.rs`: `evaluate_request` on a request at `k = 2` with five attestations
  (two valid, one for another requester, a second one of one source, one more valid) gives the
  same `N''`, in the same order, on the calling thread and, with `parallel`, in rayon pools of 1,
  2 and 4 threads; and an invalid attestation is not counted at any position. Release only; run
  it with and without `parallel`.
* `tests/pcreds_correctness.rs`, module `lattice`: six of the backend-generic tests of the suite
  at the lattice backend (root admission, a member attesting for itself, a delayed reply, helper
  restarts, a failing store, a shared store and a lost race; release only).
* `tests/serde_json.rs`: the lattice objects as opaque JSON strings and its messages in the
  structured shapes (with stand-in proofs); the bound on the text of each leaf (a leaf one
  character longer than the multibase text of the largest valid one of its role is refused
  before it is decoded, one at the bound reaches the decoder, a leaf of 4 MiB is refused at
  once; `max_multibase_len` bounds the text of zero, all-ones and random bytes); and
  `lattice_json_cost` (`#[ignore]`, release), which measures the JSON forms of full-size
  messages ([Encodings](./encodings.md#json)).
* `tests/lattice_support/mod.rs`: what the heavy suites share (a deployment with ONE real helper
  key and root members, timing).

The heavy tests run in release, one at a time:

```text
cargo test --release --features lattice --test lattice_protocol --test lattice_vsis --test lattice_tag
RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_protocol --test lattice_flows --test lattice_adversarial --test lattice_attacks --test lattice_sizes --test lattice_parallel --test pcreds_correctness -- --include-ignored --nocapture
cargo test --release --features lattice --lib -- lattice   # the unit tests, with real proofs in release
cargo test --release --features lattice --test lattice_tag -- --ignored --nocapture timing_probe
RUST_TEST_THREADS=1 cargo test --release --features lattice,parallel --test lattice_parallel -- --include-ignored --nocapture
```

They run the default, extractable build, and with `--features lattice-plain` in place of
`--features lattice` the plain build.

With `parallel`, a heavy test uses every core and `evaluate_request` holds up to one
attestation verification per thread of the pool at once, so keep `RUST_TEST_THREADS=1` there too.

The second command, with `lattice_vsis` and `lattice_tag` added, ran on an Apple M4 (10 cores,
16 GiB, macOS 27.0.1, rustc 1.99.1) on 2026-10-18 (CST), with the working tree of Stage 2 at
`ℓ_r = 3` on commit `c80e814` and under the ordinary load of the desktop, in two parts: 17:32-17:43,
where it stopped at a size pin of `lattice_protocol` still at its `ℓ_r = 13` value, and
18:03-18:10, for that suite and the ones not reached, with the pin and one more of `lattice_vsis`
corrected (`lattice_vsis` passing alone afterwards). `pcreds_correctness` took 271 s (33 tests, six
of them at the lattice backend), `lattice_flows` 206 s, `lattice_attacks` 173 s,
`lattice_parallel` 136 s, `lattice_adversarial` 108 s, `lattice_sizes` 82 s, `lattice_protocol`
51 s, `lattice_tag` 2.5 s and `lattice_vsis` 0.05 s: 64 tests in all, every one passing, about
17 minutes of tests, with a peak resident set of 0.73 GB. The last command took 153 s
(17:43-17:46), its two tests passing, with a peak of 2.50 GB; the unit tests of the lattice
modules took 37 s (53 tests). The same suites took 62 minutes and peaked at 2.0 GB with 13
components of `x_0` (the statistical variant, earlier the same day), and 16 minutes in Stage 1
(`ℓ_r = 2`, no lower bound on `‖s‖²`).

## Running the tests

```text
cargo test                                   # unit, integration and documentation tests
cargo test --test pcreds                     # one suite
cargo test --doc --all-features              # the documentation tests (README.md and
                                             # docs/operating-a-helper.md included)
cargo test --release --features lattice --test lattice_protocol   # the lattice flow at k = 1, release only
```

The crate's dev-dependency on itself enables `test-utils`, `serde`, `jali` and `lattice`, so a
plain `cargo test` compiles every suite, and the test profile is optimised (`opt-level = 3`): the
tests are dominated by pairings and scalar multiplications. The heavy lattice tests are
`#[ignore]`d and run as described above.

The checks a change has to pass, as in `.github/workflows/pcs.yml` (Ubuntu, Rust 1.95.0 and
stable):

```text
cargo fmt --all -- --check
cargo clippy --locked --all-targets --all-features -- -D warnings   # the extractable build
cargo clippy --locked --all-targets --features serde,jali,lattice-plain,parallel,test-utils -- -D warnings
cargo test --locked
cargo test --locked --features lattice-plain
RUSTDOCFLAGS='-D warnings' cargo doc --locked --no-deps --features serde,jali,lattice
RUSTDOCFLAGS='-D warnings' cargo doc --locked --no-deps --features serde,jali,lattice-plain
cargo test --locked --release --features lattice --test lattice_protocol quick_end_to_end_k1   # the job `lattice`
cargo test --locked --release --features lattice --lib proofs_are_in_the_mode_of_the_build
cargo test --locked --release --features lattice-plain --test lattice_protocol quick_end_to_end_k1
cargo test --locked --release --features lattice-plain --lib proofs_are_in_the_mode_of_the_build
```

## Benchmarks

```text
cargo bench --bench pcreds                       # Π_PCreds at k = 5, every pairing-based pair
cargo bench --bench pcreds -- 'pcreds/bbs-dy'    # one pair (the filter is a regex)
cargo bench --bench kiprf                        # Tag_DDH, Tag_DY
cargo bench --bench kiprf -- tag-dy              # one tag
cargo bench --bench lattice --features lattice   # Σ-vSIS, Tag_LWR, Π_PCreds at the lattice backend
```

The benchmarks use criterion with seeded inputs, so every run measures the same values, and each
first prints the SIZES of the objects it handles.

* **`benches/pcreds.rs`**: `Π_PCreds` at `k = 5` over BLS12-381 for each pair, in the groups
  `pcreds/ps-ddh`, `pcreds/ps-dy`, `pcreds/bbs-ddh`, `pcreds/bbs-dy` (seeds `0x5053_0001`,
  `0x5053_0002`, `0x4242_0001`, `0x4242_0002`). The fixture admits five root members and lets
  them attest for a newcomer; it prints `|id|`, `|att|`, `|π|` at `k = 5`, `|cred|` and the size of
  a membership proof. The functions are the rows of the paper's Table "Running time" (§7.1),
  each party's algorithm on its own:

  | function | what it measures | the paper's column |
  |---|---|---|
  | `attest` | the attester's tag, show and attestation proof (`Protocol::attest`) | Attester, attest |
  | `verify attestation` | the recipient's check of one attestation (`verify_attestation`) | Recipient, check |
  | `request (PrepareIssue + issuance proof)` | `request_credential` on five stored attestations: `PrepareIssue`, the issuance context over the attestations, `π_iss` | Requester, request |
  | `unblind` | `Unblind` with the check of the credential | Requester, unblind |
  | `verify (helper, k attestations + request)` | `evaluate_request`: `π_iss`, the recipient point, the `k` attestations and the count of distinct tags | Helper, check |
  | `blind issue` | `BlindIssue` alone, under a key of the backend (the helper's own key never leaves it) | Helper, issue |
  | `membership prove`, `membership verify` | the membership proof on a message and its check | Membership |
  | `prove (k attestations + request)` | the `k` attestations and the request together: the total work of the `k` attesters and the requester, which in deployment runs on `k + 1` machines (a throughput figure, not a latency) | (the paper's sum over all parties) |

* **`benches/kiprf.rs`**: `Tag_DDH` and `Tag_DY` over `G_1` of BLS12-381 (groups `tag-ddh`,
  `tag-dy`, seeds `0x4444_0001`, `0x4459_0001`): `keygen` (`TagKeyGen`), `eval` (`TagEval` at an
  ordinary point), `eval_identity_point` (at `x_0`, the identifier), `valid_tag` (`t ∈ T`),
  `prove_tag` and `verify_tag` (the stand-alone proof of `R_Tag`, the relation of the protocol's
  `π_id`), and `tag-ddh/h2` (`htag(x)` alone: the hash to the curve that `Tag_DDH` pays per point
  and `Tag_DY` does not). Sizes: `pp_Tag`, key, point, tag, tag proof.
* **`benches/lattice.rs`** (feature `lattice`), the post-quantum instantiation: the algorithms of
  `Σ-vSIS` (`lattice-vsis`: `PGen`, `KeyGen`, `PrepareIssue`, `BlindIssue`, `Verify`, `Unblind`,
  decoding the signing key), of `Tag_LWR` and its oracles (`lattice-lwr`: `x_0`, a recipient
  point, `TagEval` with its error, `TagKeyGen`) and of `Π_PCreds` at the lattice backend with one
  helper key (`lattice-pcreds`, seed `0x7063_0002`: `register`, `request_attestation` and
  `receive_attestation_request` (`π_id`), `attest` and `check_attestation` (`π_att`),
  `request_credential` at `k = 1, 3, 5` (`π_iss`), `evaluate_request` at `k = 5`, `respond`,
  `unblind`, `prove` and `verify` (`π_prove`)). The protocol's group takes 10 samples of one
  iteration and runs under `cargo bench` only; it first prints the sizes of the objects at
  `k = 5`.

## Reproducibility

* **Seeds.** Every test and benchmark draws from `StdRng::seed_from_u64` with the seed written at
  the call site, so a run is reproducible on the same toolchain and dependencies. The exceptions
  are recorded where they occur: `affinidi-bbs` 0.3.3 draws its own randomness in `commit`,
  `nym_commit` and `proof_gen` (no seeded variant in its public API), and the
  `docs/operating-a-helper.md` example of the lattice helper uses the operating system's CSPRNG on
  purpose.
* **Toolchain.** The minimum supported Rust is 1.95.0 (`rust-version`, edition 2024); CI runs
  1.95.0 and stable. Record `rustc --version` with every measurement.
* **Dependencies.** `Cargo.lock` is committed and CI builds with `--locked`. Jali and
  `ntru-trapdoor` come from crates.io, pinned to one release each (Jali `=0.3.0`,
  `ntru-trapdoor` `=0.1.1`), and
  `lattice::JALI_VERSION` repeats Jali's version (a unit test keeps the two equal; it enters the
  digest of the lattice `pp`).
  `affinidi-bbs` is pinned to `=0.3.3`, `sha2` must stay 0.10 (`ark-ff`'s field hasher is tied to
  `digest` 0.10) and `rand` 0.8 (`ark_std::rand` re-exports it).
* **Timings** depend on the machine, the compiler, the features (`parallel`, `asm`) and the load:
  record them with `rustc --version`, the commit and the features, pin the benchmark to one core
  for single-thread numbers (on Linux `taskset -c N`), and set `RAYON_NUM_THREADS` when
  `parallel` is on. The paper reports (§6, Table "Running time") measurements of this
  implementation on one performance core of an Apple M4 (macOS 27.0.1, single-threaded, on AC
  power), Rust 1.99.1; `benches/pcreds.rs` and `benches/lattice.rs` measure the same rows. The
  repository does not hold the output of those runs, and it records no `pcreds` timing of its
  own. `attest` and `unblind` consume their pending state (the pending request, the issuance
  state), so their benchmarks rebuild it outside the timed closure (`iter_batched`).

## Measurements of the lattice instantiation

Until 2026-11-16 the feature `lattice` built the plain mode and `lattice-extractable` the
extractable one. The commands below dated before then measured the plain build unless they name
`lattice-extractable`, and the same build is now `lattice-plain`.

Measured on an Apple M4 (10 cores: 4 performance, 6 efficiency; 16 GiB), macOS 27.0.1, rustc
1.99.1, with the working tree of Stage 2 (`ℓ_r = 3`, the two-sided bound on `‖s‖²`) on commit
`c80e814`, on 2026-10-18 (CST), under the ordinary load of the desktop (load average 3.5-4.0 at
the start of each run). The figures are criterion's estimates of the mean, with the 95 % interval
where it is wider than ±5 %: 20 samples for `lattice-vsis` and `lattice-lwr`, 10 samples of one
iteration for `lattice-pcreds`. Two runs, saved under criterion's baseline `lr3`:

1. `cargo bench --bench lattice --features lattice -- --save-baseline lr3` (17:46-17:58, 718 s,
   peak RSS 0.71 GB with the `k = 5` fixture): every function at one thread.
2. `cargo bench --bench lattice --features lattice,parallel -- lattice-pcreds --save-baseline lr3`
   (17:58-18:03, 298 s, peak RSS 2.89 GB): all ten cores.

The column `ℓ_r = 13` is the statistical variant (the paper's first regularity bound), measured
the same day at one thread in runs whose controls (`TrapGen`, `TagEval`, `H_mat`) are within 3 %
of these; its `Setup` comes from a loaded run. The last column is Stage 1 (`ℓ_r = 2`, the upper
bound only; one thread, 2026-10-17).

| group | function | what it measures | one thread | `parallel` | `ℓ_r = 13`, one thread | Stage 1, one thread |
|---|---|---|---|---|---|---|
| `lattice-vsis` | `setup` | `PGen` (the expansion of `pp_Σ`, 5 elements) | 55 µs | | 191 µs (15 elements) | 43.4 µs (4 elements) |
| | `keygen` | `KeyGen` (`TrapGen` and the expanded key) | 5.79 ms | | 5.93 ms | 5.96 ms |
| | `prepare_issue` | `PrepareIssue` (4 products) | 87.8 µs | | 313 µs | 67.0 µs |
| | `blind_issue` | `BlindIssue`: `x_1`, `SampPre` under the cap, the exact check | 245 µs | | 249 µs | 252 µs |
| | `verify` | `Verify` (5 products) | 141 µs | | 370 µs | 122 µs |
| | `unblind` | `Unblind` (one `Verify`) | 143 µs | | 376 µs | 125 µs |
| | `sk_decode` | decoding the signing key | 217 µs | | 221 µs | 226 µs |
| `lattice-lwr` | `identity_point` (now `identifier_point`) | `x_0` (one `H_mat` matrix) | 602 µs | | 613 µs | 609 µs |
| | `request_point` | a recipient point | 598 µs | | 610 µs | 626 µs |
| | `eval` | `TagEval` with its error | 9.22 µs | | 9.4 µs | 9.5 µs |
| | `keygen` | `TagKeyGen` | 0.96 µs | | 0.98 µs | 0.99 µs |
| `lattice-pcreds` | `setup` | `Setup` | 3.02 ms | 3.0 ms | 4.7 ms | 3.11 ms |
| | `register` | `Register` | 10.4 µs | 10.4 µs | 10.6 µs | 10.8 µs |
| | `request_attestation` | `π_id` | 1.10 s | 0.93 s | 1.15 s | 1.16 s |
| | `receive_attestation_request` | its check | 214 ms | 168 ms | 224 ms | 227 ms |
| | `attest` | `π_att` | 6.81 s (6.39-7.23) | 3.42 s | 17.9 s | 6.20 s |
| | `check_attestation` | its check | 3.50 s | 1.81 s | 10.1 s | 3.19 s |
| | `request_credential` at `k = 1, 3, 5` | `PrepareIssue` and `π_iss` | 2.02, 2.06, 2.07 s (±5-6 %) | 1.30, 1.30, 1.28 s | 5.95, 6.05, 6.21 s | 1.83, 1.89, 1.85 s |
| | `evaluate_request` at `k = 5` | `π_iss` and the five attestations | 18.0 s | 4.09 s (3.87-4.35) | 51.7 s | 15.8 s |
| | `respond` | `BlindIssue` and the record | 948 µs | 1.36 ms (1.17-1.53) | 1.09 ms | 1.45 ms |
| | `unblind` | `Unblind` | 147 µs | 146 µs | 388 µs | 126 µs |
| | `prove` | `π_prove` | 5.08 s (4.81-5.36) | 2.30 s | 18.7 s | 4.87 s |
| | `verify` | its check | 2.98 s | 1.50 s | 9.92 s | 2.51 s |

* The three components of `x_0` are 48 binary rows of the Ajtai part at proof degree 128, against
  32 for two (Stage 1) and 208 for thirteen, in `R_att`, `R_iss` and `R_Possess`; the lower bound
  on `‖s‖²` adds one row to `R_att` and `R_Possess`. Against Stage 1, the proofs that carry `x_0`
  take 4 % (`π_prove`) to 19 % (its check) more time at one thread; against `ℓ_r = 13`, 2.6
  (`π_att`) to 3.7 (`π_prove`) times less. `π_id`, whose statement did not change, keeps its time
  (1.10 s, against 1.15 and 1.16 s), and so do the functions outside Jali, but for `PrepareIssue`
  and `Verify` (and `Unblind`, one `Verify`), whose products grew from 3 and 4 to 4 and 5.
* `evaluate_request` at `k = 5` is the verification of `π_iss` and of the five attestations;
  with `parallel` the five run at once, in one batch, and Jali's own parallelism runs inside each.
* `request_credential` does not depend on `k` beyond the noise: `π_iss` proves `R_iss` alone, and
  the attestations enter only its context (a SHA-256 transcript).
* Since these runs the identifier point is the helper key's, `x_0 = H_id(⟨hvk⟩)` (the paper's
  protocol box), not a constant of the deployment. `setup` no longer derives `x_0` and its rows;
  `register` and the statements at `x_0` (`π_id`, `π_iss`) derive its matrix when they use it, one
  `H_mat` matrix (about 0.6 ms) plus the rows for a statement, and the rule `x_Q ≠ x_0` of a
  recipient point compares two matrices (about 1.2 ms). The functions of the table but `register`
  and `setup` change by well under 1 %; `register` grows by about one matrix. Not re-measured.
* `respond` runs on a freshly restored helper right after the evaluation of a root request, in
  about a millisecond; `blind_issue` (245 µs) runs the same algorithm on one key in a loop. The
  difference, cold caches and the record, was not investigated.
* The `quick_end_to_end_k1` test, one operation at a time (in both parts of the heavy run),
  printed 7.01-7.03 s for `π_att`, 3.49-3.50 s for its check, 2.42-2.43 s for `π_iss`, 6.44-6.48 s
  for `π_prove` and 2.97-2.99 s for its check. The heavy runs that contain it peaked at 0.73 GB
  and the one-thread benchmark at 0.71 GB with its `k = 5` fixture: a proof or verification of
  `R_att` or `R_Possess` holds up to about 0.7 GB, against about 1.7 GB with thirteen components
  and 0.54-0.64 GB in Stage 1.

Sizes printed by the runs (bytes, the benchmark's fixture, seed `0x7063_0002`): `hvk` 2560, the
helper's stored key 8489, a stored user 624, `id` 336, an attestation request 28,485, an
attestation 87,772, `π` at `k = 5` 485,881 (486,221 on the wire), `σ` 6144, a membership proof
82,340; identical in runs 1 and 2: Jali's output does not depend on the number of threads. The
seeded tests measured 28,477-28,478, 87,785-87,844, 485,954 (486,294 on the wire) and
82,355-82,356 for the same objects (`quick_end_to_end_k1` and `tests/lattice_sizes.rs`,
2026-10-18); every honest proof measured has 0.959 to 0.970 times the estimate of its parameter
set. With 13 components an attestation measured 136,154 bytes, a request at `k = 5` 776,785 and
a membership proof 130,659; in Stage 1, 83,491, 458,219 and 76,112.

The timing probe of `tests/lattice_tag.rs` gives the backend's own work outside Jali: `H_mat`
0.61 ms (of which SHAKE128 0.35 ms), `TagEval` with its error 8.9 µs, `TagKeyGen` 0.98 µs
(2026-10-18, release).

### The extractable build

Measured on 2026-11-15 (UTC) on the same Apple M4, rustc 1.100.0, with Jali 0.1.1, in both
builds of the working tree on commit `485d5b9`.

**Sizes.** One run of `tests/lattice_sizes.rs` per build (its fixture seed): an attestation
request 28,481 and 167,109 bytes, attestations 87,789-87,813 and 496,161-496,249, `π` at `k = 5`
485,889 and 2,803,886 (486,229 and 2,804,226 on the wire), a membership proof 82,354 and
463,551, for the plain and the extractable build. The plain figures lie in the ranges of
2026-10-18. Every extractable proof measured has about 0.98 times the estimate of its build
(`lattice::sets`).

**Cost, by retired instructions.** Criterion's wall-clock means were not usable that day: at a
load average of 6 to 8 (against 3.5 to 4.0 on 2026-10-18) the plain build's `attest` came out at
14.05 s, twice its documented time, and the extractable build's at 11.18 s, below the plain one
although it does strictly more work (saved as the baselines `sl-plain` and `sl-extractable`, not
used). Instead a probe ran the protocol up to stage `S` in one process per stage (setup, a root
user's request and its evaluation, a newcomer's attestation request and its check, an
attestation and its check, a membership proof and its check, at one thread), so that the
retired instructions of consecutive stages (`/usr/bin/time -l`) differ by one operation, for
seeds 1 to 3 in both builds. Retired instructions hardly depend on the load. In billions:

| operation | plain build, seeds 1, 2, 3 | extractable build, seeds 1, 2, 3 | ratio of the means |
|---|---|---|---|
| `π_iss` (`request_credential`) | 45.00, 45.76, 44.74 | 81.72, 58.10, 45.74 | 1.37 |
| its check (`evaluate_request`, no attestations) | 10.71, 10.31, 11.16 | 11.72, 10.95, 11.33 | 1.06 |
| `π_id` (`request_attestation`, with `respond`, `unblind` and a `register`) | 28.54, 26.31, 30.94 | 29.02, 51.96, 28.01 | 1.27 |
| its check (`receive_attestation_request`) | 3.96, 5.88, 4.42 | 3.50, 6.24, 3.94 | 0.96 |
| `π_att` (`attest`) | 147.22, 195.30, 159.53 | 256.55, 141.13, 139.67 | 1.07 |
| its check (`check_attestation`) | 75.86, 76.91, 76.15 | 76.13, 75.15, 73.55 | 0.98 |
| `π_prove` (`prove`) | 174.62, 111.55, 111.93 | 114.85, 104.28, 187.66 | 1.02 |
| its check (`verify`) | 66.38, 63.86, 62.55 | 66.19, 67.81, 66.51 | 1.04 |
| the whole run | 530.0 (mean) | 570.7 (mean) | 1.08 |

* A prover restarts a random number of times, and the extractable build adds the LinHC
  commitment's own rejection test, so single proofs differ by up to 1.8 times between seeds in
  either build. Three seeds give the provers' ratios only roughly. A proof without restarts,
  `π_iss` at seed 3, costs about 1.0 billion instructions more in the extractable build.
* One stage's count varies between runs of one binary by up to about 3 % under that load (five
  runs of stage 2 at seed 1 of the probe and of `examples/lattice_costs.rs`: 55.9 to 57.8
  billion), so a difference of two stages carries an error of a few billion instructions, as
  large as the cheap checks themselves. The verifiers' ratios lie within 6 % of 1, inside that
  error and the variation between proofs, so this run does not resolve the cost of checking the
  LinHC part. It is small against the plain verification at these sizes.
* Peak RSS over the runs: 0.65 GB in the plain build and 0.73 GB in the extractable one.
* The probe is `examples/lattice_costs.rs`, whose documentation gives the commands. Each build
  was compiled once and every stage run for seeds 1, 2 and 3 in turn.

### The CFRG transcripts (Jali 0.2.0 and Sigma -04)

Measured on 2026-11-15 (UTC) on the same Apple M4, rustc 1.100.0, one thread, release builds:
commit `8c72aa0` (Jali 0.1.1, SHA-256 `H_1`) against the working tree of the change (Jali 0.2.0
on the transcript of `draft-irtf-cfrg-fiat-shamir-04`, the pairing proofs of
`draft-irtf-cfrg-sigma-protocols-04`). A probe outside the repository ran `Π_PCreds` at `k = 1`
once per seed in one process, reading each operation's retired instructions with
`proc_pid_rusage`, the two versions alternating seed by seed (load average 4 to 8, so the
retired instructions are the figures to compare). Ratios are after over before, of the means.

**Lattice instantiation**, seeds 1 to 3, retired instructions in billions:

| operation | plain build, before | after | ratio | extractable build, before | after | ratio |
|---|---|---|---|---|---|---|
| `π_iss` (`request_credential`) | 46.66 | 46.02 | 0.99 | 46.12 | 44.17 | 0.96 |
| its check (`evaluate_request`) | 10.68 | 7.63 | 0.71 | 11.37 | 8.43 | 0.74 |
| `π_id` (`request_attestation`) | 28.87 | 25.95 | 0.90 | 33.56 | 27.71 | 0.83 |
| its check (`receive_attestation_request`) | 3.71 | 2.82 | 0.76 | 4.11 | 3.21 | 0.78 |
| `π_att` (`attest`) | 167.57 | 132.75 | 0.79 | 159.48 | 146.41 | 0.92 |
| its check (`check_attestation`) | 73.99 | 68.23 | 0.92 | 75.43 | 69.80 | 0.93 |
| `π_prove` (`prove`) | 108.33 | 106.28 | 0.98 | 132.22 | 120.25 | 0.91 |
| its check (`verify`) | 63.93 | 58.72 | 0.92 | 65.21 | 59.84 | 0.92 |
| the whole run | 503.9 | 448.5 | 0.89 | 527.6 | 480.0 | 0.91 |

The checks are deterministic for a given proof, so their ratios are the reliable ones. The
provers restart a random number of times, which three seeds do not average out. Every proof
grew by its fixed-width fields: a request at `k = 1` from 47,204-47,219 to 49,060 bytes and from
323,167-323,196 to 329,012 in the extractable build, an attestation request from 28,459-28,479
to 29,452 and 167,086-167,129 to 170,316, an attestation from 87,785-87,808 to 90,508 and
496,186-496,218 to 504,620, a membership proof from 82,316-82,350 to 84,860 and 463,515-463,551
to 471,404. Every proof of a set now has the same length. At `k = 5` (`tests/lattice_sizes.rs`,
run with the heavy suites, which pass in both builds, 64 tests each) a credential request is
501,596 bytes on the wire (486,229 before) and 2,852,108 in the extractable build (2,804,226).

**Pairing instantiations**, seeds 1 to 10 at BLS12-381: the whole run took 0.991 to 1.002 times
the retired instructions for the four base and tag pairs (PS and BBS with `Tag_DDH` and
`Tag_DY`), every operation within 2 % except the check of a Σ-BBS request
(`evaluate_request`), at 1.12 to 1.13 times. The instance of Sigma -04 lists every element of
an equation, so the image of the issuance proof is `(C, 1), (h_0, −1)`, and the verifier scales
both elements by the challenge, one more scalar multiplication in `G_1` than before. The message
sizes are unchanged.
