# Testing and Benchmarks

What the test suites cover, the checks a change has to pass, and the benchmarks.

## Test suites

Test helpers: the generic conformance flows (`cred::conformance`) and an
INSECURE hash-to-group oracle for curves without a hash-to-curve suite (`hash::testing`)
are compiled for the crate's own tests and behind the non-default cargo feature `test-utils`.
The crate lists itself as a dev-dependency with that feature, so `cargo test` enables it for
unit and integration tests alike; a normal build never contains them. The flows walk through
the way the construction box consumes a base and a tag (root signing, `Attest` / `VerifyAtt`,
`Prove` / `VerifyProof`, `Issue`, `Unblind`, `VerifyCred`, chaining), with negatives that each
hinge on one mechanism. `tests/credential_bases.rs` runs them for every compatible pair:
`Σ-PS`, `Σ-BBS` and `Σ-MAC` with `Tag_DDH` and with `Tag_DY`, `Σ-EQ` with `Tag_DDH`, each over
BLS12-381 and over BN254 (the latter with the insecure oracle where an oracle is needed), plus
the refusal of `Σ-EQ` with `Tag_DY`.

`tests/pcs_correctness.rs` runs the construction itself through its public API: Def.
"Correctness" with root issuance and chaining for every compatible pair and `k ∈ {1, 2, 5}`
(plus a run over BN254), the byte sizes of the comparison table, proof-gated issuance, and
negatives that each hinge on one verifier-side check (where the honest `prove` refuses to build
the offending proof, a cheating prover builds it from the public relation and context builders).
`tests/pcs_review_regressions.rs` holds the regression tests of a hostile review of the
construction: objects with group elements OUTSIDE the prime-order subgroup (rejected by every
decoder at every position, and by every verifier when they are built in memory), the root path
for threshold predicates, and what a helper key under two deployment labels does and does not
allow.

Three further suites were written independently of the construction's author, against its
public API only, for every compatible pair:

* `tests/pcs_soundness.rs`: the special-soundness extractor, run by rewinding the interactive
  protocol on exactly the relations `R_att` and `R_issue` that the proofs use (the extracted
  `usk` is the attester's, reproduces the tag, and `VerifyCred` accepts the credential for it;
  for `Σ-BBS` the signature is rebuilt from the extracted randomizers); simulated transcripts
  verify interactively but are rejected as Fiat-Shamir proofs; structural checks of what an
  attestation reveals; and Def. "Proof-gated issuance" exhaustively (every field of a valid proof
  mutated in turn, the number of mutants pinned). These are algebraic and structural evidence on
  seeded samples; they do not and cannot test computational indistinguishability or the
  reductions.
* `tests/pcs_adversarial.rs`: each known attack mounted against the real code and required to
  fail with the expected error: credential-free degenerate shows, the `Σ-EQ` key-reuse and
  forged-key-vector attacks, self-attestation and its disguises, a proof for a foreign context,
  the weak Fiat-Shamir attack (tag or shown credential chosen after the challenge), wrong
  attestation counts and threshold confusion, replay between the root path and the ordinary
  path, duplicate attesters, attestations grafted from another identifier, replay across
  deployments and helpers, policy violations, a malicious helper's pre-credentials, malformed
  helper keys, the undefined point of `Tag_DY`, and byte fuzzing of every encoding (no panics).
* `tests/serialization.rs`: round trips of every public type in both encodings, the byte sizes
  of the comparison table with their decomposition, rejection of trailing bytes, non-canonical
  scalars, points outside the prime-order subgroup and uncompressed encodings, and a pinned
  digest of the public parameters.

And per layer:

* `tests/sigma_protocol.rs`: the sigma layer on relations over `G_1`, `G_2`, `G_T` and mixtures
  of them: completeness, simulated transcripts, special soundness with shared variables, and the
  Fiat-Shamir transform.
* `tests/serde_json.rs` (`serde` feature): a join that travels as JSON end to end for every
  pair, strict decoding, and the JSON forms of secrets.
* `tests/bbs_ietf_interop.rs`: `Σ-BBS` under IETF parameters against the pinned dev-dependency
  `affinidi-bbs` 0.3.3, in both directions (see [Encodings](./encodings.md)).

The lattice instantiation (feature `lattice`; `cargo test` compiles it through the dev
self-dependency):

* Unit tests of the shared foundations (`lattice`: constants against `ntru-trapdoor` and
  lem:tag-lwr-short, ring types and their canonical encodings, the empty encoding and the
  documented panics of wiped values, the SHAKE128 framing with known answers that independent
  Python references reproduce, the pinned Jali parameter sets and the proof bounds at twice their
  estimates), of `cred::vsis` (every algorithm of the `Σ-vSIS` box with ONE real NTRU trapdoor,
  the exact norm bound, the exact check of every preimage before release (a vector one unit off,
  another target and a long vector of the same coset are refused), `Sign ≡ Unblind ∘
  BlindIssue`, the issuance cap, the count stored ahead of issuance, strict codecs), of
  `kiprf::lwr` and `lattice::oracles` (TagEval against the validation harness and a
  rational-arithmetic reference, rounding boundaries, known answers of `H_mat`, `c_0`,
  `EncPred`), and of `pcs::lattice` (the statements compile against their parameter sets with
  the blocks they were derived for; Jali's witness map accepts the honest witnesses and refuses
  the false witnesses of the harness, another key, a shifted tag with its error outside the exact
  bound, `x_1`, `usk` or `x_0` with a coefficient 2 with a real preimage for that message,
  `‖s‖² = ⌊β_s²⌋ + 1`; the credential-free `φ` forgery satisfies the relation and its `φ` is not
  binary; `T + p` has the witnesses of `T`; the digest of `pp` and the three contexts with known
  answers reproduced by Python; the fixed-format codec; the proof bounds of attestations,
  issuance proofs and root requests in the encoders, `check` and the decoders; `hsk` stored
  ahead of issuance; constant-time credential equality over both parts).
* `tests/lattice_vsis.rs`, `tests/lattice_tag.rs`: the base and the tag through the public API,
  and the tag clauses against Jali's own witness map.
* `tests/lattice_pcs.rs`: `LatticePCS` with one helper key: the `k = 1` flow
  (`quick_end_to_end_k1`, release builds only), the harness's main flow at `k = 3` with chaining
  and the sizes at `k = 5` (both `#[ignore]`), and the checks that need no proof (among them the
  proof bounds: oversized proofs are refused before any Jali work, in milliseconds).
* `tests/lattice_adversarial.rs`: attacks on a shared fixture (`#[ignore]`): tampered
  attestations (tag, `φ`, recipient, helper key, deployment, proof bytes), tampered issuance
  proofs (counts, duplicates, self-exclusion, `C`, `T_0`, `f`, replays between the root path and
  the ordinary path), what the honest prover refuses (policy, duplicate, a foreign attestation,
  self-attestation), a helper key at the issuance cap; and byte fuzzing of every decoder.
* `tests/lattice_flows.rs`: the main flow of the validation harness (`main_flow` of
  `pcs-128-v2/setR/harness/src/flow.rs`) at `k = 3` and `k = 5` with one helper key, every one of
  its 56 and 62 checks an assertion, and 27 more (controls, the PCS-API form of a check, wire round
  trips of every object) (`#[ignore]`). The false-witness checks run Jali's witness check on an
  independent port of the harness's statements, with real preimages under the helper key.
* `tests/lattice_attacks.rs`: a cheating prover (the same port, proving with Jali directly under
  any context) against the verifiers: the `φ` forgery, non-canonical tags, duplicate attesters, a
  self attester, the wrong `k`, wrong contexts and labels, replays and mixes (and the two replays
  that are accepted by design), the issuance cap with two units left, tampered credentials
  (`#[ignore]`); and two light tests without proofs (a non-canonical `C` or `h`, tampered
  credentials). A control shows that the port's honest proofs are accepted by `LatticePCS` and
  yield real credentials.
* `tests/lattice_sizes.rs`: the README row: the two seeded runs it was measured from, reproduced
  exactly; seeded proofs reproduced byte for byte; the spread of the sizes over ten more seeds
  (`#[ignore]`).
* `tests/lattice_parallel.rs`: the `k` attestation verifications of `CheckAtts_P`, which run in
  parallel with the feature `parallel`, at `k = 3`: a valid request accepted (`VerifyProof`,
  `Issue`, `Unblind`, `VerifyCred`, and a verifier whose policy is a closure over an `Rc`, which
  is not `Sync`), and exactly one invalid attestation (made for another recipient, or with a
  proof byte flipped) at the first, the middle and the last position, refused with
  `InvalidAttestation` by `Prove` and, after a valid `π_0` from the cheating prover, by
  `VerifyProof`. With `parallel`, every `VerifyProof` verdict is also computed in rayon pools of
  1, 2 and 3 threads, where the verifications run in batches of 1, of 2 then 1, and of 3. The
  same verdicts in both builds (`#[ignore]`; run it with and without `parallel`); a light test
  shows that a policy that is not `Sync` still gives a verifier.
* `tests/lattice_support/mod.rs`: the code the heavy suites share (deployments, the check log,
  the port, the helper's trapdoor for real preimages, wire round trips).

An attestation is a Jali proof of seconds and about 0.5 GiB, so the heavy tests run in release,
one at a time:

```text
cargo test --release --features lattice --test lattice_pcs
RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_pcs --test lattice_adversarial -- --ignored --nocapture
RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_flows --test lattice_attacks -- --ignored --nocapture
RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_sizes -- --ignored --nocapture
cargo test --release --features lattice --lib -- --ignored --nocapture pcs::lattice   # relation-level proofs, timing probe
RUST_TEST_THREADS=1 cargo test --release --features lattice --test lattice_parallel -- --ignored --nocapture
RUST_TEST_THREADS=1 cargo test --release --features lattice,parallel --test lattice_parallel -- --ignored --nocapture
```

Every suite also runs with `--features lattice,parallel`. A heavy test then uses every core and
holds up to `k` attestation verifications at once, so keep `RUST_TEST_THREADS=1` there too.

Every lattice suite with its ignored tests, one after the other, took 36 minutes on an Apple M4
(2026-10-04: `lattice_sizes` 17 minutes, `lattice_flows` 8, `lattice_attacks` 5.4,
`lattice_pcs` 3.3, `lattice_adversarial` 2.1, the unit tests of the lattice modules 0.7), and no
process exceeded 0.77 GB. With `--features lattice,parallel` they took 21 minutes (2026-10-04,
12:23-12:45: `lattice_sizes` 7.9 minutes, `lattice_flows` 4.0, `lattice_parallel` 3.3,
`lattice_attacks` 2.8, `lattice_pcs` 1.6, `lattice_adversarial` 1.1, the unit tests 0.5; an
earlier run took 29 minutes while another job kept one to four cores busy), and `lattice_pcs`,
`lattice_flows` and `lattice_sizes` peaked at 2.5-2.7 GB (2.1-2.7 GB over both runs), since the
attestations of a `k = 5` request are verified at once.

All randomness in tests and benchmarks is seeded. The tests are evidence on sampled instances:
they check algebraic and structural facts, not computational indistinguishability and not the
reductions of the paper.

## Gates and benchmarks

```text
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all-targets
cargo test --doc
RUSTDOCFLAGS='-D warnings' cargo doc --no-deps

cargo bench --bench kiprf                # Tag_DDH, Tag_DY
cargo bench --bench cred                 # Σ-PS, Σ-BBS, Σ-EQ, Σ-MAC
cargo bench --bench pcs                  # the construction, every public base/tag pair at k = 5
cargo bench --bench lattice --features lattice   # Σ-vSIS, Tag_LWR, LatticePCS at k = 1, 3, 5
cargo bench --bench cred -- sigma-bbs    # one group (the filter is a regex)
cargo bench --bench cred -- --test       # only the size tables (every benchmark runs once)
```

Benchmarks (criterion, seeded inputs, BLS12-381). Each one first prints the SIZES of the objects
it handles, then measures the running times:

* `benches/kiprf.rs`, the key-injective PRFs: `TagKeyGen`, `TagEval` at an ordinary point and
  at the identity point `c_0`, `ValidTag`, the stand-alone proof for `R_Tag` and its verifier,
  and `H_2` alone (the hash to the curve that `Tag_DDH` pays per point and `Tag_DY` does not).
  Sizes: `pp_Tag`, key, tag, tag proof.
* `benches/cred.rs`, the credential bases: `Setup`, `KeyGen`, the key range check, `Sign`,
  `Verify`, `Com`, `BlindIssue`, `Unblind`, `ReRand`, the public checks of `VerifyPossess`, the
  possession proof and its verifier, for `Σ-PS`, `Σ-BBS`, `Σ-EQ` and the designated-verifier
  `Σ-MAC` (over `G_1` of BLS12-381, whereas the paper measures it over ristretto255). Sizes:
  parameters, keys, credential, `m_aux`, issuance encoding and state, pre-credential, shown
  credential, possession proof.
* `benches/pcs.rs`, the construction: `Attest`, `VerifyAtt`, `Prove`, `VerifyProof`, `Issue`,
  `Unblind` and `VerifyCred`. `Prove` and `VerifyProof` include `CheckAtts_P`, i.e. `k`
  attestation verifications; the paper's "prove" figure (the `k` attestations together with the
  subject's proof) corresponds to `k · attest + prove`. Sizes: `pp`, `hvk`, root request,
  pre-credential, credential, `att` and `π` (the last two are the comparison table's figures).
* `benches/lattice.rs` (feature `lattice`), the post-quantum instantiation: the algorithms of
  `Σ-vSIS` (`Setup`, `KeyGen`, `Com`, `Sign`, `BlindIssue`, `Verify`, `Unblind`, decoding the
  signing key), of `Tag_LWR` (`H_0`, `TagEval`, `EncPred`, `TagKeyGen`) and of `LatticePCS`
  with one helper key (`HKeyGen`, `UKeyGen`, `Attest`, `VerifyAtt`, `Prove` at `k = 1, 3, 5`,
  `VerifyProof` and `Issue` at `k = 5`, `Unblind`, `VerifyCred`, the root path). The
  construction's group takes 10 samples of one iteration (about 16 minutes at one thread) and
  runs under `cargo bench` only. Sizes: every object at `k = 5`, and `π` at `k = 1` and `k = 3`.

Measured on an Apple M4 (10 cores, 16 GiB), macOS 27.0.1, rustc 1.99.0, commit 6b7c39a plus the
uncommitted lattice integration (2026-10-04, 05:53-06:20), load average 1.7-3.1 during the
one-thread run (the benchmark itself included) and 2.9-6.6 during the `parallel` run. The figures
are criterion's estimates: the mean of 10 samples of one iteration for `lattice-pcs`, of 20
samples for the other groups; one thread unless noted. `parallel` is `--features
lattice,parallel` on all 10 cores: "Jali only" is that run, before the attestation verifications
of `CheckAtts_P` ran in parallel, and the last column the algorithms that verify attestations
with them in parallel (2026-10-04, 10:50-11:52, the mean of three runs; see below):

| group | algorithm | one thread | `parallel`, Jali only | `parallel` |
|---|---|---|---|---|
| `lattice-vsis` | `Setup` | 54.7 µs | | |
| | `KeyGen` (`TrapGen`) | 5.81 ms | | |
| | `Com` | 65.8 µs | | |
| | `Sign` (with the exact check of the preimage) | 330 µs | | |
| | `BlindIssue` (with the exact check of the preimage) | 263 µs | | |
| | `Verify` | 139 µs | | |
| | `Unblind` | 140 µs | | |
| | decoding the signing key (with `h = g f^{-1}`) | 217 µs | | |
| `lattice-lwr` | `H_0` (one 168 × 1024 matrix) | 599 µs | | |
| | `TagEval` with its error | 9.2 µs | | |
| | `EncPred` | 0.78 µs | | |
| | `TagKeyGen` | 0.96 µs | | |
| `lattice-pcs` | `HKeyGen` | 5.93 ms | 5.93 ms | |
| | `UKeyGen` | 10.2 µs | 10.1 µs | |
| | `Attest` | 5.89 s (median 5.47 s) | 2.98 s | |
| | `VerifyAtt` | 2.97 s | 1.53 s | 1.64 s |
| | `Prove`, `k = 1` | 5.83 s | 3.57 s | 3.79 s |
| | `Prove`, `k = 3` | 11.5 s | 6.62 s | 4.70 s |
| | `Prove`, `k = 5` | 17.5 s | 9.63 s | 5.78 s |
| | `VerifyProof`, `k = 5` | 15.4 s | 8.07 s | 3.98 s |
| | `Issue`, `k = 5` (the helper: `VerifyProof`, then `BlindIssue`) | 15.4 s | 8.08 s | 3.94 s |
| | `Unblind` | 144 µs | 143 µs | |
| | `VerifyCred` | 142 µs | 142 µs | |
| | root request | 2.83 s | 2.05 s | |
| | verification of a root request | 625 ms | 423 ms | |
| | `issue_root` | 627 ms | 420 ms | |

`Prove` grows by one attestation verification per attester: about `2.9 k + 2.9` s at one thread.
`Attest` varies the most (95 % interval 5.44-6.50 s), because Jali's prover restarts its
rejection sampling a random number of times. The exact check of every preimage costs about
15 µs per `SampPre` call (`Sign` 316 µs and `BlindIssue` 247 µs before it, in an earlier run
under a load average of about 3.3), and decoding the signing key 85 µs more for `h`. That
earlier run measured the other multi-second algorithms 3-6 % slower, under more load, and the
root request 2 % faster. The one-thread run took 1085 s in all and peaked at 0.63 GiB; the
`parallel` run of `lattice-pcs` took 539 s.

The last column (`cargo bench --bench lattice --features lattice,parallel --
'lattice-pcs/(verify_att|prove|verify_proof|issue/)'`) verifies the attestations of
`CheckAtts_P` in parallel. It is the mean of the 30 samples of three runs (10:50-11:52; 20
samples for `VerifyAtt` and `Prove` at `k = 1`, whose first run was hit by a burst of other
processes and is left out). The run means were 3.80-4.13 s for `VerifyProof`, 3.77-4.17 s for
`Issue`, 5.57-6.01 s for `Prove` at `k = 5` and 4.36-4.88 s at `k = 3`; an earlier run
(09:23-09:28) measured 3.77, 3.82, 5.55 and 4.52 s. One call's time varies more than before:
`VerifyProof` took 3.55-4.49 s over the 30 samples, against 8.41-8.54 s with Jali's parallelism
alone. The machine was slower than when the "Jali only" column was measured (06:12): that
column's executable, run again right before the third run (11:39-11:47), took 3-6 % longer. That
side-by-side comparison measures the change: `VerifyProof` and `Issue` at `k = 5` 2.2 times
faster (8.45 s → 3.80 s, 8.44 s → 3.77 s), `Prove` 1.8 times at `k = 5` (10.19 s → 5.57 s) and
1.6 times at `k = 3` (6.90 s → 4.36 s), and `Prove` at `k = 1` and `VerifyAtt` unchanged (one
attestation and none: nothing to verify in parallel). Without `parallel` nothing changed:
`VerifyProof` at `k = 5` took 15.89 s with the current code and 15.91 s with the code from
before, run one after the other (11:52-12:01; the table's 15.4 s is from 05:53). The sizes
printed are those below, byte for byte.

A call holds up to `min(k, n)` attestation verifications at once on a pool of `n` threads.
`VerifyProof` at `k = 5` under `RAYON_NUM_THREADS=n`, and the peak RSS of the benchmark process
(its `k = 5` fixture included): `n = 2` and `n = 5` 10:56-11:06, `n = 10` the three runs above,
`n = 1` 09:28-09:33 and `n = 3` 10:19-10:28 (with another job on one core):

| `n` | `VerifyProof`, `k = 5` | peak RSS |
|---|---|---|
| 1 | 16.0 s | 0.62 GiB |
| 2 | 8.75 s | 1.12 GiB |
| 3 | 6.79 s | 1.53 GiB |
| 5 | 4.87 s | 2.43 GiB |
| 10 | 3.98 s | 2.38-2.47 GiB |

Against the 15.89 s of one thread without `parallel` in the same session, two threads are 1.8
times faster, five 3.3 times and ten 4.0 times. The sweep of 10:19-10:28 measured `n = 2, 5, 10`
4-9 % slower (9.13 s, 5.33 s, 4.30 s). Each further verification at once adds 0.42-0.50 GiB to
the peak, and the peak varies by up to 0.4 GiB between runs at the same `n`: 1.04-1.12 GiB at
`n = 2`, 1.49-1.53 GiB at `n = 3`, 2.02-2.43 GiB at `n = 5` and 2.29-2.47 GiB at `n = 10`. The
M4 has four performance and six efficiency cores: with more than four busy threads, some of them
run on the slower cores.

Sizes printed by the same run (bytes): `hvk` 2560, `hsk` 8489, `usk` 256, `id` 336, `ĉred`
5376, `cred` 5888, `st_iss` 896, `att` 83,586-83,629, `π` (compact) 127,650 at `k = 1`,
294,837 at `k = 3` and 462,105 at `k = 5`, `π_0` 41,147 at `k = 5`, root requests
44,031-44,059. The proof lengths of both runs are identical: Jali's output does not depend on
the number of threads. Over twelve seeded runs at `k = 5` (`tests/lattice_sizes.rs`, 60
attestations): `att` 83,583-83,652, `π` 462,030-462,151, `π_0` 41,113-41,166, root requests
44,005-44,080; a fixed seed reproduces its proofs byte for byte.

Where the time goes (`timing_probe` in `pcs::lattice::relations`, release, one thread; the run
of the final tree, within 5 % of three earlier runs): `R_att` compiles in 0.29 s, proves in
6.2 s (of which Jali's witness map 0.69 s) and verifies in 2.6 s; `R_issue` compiles in 0.16 s,
proves in 2.5 s (witness map 1.3 s) and verifies in 0.43 s; the PCS's own work (`H_0` 0.6 ms,
the rows of a tag matrix 2-3 ms, a statement 5-10 ms, `Setup` 3.9 ms) is below 1 %. Each Jali
proof or verification of `R_att` holds about 0.5 GiB; the heavy test binaries peak at 0.6-0.8 GB
at one thread, and at up to 2.7 GB with `parallel`.

Timings depend on the machine, the compiler and the enabled features: record them with
`rustc --version` and the commit.
