# Operating a Helper

What the operator of a helper (the issuer of the construction) has to decide and enforce around
the library. The Rust example below is compiled by `cargo test --doc`.

The construction is as strong as the helper's admission decisions. The code enforces what the
protocol box enforces; the following is the helper operator's part. None of it is a statement of
the paper, whose model has one `pp`, one `hvk` and a policy `P` that is given.

* **Serve a closed set of predicates.** `issue(hvk, hsk, f, id, π)` issues under whatever `f` it
  is called with: `f` is the HELPER's input. A requester that may name `f` names its own
  threshold. With a threshold-1 predicate on offer, ONE credentialed user endorses any number of
  fresh keys of its own, and those keys then endorse a newcomer for a threshold-5 community
  (the regression tests run exactly this). Theorem "Predicate soundness" is not violated (a node
  of the tree has as many children as ITS predicate asks for), but the community's threshold
  means nothing. Decide which `(threshold, label)` pairs exist and refuse everything else before
  calling `issue`.
* **Do not run with the default policy.** `SetupParams::new` selects `P ≡ 1` (`AcceptAll`),
  under which an attestation counts whatever label `φ_j` it discloses: root credentials,
  credentials of a threshold-1 predicate, and ANY other credential under `hvk`. Use an allow
  list over the predicates of the deployment whose members may endorse, e.g.

  ```rust
  use ark_bls12_381::{Bls12_381, G1Projective};
  use predicate_credential_system::{
      cred::PS,
      hash::bls12_381::G1Hasher,
      kiprf::DDH,
      pcs::{AllowList, PCS, Predicate, PredicateCredentialSystem, SetupParams},
  };

  type Open = PCS<Bls12_381, PS<Bls12_381>, DDH<G1Projective, G1Hasher>>;
  type Helper = PCS<
      Bls12_381,
      PS<Bls12_381>,
      DDH<G1Projective, G1Hasher>,
      AllowList<ark_bls12_381::Fr>,
  >;

  # fn main() -> Result<(), predicate_credential_system::Error> {
  let pp = Open::setup(SetupParams::new(b"example.org/community".to_vec()))?;
  let f_root = Predicate::root(b"founders".to_vec());
  let f = Predicate::new(2, b"members".to_vec());
  // founders and members may endorse; nobody else, whatever else `hvk` has signed
  let policy = pp.allow_list([&f_root, &f])?;
  let helper = Helper::from_public_parameters(pp.public_parameters().clone(), policy)?;
  assert_eq!(helper.parameters_digest(), pp.parameters_digest());
  # Ok(())
  # }
  ```

  The policy is the verifier's own input and is not part of `pp` or of a proof, so users can
  keep `P ≡ 1`; the helper's policy decides.
* **One helper key per deployment label.** A credential of `Σ-PS` or `Σ-EQ` is a signature under
  `hvk` on `(usk, φ)` and nothing else (`pp_Σ` is empty; `Σ-BBS` differs, its generators are
  derived from the label). If one key pair served two labels, members of one deployment could
  attest in the other with their label `φ` as a bare scalar, and `P ≡ 1` would count them (an
  allow list would not). `helper_keygen` therefore records the digest of its `pp` inside `hsk`,
  and `issue` / `issue_root` return `InvalidKey` under another `pp`. `HelperSecretKey::new` lets
  you bind a key pair to a deployment yourself: bind it to one.
* **`issue_root` sits behind your admission check, and `f_root` is yours.** A root request proves
  that `C`, `id` and `T_0` are under one key which the requester knows. It says nothing about
  whether that key should be admitted: never expose `issue_root` as an endpoint that anybody
  can call, and never take `f_root` from the request (a requester that names its root predicate
  names its admission class, e.g. one that a community's allow list admits).
* **Attestations are standing endorsements and issuance is assumed sequential** (see
  [Limitations](./design-notes.md#limitations)): if one issuance per set of attestations is wanted, record the tag sets you
  have seen per `id`.

## The lattice instantiation (feature `lattice`)

Everything above applies to `LatticePCS` as well (closed set of predicates, an allow list, one
key per deployment label, `issue_root` behind the admission check). The lattice helper has more
to look after:

* **The helper's randomness.** Give `helper_keygen`, `issue` and `issue_root` a CSPRNG seeded
  by the operating system (`rand::rngs::OsRng`), never a seeded or replayed generator.
  `TrapGen` derives the trapdoor from the RNG's output, so a fixed seed makes the trapdoor
  public: whoever knows the seed signs any credential. Every `SampPre` call and every proof draws
  fresh coins from the same RNG, and the paper requires fresh coins in every `SampPre` call
  (building-blocks.tex, "The implemented preimage sampler"). The API documentation's examples
  are seeded only to be reproducible.
* **The issuance cap.** Every `Issue` and `issue_root` calls `SampPre` once, and the paper's
  assumption allows at most `Q_max = 2^48` calls per helper key (construction.tex, "Issuance
  cap"). The signing key counts them and refuses from then on (`Error::IssuanceCapReached`).
  The count travels in the encoding of `hsk` (bytes 5889-5896 of its 8489 bytes, little-endian;
  see [Encodings](./encodings.md)). Never restore an older copy, which would roll the count
  back. Store the key BEFORE issuing: `hsk.to_bytes_reserving(n)` encodes it with its count `n`
  ahead, so that a restart from that copy (after a crash, say) never reuses a unit of the cap;
  store again before `hsk.signing_key().issued()` passes the count stored last. A stored count
  above the true one is safe: the key only reaches the cap earlier.
* **One live instance per stored key.** The count lives in the in-memory key, and two values
  decoded from the same bytes count separately: two processes (or two hosts) that load one
  stored `hsk` can together answer more than `Q_max` calls, and the last one to store wins. Run
  one instance per helper key and let worker threads share it (`&HelperSecretKey` is `Sync`,
  and its counter is atomic).
* **Rotation.** At the cap, run `helper_keygen` again and publish the new `hvk`. Credentials
  under the old key stay valid under that key, but this crate's `verify_attestation` and
  `verify_proof` take ONE `hvk`: holders of old credentials cannot attest for issuance under
  the new key here (the paper's remedy, a `VerifyProofAtt` that accepts each of the helper's
  keys, is not implemented). Rotation also splits the attesters' anonymity sets by key. At
  `2^48` issuances per key, rotation is not expected in practice.
* **Memory and time per request.** Verifying one attestation is a Jali verification of about
  3 s and 0.5 GiB at one thread. `VerifyProof` (and so `Issue`) at threshold `k` verifies `π_0`
  (about 0.6 s) and then the `k` attestations. Without the feature `parallel` it verifies them
  one after the other, with one verification in memory at a time: 15.4 s at `k = 5` on an Apple
  M4. With `parallel` it verifies them in parallel on rayon's thread pool, and Jali's own
  parallelism runs inside each verification on the same pool (rayon's work stealing schedules
  both levels): on the M4's ten cores, `VerifyProof` at `k = 5` took about 4 s (3.8-4.1 s over
  four runs), against 8.1-8.5 s with Jali's parallelism alone. A request then holds up to
  `min(k, n)` verifications at once on a pool of `n` threads; at `k = 5` the benchmark process
  peaked at 0.6 GiB with one thread, 1.0-1.1 GiB with two, 1.5 GiB with three and 2.0-2.5 GiB
  with five or ten. The verdicts are the same either way. Bound the memory of a request with the
  pool: `RAYON_NUM_THREADS=n` sizes the global pool, or build a pool of your own,
  `rayon::ThreadPoolBuilder::new().num_threads(n).build()`, and serve the requests inside it,
  `pool.install(|| helper.issue(&hvk, &hsk, &f, &id, &proof, &mut rng))` (`install` needs a
  `Sync` policy, which the allow lists are; with another policy, size the global pool with
  `RAYON_NUM_THREADS`, or with `ThreadPoolBuilder::build_global` at start-up, before anything
  uses rayon: the first use, by arkworks, Jali or this crate, builds the global pool with the
  defaults, and `build_global` fails from then on). A pool of one thread verifies one
  attestation at a time, as without the feature. Requests served at the same time add up: size
  the worker pool by memory, and verify untrusted requests with a bounded concurrency. The cheap
  public checks (count, distinct tags, self-exclusion, policy, the length of every proof) run
  before any proof is looked at, and a proof longer than twice its parameter set's estimate is
  refused while decoding.
* **Bound the work per requester.** `Issue` is stateless: the same valid request can be sent
  again and costs a full `VerifyProof` each time (and, when it verifies, another unit of the
  cap), and a requester with only a user key can build one valid `π_0` over attestations it
  copied and replay it at no further cost. Rate-limit by `id` (public in every request), and
  remember the verdict per request (keyed, e.g., by a hash of `f`, `id` and the request's
  compact encoding) so that a replay costs a lookup and not a verification (at `k = 5`, 15.4 s
  at one thread, about 4 s with `parallel` on ten cores). With `parallel`, a refused request can
  also cost more CPU time and memory than without it: a verification that has started runs to
  its end even when another one fails, and a batch starts up to `min(k, n)` of them at once, so
  a request whose first attestation is bad can cost `min(k, n)` attestation verifications where
  the sequential loop stops after one. The worst case, a bad attestation last (or a valid
  request), costs `k` verifications either way.
* **Variable time.** Jali, the floating-point arithmetic and rejection loops of `SampPre`, and
  `TrapGen` run in variable time. A requester can trigger `SampPre` on targets it influences;
  keep the helper's timing out of reach of requesters where that matters.
* **Attestations are standing endorsements here too, and issuance is not enforced to be
  sequential.** Jali's proofs are extracted by rewinding, so the paper's Remark "Concurrent
  issuance" applies as for the pairing instantiations; for the lattice instantiation the paper
  states no theorem yet (its `thm:pq-security` is referenced, not stated).

```rust
use predicate_credential_system::{
    LatticePCS,
    cred::VSIS,
    lattice::Q_MAX,
    pcs::{HelperSecretKey, Predicate, PredicateCredentialSystem, SetupParams},
    serialization::WireFormat,
};
use rand::rngs::OsRng;

# fn main() -> Result<(), predicate_credential_system::Error> {
let open = LatticePCS::setup(SetupParams::new(b"example.org/community".to_vec()))?;
let f_root = Predicate::root(b"founders".to_vec());
let f = Predicate::new(2, b"members".to_vec());
let helper = LatticePCS::from_public_parameters(
    open.public_parameters().clone(),
    open.allow_list([&f_root, &f]),
)?;
// the operating system's CSPRNG: the trapdoor is a function of the RNG's output
let mut rng = OsRng;
let (_hvk, hsk) = helper.helper_keygen(&mut rng); // TrapGen, about 6 ms
assert_eq!(hsk.signing_key().remaining(), Q_MAX);
// Before serving the next 1000 requests, store hsk with its count 1000 ahead; store again
// before `hsk.signing_key().issued()` reaches 1000.
let stored = hsk.to_bytes_reserving(1000)?;
assert_eq!(stored.len(), 8489);
let restored = <HelperSecretKey<VSIS> as WireFormat>::from_bytes(&stored)?;
assert_eq!(restored.signing_key().issued(), 1000);
assert_eq!(hsk.signing_key().issued(), 0);
# Ok(())
# }
```
