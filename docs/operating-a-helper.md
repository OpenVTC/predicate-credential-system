# Operating a Helper

What the operator of a helper (the issuer of `Π_PCreds`) has to decide and enforce around the
library. The Rust examples below are compiled and run by `cargo test --doc` (the crate includes
this file as a doctest); they are seeded so that they are reproducible, whereas a deployment draws
its keys and proofs from the operating system's CSPRNG (`rand::rngs::OsRng`).

The code enforces what the protocol box enforces, and a few rules of its own (listed in
[Design notes](./design-notes.md)). The rest is the operator's part. None of it is a statement of
the paper, whose model has one `pp`, one helper key and the policy `Pol_k` as given inputs.

The first part is about the pairing-based helper of `pcreds` (`Helper<Bk, S>`); the lattice
instantiation, which still follows the earlier construction, has its own section at the end.

## The policy

`Policy::threshold(k)` is the threshold policy `Pol_k`: a request is valid iff its attestations
carry at least `k` distinct tags that verify at the requester's recipient point. It is the
HELPER's input, fixed when the helper is created or restored; nothing in a request names a
threshold.

* **`k ≥ 1`.** "The threshold policy `Pol_k` never accepts a first request" (Remark "Root users
  and chaining") only because `k ≥ 1`; with `k = 0` every requester with a valid issuance proof
  would be issued to. `Policy::threshold(0)` is `Error::ZeroThreshold`. Root users are admitted
  by an explicit decision instead (next section).
* **Any number of attestations, and an optional limit.** `Pol_k` accepts a request with `k` or
  more distinct valid tags, whatever number of attestations it carries; duplicates and invalid
  attestations count for nothing. The helper verifies every attestation of a request and the
  requester chooses their number, so a helper may set an operational limit:
  `with_max_attestations(max)` (`max ≥ k`, otherwise `Error::DegenerateInput`) makes
  `evaluate_request` refuse a request with more than `max` attestations before it verifies any
  (`Error::TooManyAttestations`). There is no limit by default; a limit well above `k` bounds
  the work per request without refusing honest requesters that send more than `k`.
* **Bound the work per requester.** `evaluate_request` verifies `π_iss` and every attestation
  (at most `max` if you set a limit), each a pairing-product check (the paper reports 27.1 to
  29.8 ms for the helper's whole check at `k = 5` on one core of an Intel Core Ultra 7 258V at
  2.2 GHz, §7.1, Table "Running time"). The same request can be sent again and costs the same each time, and a
  request for a spent identifier is answered `issued` only after that work. Rate-limit by `id_Q`
  (it is public in every request). If you use `IssuanceStore::contains` to drop requests of spent
  identifiers early, still reply only after `evaluate_request` has checked `π_iss`: every
  attester learns `id_Q`, and an `issued` reply to an unverified request would tell it whether `Q`
  holds a credential. (Implementation note, our reasoning; the paper's helper always checks
  `π_iss` first.)

```rust
use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::DDH,
    pcreds::{Policy, Protocol, pairing::{PS, PairingBackend}},
};

type Bk = PairingBackend<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;

# fn main() -> Result<(), Error> {
// Pol_3: three or more distinct valid tags, among any number of attestations ...
assert_eq!(Policy::threshold(3)?.max_attestations(), None);
// ... unless the helper limits that number: a request with more than 16 attestations is then
// refused before any is verified.
let policy = Policy::threshold(3)?.with_max_attestations(16)?;
assert_eq!((policy.k(), policy.max_attestations()), (3, Some(16)));
assert_eq!(Policy::threshold(0).err(), Some(Error::ZeroThreshold));
assert!(matches!(
    Policy::threshold(3)?.with_max_attestations(2),
    Err(Error::DegenerateInput(_))
));

// Received public parameters are accepted only if Setup derives them from their label.
let pcreds = Protocol::<Bk>::setup(b"example.org/community")?;
let pp = pcreds.public_parameters().clone();
let received = Protocol::<Bk>::from_public_parameters(pp.clone())?;
assert_eq!(received.parameters_digest(), pcreds.parameters_digest());
let mut relabelled = pp;
relabelled.label = b"example.org/another".to_vec(); // the parameters are not that label's
assert!(matches!(
    Protocol::<Bk>::from_public_parameters(relabelled),
    Err(Error::InvalidPublicParameters(_))
));
# Ok(())
# }
```

## Root admission

The threshold policy never accepts a first request, so root users are admitted by the helper's
explicit decision: `respond(.., Decision::Root, ..)` on an ORDINARY credential request, which
issues regardless of the policy value (Remark "Root users and chaining"). The credential has the
ordinary format, and every credential then traces back through attestations to such admissions:
the integrity of the deployment is relative to them.

* **`Decision::Root` sits behind your own admission check** (an invitation, a personhood check,
  a founding member list). Never take the decision from the request, and never expose a code path
  that answers `Decision::Root` to anybody who asks. `evaluate_request` has checked that the
  requester owns `id_Q` (`π_iss`), nothing about whether it should be admitted.
* A root admission is an issuance like any other: it records `id_Q` in `I`, and a second root
  admission (or any later valid request) of the same identifier is answered `Reply::Issued`.

## What the helper learns

From a credential request the helper learns what the paper's Table "What each party learns" lists
for it: the requester's identifier `id_Q`, the tags named in the request, and the policy result,
here `EvaluatedRequest::{id, tags, is_valid}` (and the sub-session `ssid`). `tags()` is `N''`,
the distinct tags of the attestations that verify at `x_Q`; the request itself carries every
attestation, so the helper also sees which of them share a source (the same tag), but, by the
paper's theorem and under its assumptions, not who the sources are, although it issued their
credentials. `σ*` and the proofs are re-randomized and zero knowledge; `Ĉ` hides `usk_Q`.

Keep it that way: do not log the requests together with anything that identifies the attesters,
and do not ask attesters to reveal themselves out of band. An attester attests only for an
identifier whose ownership the requester proved to it (`π_id`, checked by
`receive_attestation_request`), so the helper cannot obtain an attester's tag for `id_Q` and
compare it with the tags of `Q`'s request.

## The issued identifiers `I`

The helper "records its first issuance to an identifier before releasing the response" (Remark
"Concurrency"). `respond` calls `IssuanceStore::record(id_Q)` BEFORE `BlindIssue`: a
test-and-set that returns `Ok(true)` if `id_Q` was absent and is now recorded, `Ok(false)` if it
was recorded before (the reply is then `issued`), and an error if the store cannot answer, in
which case nothing is released (`Error::Storage`). This is the order of the protocol box ("adds
`id_Q` to `I` and replies `(ssid, σ̂)` with `σ̂ ← BlindIssue(sk, Ĉ)`"). Under the pairing bases
`BlindIssue` cannot fail on a request that `evaluate_request` accepted; under the lattice base it
fails only if a bounded sampling loop gives up, which is negligible, and the identifier then
stays in `I`, as in the paper. A lattice key at its issuance cap is refused before anything is
recorded (below). What the code cannot do for you:

* **Make `I` durable.** The default store, `IssuanceRecord`, lives in memory; "at most once per
  identifier" then holds per process only. Either persist it after every `respond` that returned
  `Reply::PreCredential` and BEFORE the reply leaves (`serialization::to_bytes(helper.store())`;
  it is canonically serializable), or implement `IssuanceStore` on durable storage, where
  `record` is ONE atomic insert-if-absent (a unique key, and an insert whose result says whether
  the row was new) that is committed before it returns `Ok(true)`, and fails rather than forget.
  On storage shared by several helper processes this is what keeps two processes from both
  seeing an identifier as new. Never restore an older copy of `I`: every identifier recorded
  after it could be issued to again.
* **Re-deliver a lost reply.** If the reply is lost after the record was written (a crash, a
  dropped connection), the identifier is spent: later requests are answered `issued`, and the
  requester cannot unblind anything without the `σ̂` that matches the `IssuanceState` of its
  first request. The library keeps no copy of `σ̂`. A deployment that wants re-delivery stores
  `σ̂` with the record and sends it again, to a later request for the same identifier whose
  `π_iss` `evaluate_request` has checked; the requester keeps its `IssuanceState` until it holds a
  credential.
* **Restore the helper.** `Helper::to_bytes` is the KEY (`pp digest ‖ hvk ‖ sk`, in a buffer
  that is wiped on drop); the policy and the store are kept separately and handed back to
  `Protocol::restore_helper(bytes, policy, store)`, which accepts the key only for THIS
  deployment, an admissible `hvk` and an `sk` that belongs to it. The key bytes are as secret as
  `sk`.

```rust
use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::DDH,
    pcreds::{Decision, IssuanceRecord, Policy, Protocol, Reply, pairing::{PS, PairingBackend}},
    serialization,
};
use rand::{SeedableRng, rngs::StdRng};

type Bk = PairingBackend<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;

# fn main() -> Result<(), Error> {
let mut rng = StdRng::seed_from_u64(1);
let pcreds = Protocol::<Bk>::setup(b"example.org/community")?;
let mut helper = pcreds.helper_keygen(Policy::threshold(2)?, &mut rng);
let hvk = pcreds.helper_key(helper.key().vk())?;

// A founder sends an ordinary request without attestations.
let founder = pcreds.register(&hvk, &mut rng)?;
let (request, state) =
    pcreds.request_credential(&hvk, &founder, Vec::new(), b"join-1", &mut rng)?;
let evaluated = pcreds.evaluate_request(&helper, &request, b"join-1")?;
// What the helper learns: id_Q, the tags of the valid attestations, the policy result.
assert_eq!(evaluated.id(), founder.id());
assert!(evaluated.tags().is_empty() && !evaluated.is_valid());
// The outcome of YOUR admission check, never a field of the request.
let admitted = true;
let decision = if admitted { Decision::Root } else { Decision::Policy };
let Reply::PreCredential(pre) = pcreds.respond(&mut helper, evaluated, decision, &mut rng)? else {
    unreachable!("a root admission of a new identifier issues");
};
let _credential = pcreds.unblind(&hvk, &founder, &pre, state)?;

// Store the key once and the record after every issuance, before the reply leaves.
let key = helper.to_bytes()?;
let record = serialization::to_bytes(helper.store())?;

// After a restart: the identifier is spent, so the same request is answered `issued`.
let record: IssuanceRecord = serialization::from_bytes(&record)?;
let mut helper = pcreds.restore_helper(&key, Policy::threshold(2)?, record)?;
let evaluated = pcreds.evaluate_request(&helper, &request, b"join-1")?;
assert_eq!(pcreds.respond(&mut helper, evaluated, Decision::Root, &mut rng)?, Reply::Issued);

// The key belongs to its deployment.
let other = Protocol::<Bk>::setup(b"example.org/another")?;
let restored = other.restore_helper(&key, Policy::threshold(2)?, IssuanceRecord::new());
assert_eq!(restored.err(), Some(Error::InvalidKey));
# Ok(())
# }
```

A store on shared storage. Here a mutex stands in for the database; on a database, `record` is
the insert-if-absent described above.

```rust
use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

use ark_bls12_381::{Bls12_381, G1Projective};
use predicate_credential_system::{
    Error,
    hash::bls12_381::G1Hasher,
    kiprf::DDH,
    pcreds::{Decision, IssuanceStore, Policy, Protocol, Reply, pairing::{PS, PairingBackend}},
};
use rand::{SeedableRng, rngs::StdRng};

type Bk = PairingBackend<Bls12_381, PS, DDH<G1Projective, G1Hasher>>;

/// `I` in storage shared by several helper processes.
#[derive(Clone, Default)]
struct SharedStore(Arc<Mutex<BTreeSet<Vec<u8>>>>);

impl IssuanceStore for SharedStore {
    fn contains(&self, id: &[u8]) -> Result<bool, Error> {
        let ids = self.0.lock().map_err(|_| Error::Storage("lock poisoned".into()))?;
        Ok(ids.contains(id))
    }

    fn record(&mut self, id: &[u8]) -> Result<bool, Error> {
        let mut ids = self.0.lock().map_err(|_| Error::Storage("lock poisoned".into()))?;
        // one test-and-set: true iff the identifier was absent
        Ok(ids.insert(id.to_vec()))
    }
}

/// A store that cannot answer.
struct Unavailable;

impl IssuanceStore for Unavailable {
    fn contains(&self, _id: &[u8]) -> Result<bool, Error> {
        Err(Error::Storage("database unreachable".into()))
    }

    fn record(&mut self, _id: &[u8]) -> Result<bool, Error> {
        Err(Error::Storage("database unreachable".into()))
    }
}

# fn main() -> Result<(), Error> {
let mut rng = StdRng::seed_from_u64(2);
let pcreds = Protocol::<Bk>::setup(b"example.org/community")?;
let store = SharedStore::default();
let mut a = pcreds.helper_keygen_with_store(Policy::threshold(1)?, store.clone(), &mut rng);
let key = a.to_bytes()?;
// a second process with the same key and the same store
let mut b = pcreds.restore_helper(&key, Policy::threshold(1)?, store.clone())?;
let hvk = pcreds.helper_key(a.key().vk())?;

// The same request reaches both processes; one issues, the other answers `issued`.
let user = pcreds.register(&hvk, &mut rng)?;
let (request, _state) = pcreds.request_credential(&hvk, &user, Vec::new(), b"join", &mut rng)?;
let at_a = pcreds.evaluate_request(&a, &request, b"join")?;
let at_b = pcreds.evaluate_request(&b, &request, b"join")?;
let reply = pcreds.respond(&mut a, at_a, Decision::Root, &mut rng)?;
assert!(matches!(reply, Reply::PreCredential(_)));
assert_eq!(pcreds.respond(&mut b, at_b, Decision::Root, &mut rng)?, Reply::Issued);
assert!(store.contains(&predicate_credential_system::serialization::to_bytes(user.id())?)?);

// If the store fails, nothing is released.
let mut c = pcreds.restore_helper(&key, Policy::threshold(1)?, Unavailable)?;
let at_c = pcreds.evaluate_request(&c, &request, b"join")?;
let reply = pcreds.respond(&mut c, at_c, Decision::Root, &mut rng);
assert!(matches!(reply, Err(Error::Storage(_))));
# Ok(())
# }
```

Identifiers enter the store as their canonical compressed encoding (`serialization::to_bytes`,
48 bytes for a `G_1` tag).

## One key per deployment

A helper key serves one deployment label. A `Σ-PS` credential is a signature under `hvk` on `usk`
and nothing else (`pp_Σ` of `Σ-PS` is empty), so a key that served two labels would let members
of one deployment attest and prove membership in the other with the same `usk`. (`Σ-BBS` differs:
its generators are derived from the label, and a credential of one deployment does not verify in
another.) The library binds everything it can: `helper_keygen` records the digest of its `pp` in
the helper, `restore_helper` refuses key bytes of another deployment, a `HelperKey` is checked
under one deployment, and every algorithm refuses a helper, a key, a user or an issuance state of
another `pp` (`Error::InvalidKey`, `Error::IdentifierMismatch`, `Error::IssuanceStateMismatch`).
It cannot stop an operator who rewrites the digest in stored key bytes, or who hands one key
pair to `Protocol::helper_from_key_pair` under two deployments: do not. (That constructor exists
for a key pair that exists before `pp`, e.g. the key of a `Σ-BBS` deployment with IETF
parameters, which depend on the key; it checks that `sk` belongs to `hvk` and binds the helper to
the deployment it is called on.)

* **Publish `pp` and `hvk`; users check both once.** `Protocol::from_public_parameters(pp)`
  accepts a received `pp` only if it is what `Setup` derives from its label (well-formed
  parameters are not good enough: generators with a known relation look like any others), and
  `Protocol::helper_key(vk)` checks `hvk ∈ V_pp` once and returns the `HelperKey` that every other
  algorithm takes. A deployment set up with parameters of its own (`Protocol::setup_with_params`,
  e.g. `Σ-BBS` generators derived from the helper's key) is received with
  `Protocol::from_public_parameters_with_params(pp, &expected)`, where the user derived
  `expected` itself.
* **Key rotation** is not part of the protocol: a new key is a new `hvk`, and credentials under
  the old key do not verify under the new one. This crate's verifiers take one `hvk`.

## Sessions and contact names

`ssid` and the contact name `P̃` are the application's. An attester passes to
`receive_attestation_request` the contact name through which the request REACHED it (its own) and
the `ssid` of that exchange, never values taken from the request: `π_id` is bound to
`(ssid, P̃)`, so that a request made for one contact name does not verify at another. The helper
passes the `ssid` of the issuance exchange to `evaluate_request`; `π_iss` is bound to it and to
the exact list of attestations.

## The lattice instantiation (feature `lattice`)

The post-quantum instantiation is a backend of the same protocol
(`pcreds::lattice::LatticeProtocol`, `Σ-vSIS` with the short-key `Tag_LWR` and Jali proofs), so
everything above applies to it unchanged: the policy, root admission, the record `I`, one key per
deployment, sessions and contact names. The lattice helper has more to look after:

* **The helper's randomness.** Give `helper_keygen` and `respond` a CSPRNG seeded by the
  operating system (`rand::rngs::OsRng`), never a seeded or replayed generator. `TrapGen` derives
  the trapdoor from the RNG's output, so a fixed seed makes the trapdoor public: whoever knows the
  seed signs any credential. Every `SampPre` call and every proof draws fresh coins from the same
  RNG, and the paper requires fresh coins in every `SampPre` call (§6.2.3, "The implemented
  preimage sampler"). The API documentation's examples are seeded only to be reproducible.
* **The issuance cap.** Every issuance (`respond` on a valid request or a root admission) calls
  `SampPre` once, and the paper's assumption allows at most `Q_max = 2^48` calls per helper key
  (§6.2.3, "Issuance cap"). The signing key counts them and refuses from then on:
  `respond` returns `Error::IssuanceCapReached`, and records nothing: it asks the key before it
  records (the paper's helper rotates its key at the cap, which this code does not do, so an
  identifier of a refused request can still be issued to by a process whose copy of the key has
  capacity left). The count travels in the encoding of
  the helper's key (`Helper::to_bytes`: `digest ‖ hvk ‖ sk`, the count in the last 8 bytes of
  its 8489, little-endian; see [Encodings](./encodings.md)). Never restore an older copy, which
  would roll the count back. Store the key BEFORE issuing: `helper.to_bytes_reserving(n)` encodes
  it with its count `n` ahead, so that a restart from that copy (after a crash, say) never reuses
  a unit of the cap; store again before the key has answered `n` more requests. A stored count
  above the true one is safe: the key only reaches the cap earlier.
* **One live instance per stored key.** The count lives in the in-memory key, and two values
  restored from the same bytes count separately: two processes (or two hosts) that load one
  stored key can together answer more than `Q_max` calls. Run one process per helper key. Inside
  it, `evaluate_request` takes `&Helper` and can run for several requests at once; `respond` takes
  `&mut Helper` (it updates `I` and the count) and is cheap, so serialize it behind a lock.
* **Rotation.** At the cap, generate a new key and publish the new `hvk`. Credentials under the
  old key stay valid under that key, but `check_attestation` and `evaluate_request` take ONE
  `hvk`: holders of old credentials cannot attest for issuance under the new key here (the
  paper's remedy, accepting attestations under each of the helper's keys, §6.2.3, "Issuance cap",
  is not implemented). Rotation also splits the attesters' anonymity sets by key. At `2^48`
  issuances per key, rotation is not expected in practice.
* **Memory and time per request.** Verifying one attestation is a Jali verification of about
  3.5 s (Apple M4) and up to 0.7 GB at one thread in the plain build (feature `lattice-plain`),
  and about as long and up to 0.75 GB in the default, extractable build. `evaluate_request` verifies `π_iss` and then the
  attestations of the request, each at most once and none of a tag already counted. The requester
  chooses their number, so **set a limit**: `Policy::threshold(k)?.with_max_attestations(m)`
  refuses a request with more than `m` attestations before any proof is verified
  (`Error::TooManyAttestations`); a limit of a few times `k` costs honest requesters nothing.
  Without the feature `parallel` the attestations are verified one after the other, with one
  verification in memory at a time. With `parallel` each round of them is verified on rayon's
  thread pool of the calling thread, in batches no wider than the pool, and Jali's own
  parallelism runs inside each verification on the same pool: a request holds up to
  `min(m, n)` verifications at once on a pool of `n` threads. The verdicts are the same either
  way. Bound the memory of a request with the pool: `RAYON_NUM_THREADS=n` sizes the global pool,
  or build a pool of your own, `rayon::ThreadPoolBuilder::new().num_threads(n).build()`, and
  evaluate the requests inside it, `pool.install(|| pcreds.evaluate_request(&helper, &message,
  &ssid))`. A pool of one thread verifies one attestation at a time. Requests served at the same
  time add up: size the worker pool by memory, and verify untrusted requests with a bounded
  concurrency. The cheap public checks (the number of attestations, the length of every proof)
  run before any proof is looked at, and a proof longer than twice its parameter set's estimate
  is refused while decoding and by every verifier.
* **Bound the work per requester.** `evaluate_request` verifies a request whether or not its
  identifier was issued to, and a valid request can be sent again: rate-limit by `id_Q` (public
  in every request), answer an identifier already in `I` (`helper.store().contains(…)`) before
  you evaluate its request, and remember the verdict per request (keyed, e.g., by a hash of the
  request's compact encoding and its `ssid`) so that a replay costs a lookup and not a
  verification.
* **Message sizes.** An attestation is about 91 KB and a credential request at `k = 5` about
  502 KB in the compact format (`to_compact_bytes`), and about 505 KB and 2.9 MB in the
  extractable build (with Jali 0.2.0 and later, whose proofs have a fixed size per relation). Their JSON
  forms (feature `serde`) are about 1.37 times longer, and base58btc takes time quadratic in
  the length of a string: on an Apple M4, encoding a request of 777 KB (of an earlier parameter
  variant) took 14.3 s and decoding it 12.5 s ([Encodings](./encodings.md#json)), and a request
  of the extractable build is 3.7 times as long as that one. Prefer the compact format, whose
  decoders bound every proof before they read it. The JSON decoders refuse a leaf longer than
  the text of the longest valid one of its role before they decode it, so the cost of parsing
  a message is linear in its length; bound the length of the whole text at your transport.
* **Variable time.** Jali, the floating-point arithmetic and rejection loops of `SampPre`, and
  `TrapGen` run in variable time. A requester can trigger `SampPre` on targets it influences;
  keep the helper's timing out of reach of requesters where that matters.
* **What is not covered.** No theorem of the paper covers this instantiation as implemented yet:
  Jali's proofs are straight-line extractable, as the paper's theorem assumes an online
  simulation-extractable NIZK, but Jali argues this extraction only as an outline in the
  classical random-oracle model (and a helper built with the feature `lattice-plain` proves
  with Fiat-Shamir, whose extraction rewinds), and the assumptions of `Σ-vSIS` are not estimated at
  these parameters ($`k = 1 + \ell_r = 4`$ columns of $`B`$). The extraction of $`s \neq 0`$
  rests on the lower-bound argument of §5.2.3 (the module docs of `pcreds::lattice::base`, "What
  the paper asks of the parameters").

```rust
use predicate_credential_system::{
    lattice::Q_MAX,
    pcreds::{IssuanceRecord, Policy, lattice::LatticeProtocol},
};
use rand::rngs::OsRng;

# fn main() -> Result<(), predicate_credential_system::Error> {
let pcreds = LatticeProtocol::setup(b"example.org/community")?;
// every attestation costs the helper seconds: limit their number per request
let policy = Policy::threshold(2)?.with_max_attestations(8)?;
// the operating system's CSPRNG: the trapdoor is a function of the RNG's output
let mut rng = OsRng;
let helper = pcreds.helper_keygen(policy, &mut rng); // TrapGen, about 6 ms
// Before serving the next 1000 requests, store the key with its count 1000 ahead; store again
// before the key has issued 1000 more credentials.
let stored = helper.to_bytes_reserving(1000)?;
assert_eq!(stored.len(), 8489);
assert_eq!(stored[8481..], 1000u64.to_le_bytes());
let restored = pcreds.restore_helper(&stored, policy, IssuanceRecord::new())?;
assert_eq!(restored.key(), helper.key());
assert!(1000 < Q_MAX);
# Ok(())
# }
```
