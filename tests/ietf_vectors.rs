//! The test vectors of the IETF CFRG drafts that the Fiat-Shamir transform of this crate follows
//! (`kat/ietf/`, see its README for their origin and the hashes of the draft texts):
//!
//! * `draft-irtf-cfrg-fiat-shamir-04`, Appendix C: the SHAKE128 duplex sponge, `DeriveSessionID`
//!   and `DecodeUint` against `hash::duplex_sponge`, and the draft's sumcheck example (its
//!   Appendix B) as a multi-round use of the sponge. The suite-independent codec vectors run
//!   against small reference codecs in this file, except the big-endian field serialization,
//!   which runs against the scalar codec of `sigma::codec`. The 12 TurboSHAKE128 vectors are out
//!   of scope.
//! * `draft-irtf-cfrg-sigma-protocols-04`, Appendix A.3: every vector of the ciphersuite
//!   `sigma-proofs_Shake128_BLS12381`. The instance of each vector is read with
//!   `GroupRelation::from_instance_bytes` and serialized back. Every valid proof is reproduced
//!   byte for byte by the library's prover with the draft's seeded generator (Appendix A.1), in
//!   both flavors, from a `GroupRelation` and from a `PairingRelation` built through the value
//!   builders. Every vector is verified and must give its `Expected` decision, and every
//!   adversarial vector's baseline must be accepted. The compact flavor is the library's
//!   (`fiat_shamir::{prove_compact, verify_compact}`). The batchable flavor, which the protocol
//!   does not use, is assembled here from the library's parts (`commit`, `respond`,
//!   `derive_challenge`, the interactive `verify`) as `ProveBatchable` and `VerifyBatchable` of
//!   §5.4 describe it. The 48 vectors of `sigma-proofs_Shake128_P256` are out of scope.

use std::collections::BTreeMap;

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective};
use ark_ec::PrimeGroup;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalDeserialize;
use predicate_credential_system::{
    hash::duplex_sponge::{DuplexSponge, decode_field, derive_session_id, ns},
    sigma::{
        GroupRelation, LinearRelation, PairingRelation,
        ciphersuite::SIGMA_BLS12381,
        codec::{scalar_from_bytes, scalar_to_bytes},
        commit,
        fiat_shamir::{derive_challenge, prove_compact, verify_compact},
        respond, verify,
    },
};
use rand::{CryptoRng, RngCore, SeedableRng, rngs::StdRng};
use serde_json::Value;

const FS_VECTORS: &str = include_str!("../kat/ietf/fiat-shamir-04.json");
const SIGMA_VECTORS: &str = include_str!("../kat/ietf/sigma-protocols-04.json");

fn vectors(json: &str) -> Vec<Value> {
    let doc: Value = serde_json::from_str(json).unwrap();
    doc["vectors"].as_array().unwrap().clone()
}

fn field<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key]
        .as_str()
        .unwrap_or_else(|| panic!("{}: no {key}", v["Id"]))
}

/// Hexadecimal to bytes. The extractor writes the empty string as `""`.
fn bytes(s: &str) -> Vec<u8> {
    if s == "\"\"" {
        return Vec::new();
    }
    assert!(s.len().is_multiple_of(2), "odd hexadecimal {s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// ---------------------------------------------------------------------------------------------
// A small reference arithmetic for moduli below 2^256 (the codec vectors use P-256's order and
// 2^256 − 189, for which this crate has no field type)
// ---------------------------------------------------------------------------------------------

/// A non-negative integer below `2^320`, little-endian limbs.
type Big = [u64; 5];

/// An integer written in decimal (below `2^64`) or with the prefix `0x`.
fn big(s: &str) -> Big {
    let mut out = [0u64; 5];
    match s.strip_prefix("0x") {
        Some(h) => {
            let padded = format!("{h:0>80}");
            for (i, limb) in out.iter_mut().enumerate() {
                let at = 80 - 16 * (i + 1);
                *limb = u64::from_str_radix(&padded[at..at + 16], 16).unwrap();
            }
        }
        None => out[0] = s.parse().unwrap(),
    }
    out
}

fn ge(a: &Big, b: &Big) -> bool {
    for i in (0..5).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

fn sub(a: &mut Big, b: &Big) {
    let mut borrow = 0u64;
    for i in 0..5 {
        let (d, o1) = a[i].overflowing_sub(b[i]);
        let (d, o2) = d.overflowing_sub(borrow);
        a[i] = d;
        borrow = u64::from(o1 || o2);
    }
}

fn bits(a: &Big) -> u32 {
    (0..5)
        .rev()
        .find(|&i| a[i] != 0)
        .map_or(0, |i| 64 * i as u32 + 64 - a[i].leading_zeros())
}

/// `LE2IP(buf) mod m`, bit by bit from the most significant one (`m < 2^256`).
fn le2ip_mod(buf: &[u8], m: &Big) -> Big {
    let mut acc = [0u64; 5];
    for byte in buf.iter().rev() {
        for bit in (0..8).rev() {
            // acc < m < 2^256, so 2·acc + 1 < 2^257 fits
            for i in (1..5).rev() {
                acc[i] = (acc[i] << 1) | (acc[i - 1] >> 63);
            }
            acc[0] = (acc[0] << 1) | u64::from((byte >> bit) & 1);
            if ge(&acc, m) {
                sub(&mut acc, m);
            }
        }
    }
    acc
}

/// `N_s` of the modulus `m`: `⌈bits(m − 1)/8⌉` (for a modulus that is not a power of two this is
/// `⌈bits(m)/8⌉`).
fn ns_of(m: &Big) -> usize {
    let mut m1 = *m;
    sub(&mut m1, &big("1"));
    bits(&m1).div_ceil(8) as usize
}

/// `LE(x, n)`.
fn le_bytes(x: &Big, n: usize) -> Vec<u8> {
    let all: Vec<u8> = x.iter().flat_map(|l| l.to_le_bytes()).collect();
    assert!(all[n..].iter().all(|b| *b == 0));
    all[..n].to_vec()
}

/// `LE2IP(x)` for at most 40 bytes.
fn from_le(x: &[u8]) -> Big {
    let mut padded = [0u8; 40];
    padded[..x.len()].copy_from_slice(x);
    let mut out = [0u64; 5];
    for (i, limb) in out.iter_mut().enumerate() {
        *limb = u64::from_le_bytes(padded[8 * i..8 * i + 8].try_into().unwrap());
    }
    out
}

/// `DeserializeUint(input, m)`: the next `N_s` bytes little-endian, `None` if short or `≥ m`.
fn deserialize_uint<'a>(input: &'a [u8], m: &Big) -> Option<(Big, &'a [u8])> {
    let n = ns_of(m);
    if input.len() < n {
        return None;
    }
    let x = from_le(&input[..n]);
    (!ge(&x, m)).then_some((x, &input[n..]))
}

// ---------------------------------------------------------------------------------------------
// draft-irtf-cfrg-fiat-shamir-04
// ---------------------------------------------------------------------------------------------

/// Runs the `Operations` of a vector on the sponge, returning every squeezed byte.
fn run(sponge: &mut DuplexSponge, v: &Value) -> Vec<u8> {
    let mut out = Vec::new();
    for op in v["Operations"].as_array().unwrap() {
        let op = op.as_str().unwrap();
        if let Some(x) = op.strip_prefix("absorb ") {
            sponge.absorb(&bytes(x));
        } else if let Some(n) = op.strip_prefix("squeeze ") {
            let mut buf = vec![0u8; n.parse().unwrap()];
            sponge.squeeze(&mut buf);
            out.extend_from_slice(&buf);
        } else {
            panic!("unknown operation {op}");
        }
    }
    out
}

fn session_id(v: &Value) -> [u8; 32] {
    bytes(field(v, "SessionId")).try_into().unwrap()
}

/// The sumcheck example of FS -04 Appendix B over a prime `p < 2^32` (`N_s = 4`).
mod sumcheck {
    use super::*;

    fn le4(x: u64) -> [u8; 4] {
        u32::try_from(x).unwrap().to_le_bytes()
    }

    /// `r := LE2IP(state.Squeeze(Ns)) mod p` with `Ns = 4`.
    fn challenge(state: &mut DuplexSponge, p: u64) -> u64 {
        u64::from(u32::from_le_bytes(state.squeeze_array::<4>())) % p
    }

    fn start(session_id: &[u8; 32], v: u32, s: u64) -> DuplexSponge {
        let mut state = DuplexSponge::new(session_id);
        let mut instance = v.to_le_bytes().to_vec();
        instance.extend_from_slice(&le4(s));
        state.absorb(&instance);
        state
    }

    /// `SumcheckProve`: the NARG string and the final evaluation.
    pub(super) fn prove(session_id: &[u8; 32], p: u64, v: u32, w: &[u64]) -> (Vec<u8>, u64) {
        let mut w: Vec<u64> = w.iter().map(|x| x % p).collect();
        let s = w.iter().fold(0, |a, x| (a + x) % p);
        let mut state = start(session_id, v, s);
        let mut narg = Vec::new();
        for _ in 0..v {
            let a0 = w.iter().step_by(2).fold(0, |a, x| (a + x) % p);
            let odd = w.iter().skip(1).step_by(2).fold(0, |a, x| (a + x) % p);
            let a1 = (odd + p - a0) % p;
            let mut msg = le4(a0).to_vec();
            msg.extend_from_slice(&le4(a1));
            state.absorb(&msg);
            narg.extend_from_slice(&msg);
            let r = challenge(&mut state, p);
            w = w
                .chunks(2)
                .map(|c| (c[0] + r * ((c[1] + p - c[0]) % p)) % p)
                .collect();
        }
        (narg, w[0])
    }

    /// `SumcheckVerify`, with the reason of a rejection.
    pub(super) fn verify(
        session_id: &[u8; 32],
        p: u64,
        v: u32,
        claimed: u64,
        narg: &[u8],
        y: u64,
    ) -> Result<(), &'static str> {
        let modulus = big(&p.to_string());
        let mut state = start(session_id, v, claimed);
        let (mut s, mut rest) = (claimed, narg);
        for _ in 0..v {
            let (a0, r1) = deserialize_uint(rest, &modulus).ok_or("deserialization")?;
            let (a1, r2) = deserialize_uint(r1, &modulus).ok_or("deserialization")?;
            rest = r2;
            let (a0, a1) = (a0[0], a1[0]);
            if (2 * a0 + a1) % p != s {
                return Err("round sum");
            }
            let mut msg = le4(a0).to_vec();
            msg.extend_from_slice(&le4(a1));
            state.absorb(&msg);
            let r = challenge(&mut state, p);
            s = (a0 + a1 * r) % p;
        }
        if !rest.is_empty() {
            return Err("trailing bytes");
        }
        if s != y {
            return Err("final evaluation");
        }
        Ok(())
    }
}

#[test]
fn fiat_shamir_04_vectors() {
    let all = vectors(FS_VECTORS);
    let by_id = |id: &str| all.iter().find(|v| v["Id"] == id).unwrap().clone();
    let turbo = |v: &Value| v.get("Suite").is_some_and(|s| s == "TurboSHAKE128");
    let mut ran = BTreeMap::<&str, usize>::new();
    for v in all.iter().filter(|v| !turbo(v)) {
        let id = field(v, "Id");
        let function = field(v, "Function");
        match function {
            "DuplexSponge" => {
                let out = run(&mut DuplexSponge::new(&session_id(v)), v);
                assert_eq!(hex(&out), field(v, "Output"), "{id}");
            }
            "DeriveSessionID" => {
                let sid = derive_session_id(&bytes(field(v, "Tag")));
                assert_eq!(hex(&sid), field(v, "SessionId"), "{id}");
            }
            "DecodeUint" => {
                let m = big(field(v, "Modulus"));
                let buf = if v.get("Operations").is_some() {
                    let out = run(&mut DuplexSponge::new(&session_id(v)), v);
                    assert_eq!(hex(&out), field(v, "Output"), "{id}");
                    out
                } else {
                    bytes(field(v, "Input"))
                };
                assert_eq!(ns_of(&m) + 16, buf.len(), "{id}");
                assert_eq!(
                    le2ip_mod(&buf, &m),
                    big(field(v, "VerifierMessage")),
                    "{id}"
                );
            }
            "SerializeVarLenString" => {
                let input = bytes(field(v, "Input"));
                let out = [(input.len() as u32).to_le_bytes().to_vec(), input].concat();
                assert_eq!(hex(&out), field(v, "Output"), "{id}");
            }
            "SerializeUint" => {
                let m = big(field(v, "Modulus"));
                let x = big(field(v, "Value"));
                assert!(!ge(&x, &m));
                assert_eq!(hex(&le_bytes(&x, ns_of(&m))), field(v, "Output"), "{id}");
            }
            "SerializeField" => {
                // the big-endian serialization, which this crate's scalar codec is: the value is
                // below the modulus of BLS12-381 too, and both moduli have N_s = 32
                assert_eq!(field(v, "ByteOrder"), "big-endian", "{id}");
                let m = big(field(v, "Modulus"));
                assert_eq!(ns_of(&m), ns::<Fr>(), "{id}");
                let x = big(field(v, "Value"));
                assert!(x[1..].iter().all(|l| *l == 0));
                assert_eq!(
                    hex(&scalar_to_bytes(&Fr::from(x[0]))),
                    field(v, "Output"),
                    "{id}"
                );
            }
            "DeserializeVarLenString" => {
                assert_eq!(field(v, "Expected"), "reject", "{id}");
                let input = bytes(field(v, "Input"));
                let accepted = input.split_first_chunk::<4>().is_some_and(|(head, rest)| {
                    usize::try_from(u32::from_le_bytes(*head)).is_ok_and(|n| rest.len() >= n)
                });
                assert!(!accepted, "{id}");
            }
            "DeserializeUint" => {
                assert_eq!(field(v, "Expected"), "reject", "{id}");
                let m = big(field(v, "Modulus"));
                assert!(
                    deserialize_uint(&bytes(field(v, "Input")), &m).is_none(),
                    "{id}"
                );
            }
            "DeserializeField" => {
                // coordinate by coordinate, every one canonical
                assert_eq!(field(v, "Expected"), "reject", "{id}");
                let m = big(field(v, "Modulus"));
                let degree: usize = field(v, "ExtensionDegree").parse().unwrap();
                let input = bytes(field(v, "Input"));
                let mut rest = input.as_slice();
                let mut ok = true;
                for _ in 0..degree {
                    match deserialize_uint(rest, &m) {
                        Some((_, r)) => rest = r,
                        None => ok = false,
                    }
                }
                assert!(!ok, "{id}");
            }
            "Sumcheck" => {
                let p = big(field(v, "Modulus"))[0];
                let nv: u32 = field(v, "NumVariables").parse().unwrap();
                let claimed = big(field(v, "ClaimedSum"))[0];
                let sid = session_id(v);
                if let Some(tag) = v.get("Tag") {
                    assert_eq!(
                        derive_session_id(&bytes(tag.as_str().unwrap())),
                        sid,
                        "{id}"
                    );
                }
                if field(v, "Expected") == "accept" {
                    let w: Vec<u64> = v["Witness"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|x| x.as_str().unwrap().parse().unwrap())
                        .collect();
                    let (narg, y) = sumcheck::prove(&sid, p, nv, &w);
                    assert_eq!(hex(&narg), field(v, "NargString"), "{id}");
                    assert_eq!(y, big(field(v, "FinalEvaluation"))[0], "{id}");
                    assert_eq!(sumcheck::verify(&sid, p, nv, claimed, &narg, y), Ok(()));
                } else {
                    let narg = bytes(field(v, "NargString"));
                    // the baseline's final evaluation, so that only the vector's own defect fails
                    let y = v.get("BaseId").map_or(0, |b| {
                        big(field(&by_id(b.as_str().unwrap()), "FinalEvaluation"))[0]
                    });
                    let reason = if id.ends_with("trailing_bytes") {
                        "trailing bytes"
                    } else {
                        "deserialization"
                    };
                    assert_eq!(
                        sumcheck::verify(&sid, p, nv, claimed, &narg, y),
                        Err(reason),
                        "{id}"
                    );
                }
            }
            other => panic!("{id}: no runner for {other}"),
        }
        *ran.entry(function).or_default() += 1;
    }
    assert_eq!(all.len(), 35);
    assert_eq!(all.iter().filter(|v| turbo(v)).count(), 12);
    let expected: BTreeMap<&str, usize> = [
        ("DecodeUint", 2),
        ("DeriveSessionID", 1),
        ("DeserializeField", 1),
        ("DeserializeUint", 2),
        ("DeserializeVarLenString", 2),
        ("DuplexSponge", 8),
        ("SerializeField", 1),
        ("SerializeUint", 1),
        ("SerializeVarLenString", 2),
        ("Sumcheck", 3),
    ]
    .into_iter()
    .collect();
    assert_eq!(ran, expected);
    assert_eq!(ran.values().sum::<usize>(), 23, "vectors run");
}

/// `DecodeField` of the library (arkworks' `from_le_bytes_mod_order` over the scalar field of
/// BLS12-381) is `LE2IP(buf) mod p` of the reference above, on edge cases and random inputs.
#[test]
fn decode_field_is_the_integer_reduction() {
    let r_hex = hex(&Fr::MODULUS.to_bytes_be());
    let r = big(&format!("0x{r_hex}"));
    let check = |buf: &[u8]| {
        let ours: Fr = decode_field(buf).unwrap();
        let reference = le2ip_mod(buf, &r);
        let reference_be: Vec<u8> = le_bytes(&reference, 32).into_iter().rev().collect();
        assert_eq!(scalar_to_bytes(&ours), reference_be, "{}", hex(buf));
    };
    let mut edge = vec![[0u8; 48], [0xff; 48]];
    // p, p − 1, p + 1 and 2^256 · p as 48 little-endian bytes
    let p_le = Fr::MODULUS.to_bytes_le();
    let mut p = [0u8; 48];
    p[..32].copy_from_slice(&p_le);
    edge.push(p);
    let mut p_minus_1 = p;
    p_minus_1[0] -= 1;
    edge.push(p_minus_1);
    let mut p_plus_1 = p;
    p_plus_1[0] += 1;
    edge.push(p_plus_1);
    let mut shifted = [0u8; 48];
    shifted[16..48].copy_from_slice(&p_le);
    edge.push(shifted);
    for buf in &edge {
        check(buf);
    }
    let mut rng = StdRng::seed_from_u64(0x1e7f_0001);
    for _ in 0..256 {
        let mut buf = [0u8; 48];
        rng.fill_bytes(&mut buf);
        check(&buf);
    }
}

// ---------------------------------------------------------------------------------------------
// draft-irtf-cfrg-sigma-protocols-04, ciphersuite sigma-proofs_Shake128_BLS12381
// ---------------------------------------------------------------------------------------------

/// The seeded generator of Sigma -04 Appendix A.1: a duplex sponge initialized with
/// `DeriveSessionID(prng_tag)`, read by squeezing. TEST ONLY: the draft forbids its use in
/// applications.
struct SeededPrng(DuplexSponge);

impl SeededPrng {
    fn new(tag: &str) -> Self {
        Self(DuplexSponge::new(&derive_session_id(tag.as_bytes())))
    }
}

impl RngCore for SeededPrng {
    fn next_u32(&mut self) -> u32 {
        u32::from_le_bytes(self.0.squeeze_array())
    }

    fn next_u64(&mut self) -> u64 {
        u64::from_le_bytes(self.0.squeeze_array())
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.squeeze(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// Test-only marker: the provers ask for a `CryptoRng`.
impl CryptoRng for SeededPrng {}

const SUITE: &str = "sigma-proofs_Shake128_BLS12381";
/// `N_e` of `G_1`.
const NE: usize = 48;
/// `N_s`.
const NS: usize = 32;

/// `ProveBatchable` of §5.4: `Group.serialize(commitment) ‖ Scalar.serialize(response)`, with the
/// challenge `DeriveChallenge(tag, instance, Group.serialize(commitment))`.
fn prove_batchable<R: LinearRelation<Scalar = Fr>>(
    tag: &[u8],
    rel: &R,
    witness: &[Fr],
    rng: &mut SeededPrng,
) -> Vec<u8> {
    assert!(rel.validate().is_ok() && rel.is_satisfied_by(witness));
    let (commitment, state) = commit(rel, rng).unwrap();
    let mut narg = rel.serialize_image(&commitment).unwrap();
    let challenge = derive_challenge(tag, rel, &narg).unwrap();
    for z in respond(state, witness, &challenge).unwrap() {
        narg.extend_from_slice(&scalar_to_bytes(&z));
    }
    narg
}

/// `VerifyBatchable` of §5.4 over `G_1`: the exact length, strict deserialization of the
/// commitment points (on the curve, in `G_1`, canonical) and of the responses, then the
/// interactive verifier (which validates the instance).
fn verify_batchable(tag: &[u8], rel: &GroupRelation<G1Projective>, narg: &[u8]) -> bool {
    let (neq, nsc) = (rel.equations().len(), rel.num_scalars());
    if rel.validate().is_err() || narg.len() != NE * neq + NS * nsc {
        return false;
    }
    let (commitment_bytes, response_bytes) = narg.split_at(NE * neq);
    let Ok(commitment) = commitment_bytes
        .chunks(NE)
        .map(|chunk| G1Affine::deserialize_compressed(chunk).map(G1Projective::from))
        .collect::<Result<Vec<_>, _>>()
    else {
        return false;
    };
    let Some(responses) = response_bytes
        .chunks(NS)
        .map(scalar_from_bytes::<Fr>)
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let Ok(serialized) = rel.serialize_image(&commitment) else {
        return false;
    };
    let Ok(challenge) = derive_challenge(tag, rel, &serialized) else {
        return false;
    };
    verify(rel, &commitment, &challenge, &responses)
}

/// The verifier's decision on a vector, from its bytes alone.
fn decide(v: &Value) -> bool {
    let tag = field(v, "Tag").as_bytes();
    let narg = bytes(field(v, "NargString"));
    let Ok(rel) = GroupRelation::<G1Projective>::from_instance_bytes(&bytes(field(v, "Instance")))
    else {
        return false;
    };
    match field(v, "Flavor") {
        "compact" => verify_compact(tag, &rel, &narg),
        "batchable" => verify_batchable(tag, &rel, &narg),
        other => panic!("unknown flavor {other}"),
    }
}

/// The relation built again through the value builder of `GroupRelation`: the elements declared
/// in the order of the instance, then the equations by value.
fn rebuilt_group(rel: &GroupRelation<G1Projective>) -> GroupRelation<G1Projective> {
    let mut out = GroupRelation::new();
    out.alloc_scalars(rel.num_scalars());
    for element in rel.elements() {
        out.declare_element(*element);
    }
    for equation in rel.linear_equations() {
        out.add_equation(equation).unwrap();
    }
    out
}

/// The same through `PairingRelation`, the statement type of the protocol (`G_1` equations only).
fn rebuilt_pairing(rel: &GroupRelation<G1Projective>) -> PairingRelation<Bls12_381> {
    let mut out = PairingRelation::new();
    out.alloc_scalars(rel.num_scalars());
    for element in rel.elements() {
        out.declare_g1_element(*element);
    }
    for equation in rel.linear_equations() {
        out.add_g1(equation).unwrap();
    }
    out
}

#[test]
fn sigma_protocols_04_bls12_381_vectors() {
    let all = vectors(SIGMA_VECTORS);
    let ours: Vec<&Value> = all.iter().filter(|v| v["Ciphersuite"] == SUITE).collect();
    assert_eq!((all.len(), ours.len()), (95, 47));
    let by_id = |id: &str| *ours.iter().find(|v| v["Id"] == id).unwrap();

    let mut decisions = BTreeMap::<(String, String), usize>::new();
    let mut reproduced = BTreeMap::<String, usize>::new();
    let mut baselines = 0;
    for v in &ours {
        let id = field(v, "Id");
        assert_eq!(field(v, "Function"), "SigmaProof", "{id}");
        let (tag, flavor, expected) = (field(v, "Tag"), field(v, "Flavor"), field(v, "Expected"));
        assert!(expected == "accept" || expected == "reject", "{id}");
        if let Some(sid) = v.get("SessionId") {
            assert_eq!(
                hex(&derive_session_id(tag.as_bytes())),
                sid.as_str().unwrap(),
                "{id}"
            );
        }

        // the decision
        assert_eq!(decide(v), expected == "accept", "{id}: expected {expected}");
        *decisions
            .entry((flavor.to_owned(), expected.to_owned()))
            .or_default() += 1;
        if let Some(base) = v.get("BaseId") {
            assert!(
                decide(by_id(base.as_str().unwrap())),
                "{id}: its baseline is rejected"
            );
            baselines += 1;
        }

        // the valid proofs, reproduced
        let Some(witness) = v.get("Witness") else {
            continue;
        };
        let instance = bytes(field(v, "Instance"));
        let rel = GroupRelation::<G1Projective>::from_instance_bytes(&instance).unwrap();
        assert_eq!(
            rel.serialize_instance().unwrap(),
            instance,
            "{id}: round trip"
        );
        assert_eq!(rel.suite_id(), SIGMA_BLS12381);
        let witness: Vec<Fr> = bytes(witness.as_str().unwrap())
            .chunks(NS)
            .map(|chunk| scalar_from_bytes(chunk).unwrap())
            .collect();
        assert_eq!(witness.len(), rel.num_scalars(), "{id}");
        assert!(
            rel.is_satisfied_by(&witness),
            "{id}: the witness satisfies the instance"
        );

        let relation = field(v, "Relation");
        let marker = match flavor {
            "compact" => "CMPT",
            "batchable" => "DSFS",
            other => panic!("unknown flavor {other}"),
        };
        let prng = || {
            SeededPrng::new(&format!(
                "TestDRNG-SIGMA-PROOFS-{marker}-{SUITE}-{relation}"
            ))
        };
        let narg = field(v, "NargString");
        let (group, pairing) = (rebuilt_group(&rel), rebuilt_pairing(&rel));
        // the value builders compile to the draft's instance, byte for byte
        assert_eq!(
            group.serialize_instance().unwrap(),
            instance,
            "{id}: GroupRelation"
        );
        assert_eq!(
            pairing.serialize_instance().unwrap(),
            instance,
            "{id}: PairingRelation"
        );
        assert_eq!(pairing.suite_id(), SIGMA_BLS12381);
        let proofs = match flavor {
            "compact" => [
                prove_compact(tag.as_bytes(), &rel, &witness, &mut prng()).unwrap(),
                prove_compact(tag.as_bytes(), &group, &witness, &mut prng()).unwrap(),
                prove_compact(tag.as_bytes(), &pairing, &witness, &mut prng()).unwrap(),
            ],
            _ => [
                prove_batchable(tag.as_bytes(), &rel, &witness, &mut prng()),
                prove_batchable(tag.as_bytes(), &group, &witness, &mut prng()),
                prove_batchable(tag.as_bytes(), &pairing, &witness, &mut prng()),
            ],
        };
        for proof in &proofs {
            assert_eq!(hex(proof), narg, "{id}: the NARG string is reproduced");
        }
        if flavor == "compact" {
            assert!(verify_compact(tag.as_bytes(), &pairing, &proofs[2]));
        }
        *reproduced.entry(flavor.to_owned()).or_default() += 1;
    }

    let count = |flavor: &str, expected: &str| decisions[&(flavor.to_owned(), expected.to_owned())];
    assert_eq!(
        (
            count("batchable", "accept"),
            count("batchable", "reject"),
            count("compact", "accept"),
            count("compact", "reject"),
        ),
        (14, 15, 9, 9)
    );
    assert_eq!(decisions.values().sum::<usize>(), 47, "vectors run");
    assert_eq!(reproduced["compact"], 7, "compact proofs reproduced");
    assert_eq!(reproduced["batchable"], 7, "batchable proofs reproduced");
    assert_eq!(
        baselines, 24,
        "adversarial vectors checked against their baseline"
    );
}

/// The draft's adversarial vectors flip one property at a time. This one checks the same
/// properties on a fresh proof of the library under its own tag: the decisions of the compact
/// verifier do not depend on the vectors' particular bytes.
#[test]
fn compact_verifier_rejects_what_the_draft_rejects() {
    let mut rng = StdRng::seed_from_u64(0x1e7f_0002);
    let all = vectors(SIGMA_VECTORS);
    let v = all
        .iter()
        .find(|v| v["Id"] == "sigma-protocols/bls12381/pedersen_commitment/compact")
        .unwrap();
    let rel =
        GroupRelation::<G1Projective>::from_instance_bytes(&bytes(field(v, "Instance"))).unwrap();
    let witness: Vec<Fr> = bytes(field(v, "Witness"))
        .chunks(NS)
        .map(|chunk| scalar_from_bytes(chunk).unwrap())
        .collect();
    let tag = b"pcs-test-CMPT-with-sigma-proofs_Shake128_BLS12381";
    let narg = prove_compact(tag, &rel, &witness, &mut rng).unwrap();
    assert!(verify_compact(tag, &rel, &narg));
    // trailing byte, truncation, an all-zero proof
    assert!(!verify_compact(
        tag,
        &rel,
        &[narg.clone(), vec![0]].concat()
    ));
    assert!(!verify_compact(tag, &rel, &narg[..narg.len() - 1]));
    assert!(!verify_compact(tag, &rel, &vec![0u8; narg.len()]));
    // a scalar re-encoded as s + p (non-canonical, same value modulo p)
    let p = Fr::MODULUS.to_bytes_be();
    for at in (0..narg.len()).step_by(NS) {
        let s = &narg[at..at + NS];
        let mut sum = [0u8; NS];
        let mut carry = 0u16;
        for i in (0..NS).rev() {
            let t = u16::from(s[i]) + u16::from(p[i]) + carry;
            sum[i] = t as u8;
            carry = t >> 8;
        }
        if carry == 0 {
            let mut bad = narg.clone();
            bad[at..at + NS].copy_from_slice(&sum);
            assert!(!verify_compact(tag, &rel, &bad), "s + p at {at}");
        }
        // and a changed value
        let mut bad = narg.clone();
        bad[at + NS - 1] ^= 1;
        assert!(!verify_compact(tag, &rel, &bad), "flipped bit at {at}");
    }
    // another tag (flavor, suite or application) and another statement
    for other in [
        &b"pcs-test-DSFS-with-sigma-proofs_Shake128_BLS12381"[..],
        b"pcs-test-CMPT-with-sigma-proofs_Shake128_P256",
        b"",
    ] {
        assert!(!verify_compact(other, &rel, &narg));
    }
    let mut changed = rebuilt_group(&rel);
    changed.alloc_scalar();
    assert!(
        verify_compact(tag, &changed, &narg),
        "an unused variable is not part of it"
    );
    // the first element of the statement moved by the generator
    let first = rel.elements()[0];
    let moved = first + G1Projective::generator();
    let mut changed = GroupRelation::<G1Projective>::new();
    changed.alloc_scalars(rel.num_scalars());
    for element in rel.elements() {
        changed.declare_element(if *element == first { moved } else { *element });
    }
    for mut equation in rel.linear_equations() {
        let swap = |e: &mut G1Projective| {
            if *e == first {
                *e = moved;
            }
        };
        equation.image.iter_mut().for_each(|(e, _)| swap(e));
        equation.terms.iter_mut().for_each(|(_, e, _)| swap(e));
        changed.add_equation(equation).unwrap();
    }
    assert_ne!(
        changed.serialize_instance().unwrap(),
        rel.serialize_instance().unwrap()
    );
    assert!(!verify_compact(tag, &changed, &narg));
    // a fresh proof is a different string (fresh nonces), and also verifies
    let again = prove_compact(tag, &rel, &witness, &mut rng).unwrap();
    assert_ne!(again, narg);
    assert!(verify_compact(tag, &rel, &again));
}
