//! Integration tests of the credential base `Σ-vSIS` (`pcreds::lattice::base`, §6.2.3) through
//! the PUBLIC API only, with ONE real helper key per test (TrapGen of `ntru-trapdoor`, about
//! 6 ms): the issuance flow of the box with every object over the wire, the wire sizes of every
//! base object, the issuance counter of the cap $`Q_{\max}`$ through the helper's encoding, and
//! decoders fed with arbitrary bytes. The unit tests of `pcreds::lattice::base` cover the
//! algorithms in detail.
//!
//! Fast: nothing here runs a Jali proof.

#![cfg(feature = "lattice")]
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use predicate_credential_system::{
    Error,
    lattice::{Q_MAX, Rq, S_BOUND, Ternary},
    pcreds::{
        IssuanceRecord, Policy,
        lattice::{
            LatticeProtocol,
            base::{
                VSIS, VSISCredential, VSISParams, VSISPreCredential, VSISSigningKey, VSISTape,
                VSISVerificationKey,
            },
        },
    },
    serialization::{WireFormat, from_bytes, to_bytes},
};
use rand::{RngCore, SeedableRng, rngs::StdRng};

const LABEL: &[u8] = b"PCS-VSIS-INTEGRATION";

/// The issuance flow of the box, with the request and the pre-credential over the wire: the
/// user commits, the helper issues blindly, the user unblinds (and `Unblind` verifies).
fn issue(
    pp: &VSISParams,
    vk: &VSISVerificationKey,
    sk: &VSISSigningKey,
    usk: &Ternary,
    tape: &VSISTape,
    rng: &mut StdRng,
) -> Result<VSISCredential, Error> {
    let c = VSIS::prepare_issue(pp, usk, tape).ok_or(Error::InvalidIssuanceEncoding)?;
    let c = from_bytes::<Rq>(&to_bytes(&c)?)?; // over the wire
    let pre = VSIS::blind_issue(pp, sk, &c, rng)?;
    let pre = from_bytes::<VSISPreCredential>(&to_bytes(&pre)?)?; // over the wire
    let cred = VSIS::unblind(pp, vk, usk, &pre, tape)?;
    assert!(VSIS::verify(pp, vk, usk, &cred));
    Ok(cred)
}

#[test]
fn issuance_through_the_public_api() {
    let mut rng = StdRng::seed_from_u64(0x7515_0001);
    let pp = VSIS::setup(LABEL);
    let (vk, sk) = VSIS::keygen(&mut rng);
    assert!(VSIS::admissible_key(&vk));
    assert!(VSIS::key_pair_matches(&vk, &sk));
    let usk = Ternary::sample(&mut rng);
    let tape = VSISTape::sample(&mut rng);
    let cred = issue(&pp, &vk, &sk, &usk, &tape, &mut rng).unwrap();
    assert!(cred.pre().norm_sq() <= S_BOUND && cred.pre().norm_sq() > 0);
    assert_eq!((sk.issued(), sk.remaining()), (1, Q_MAX - 1));
    // the credential of one key does not verify under another, nor for another key usk
    let (vk2, _) = VSIS::keygen(&mut rng);
    assert!(!VSIS::verify(&pp, &vk2, &usk, &cred));
    assert!(!VSIS::verify(&pp, &vk, &Ternary::sample(&mut rng), &cred));
}

/// The sizes of the base objects, which the backend's encodings build on.
#[test]
fn wire_sizes_of_the_base_objects() {
    let mut rng = StdRng::seed_from_u64(0x7515_0002);
    let pp = VSIS::setup(LABEL);
    let (vk, sk) = VSIS::keygen(&mut rng);
    let usk = Ternary::sample(&mut rng);
    let tape = VSISTape::sample(&mut rng);
    let c = VSIS::prepare_issue(&pp, &usk, &tape).unwrap();
    let pre = VSIS::blind_issue(&pp, &sk, &c, &mut rng).unwrap();
    let cred = VSIS::unblind(&pp, &vk, &usk, &pre, &tape).unwrap();
    let sizes = [
        (pp.to_bytes().unwrap().len(), VSISParams::BYTES, 12_800),
        (to_bytes(&sk).unwrap().len(), VSISSigningKey::BYTES, 5_897),
        (
            vk.to_bytes().unwrap().len(),
            VSISVerificationKey::BYTES,
            2_560,
        ),
        (to_bytes(&c).unwrap().len(), Rq::BYTES, 2_560),
        (to_bytes(&tape).unwrap().len(), VSISTape::BYTES, 768),
        (
            pre.to_bytes().unwrap().len(),
            VSISPreCredential::BYTES,
            5_376,
        ),
        (to_bytes(&cred).unwrap().len(), VSISCredential::BYTES, 6_144),
        (to_bytes(&usk).unwrap().len(), Ternary::BYTES, 256),
    ];
    for (actual, constant, expected) in sizes {
        assert_eq!((actual, constant), (expected, expected));
    }
    // serialized_size agrees with the bytes written
    assert_eq!(pp.compressed_size(), 12_800);
    assert_eq!(sk.compressed_size(), 5_897);
    assert_eq!(pre.compressed_size(), 5_376);
    assert_eq!(cred.compressed_size(), 6_144);
    // round trips
    assert_eq!(VSISParams::from_bytes(&pp.to_bytes().unwrap()).unwrap(), pp);
    assert_eq!(
        VSISVerificationKey::from_bytes(&vk.to_bytes().unwrap()).unwrap(),
        vk
    );
    assert_eq!(
        VSISPreCredential::from_bytes(&pre.to_bytes().unwrap()).unwrap(),
        pre
    );
    assert_eq!(
        from_bytes::<VSISCredential>(&to_bytes(&cred).unwrap()).unwrap(),
        cred
    );
}

/// The helper's key `digest ‖ hvk ‖ sk` (32 + 2560 + 5897 = 8489 bytes): the issuance counter
/// travels with it, a restored helper issues under the same `hvk`, and a copy stored AHEAD of the
/// true count (`to_bytes_reserving`) restores with the advanced count.
#[test]
fn the_helper_key_carries_the_issuance_count() {
    let mut rng = StdRng::seed_from_u64(0x7515_0003);
    let pcreds = LatticeProtocol::setup(LABEL).unwrap();
    let policy = Policy::threshold(1).unwrap();
    let helper = pcreds.helper_keygen(policy, &mut rng);
    let usk = Ternary::sample(&mut rng);
    let tape = VSISTape::sample(&mut rng);
    let pp = pcreds.params().sigma();
    let c = VSIS::prepare_issue(pp, &usk, &tape).unwrap();
    // five issuances through a restored copy of the key, which counts them
    let restored = pcreds
        .restore_helper(&helper.to_bytes().unwrap(), policy, IssuanceRecord::new())
        .unwrap();
    let bytes = restored.to_bytes().unwrap();
    assert_eq!(bytes.len(), 8_489);
    let sk = from_bytes::<VSISSigningKey>(&bytes[32 + 2560..]).unwrap();
    for _ in 0..5 {
        VSIS::blind_issue(pp, &sk, &c, &mut rng).unwrap();
    }
    assert_eq!(sk.issued(), 5);
    assert_eq!(&sk.verification_key().unwrap(), helper.key().vk());
    let stored = sk.to_bytes_reserving(0).unwrap();
    let back = from_bytes::<VSISSigningKey>(&stored).unwrap();
    assert_eq!(back.issued(), 5);
    let pre = VSIS::blind_issue(pp, &back, &c, &mut rng).unwrap();
    assert!(VSIS::unblind(pp, helper.key().vk(), &usk, &pre, &tape).is_ok());
    assert_eq!(back.issued(), 6);
    // ahead of the true count, through the helper
    let ahead = helper.to_bytes_reserving(100).unwrap();
    let ahead_sk = from_bytes::<VSISSigningKey>(&ahead[32 + 2560..]).unwrap();
    assert_eq!(ahead_sk.issued(), 100);
    assert_eq!(format!("{back:?}"), "VSISSigningKey(<redacted>)");
}

/// The cap ("Issuance cap"): a key stored with Q_max − 1 calls used answers once more, then
/// refuses, also after another round trip; a stored count above Q_max is no key.
#[test]
fn a_key_restored_near_the_cap_answers_once_more() {
    let mut rng = StdRng::seed_from_u64(0x7515_0004);
    let pp = VSIS::setup(LABEL);
    let (_vk, sk) = VSIS::keygen(&mut rng);
    let usk = Ternary::sample(&mut rng);
    let tape = VSISTape::sample(&mut rng);
    let c = VSIS::prepare_issue(&pp, &usk, &tape).unwrap();
    let mut bytes = to_bytes(&sk).unwrap();
    let count = bytes.len() - 8;
    bytes[count..].copy_from_slice(&(Q_MAX - 1).to_le_bytes());
    let restored: VSISSigningKey = from_bytes(&bytes).unwrap();
    assert_eq!(restored.remaining(), 1);
    assert!(VSIS::blind_issue(&pp, &restored, &c, &mut rng).is_ok());
    assert_eq!(
        VSIS::blind_issue(&pp, &restored, &c, &mut rng).unwrap_err(),
        Error::IssuanceCapReached
    );
    let again: VSISSigningKey = from_bytes(&to_bytes(&restored).unwrap()).unwrap();
    assert_eq!((again.issued(), again.remaining()), (Q_MAX, 0));
    bytes[count..].copy_from_slice(&(Q_MAX + 1).to_le_bytes());
    assert!(from_bytes::<VSISSigningKey>(&bytes).is_err());
}

/// 16 threads issue through one `&VSISSigningKey` with 10 calls left: exactly 10 succeed.
#[test]
fn concurrent_issuance_through_one_key_respects_the_cap() {
    let mut rng = StdRng::seed_from_u64(0x7515_0005);
    let pp = VSIS::setup(LABEL);
    let (_vk, sk) = VSIS::keygen(&mut rng);
    let mut bytes = to_bytes(&sk).unwrap();
    let count = bytes.len() - 8;
    bytes[count..].copy_from_slice(&(Q_MAX - 10).to_le_bytes());
    let sk: VSISSigningKey = from_bytes(&bytes).unwrap();
    let usk = Ternary::sample(&mut rng);
    let tape = VSISTape::sample(&mut rng);
    let c = VSIS::prepare_issue(&pp, &usk, &tape).unwrap();
    let issued: usize = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..16u64)
            .map(|i| {
                let (pp, sk, c) = (&pp, &sk, &c);
                scope.spawn(move || {
                    let mut rng = StdRng::seed_from_u64(1000 + i);
                    (0..3)
                        .filter(|_| match VSIS::blind_issue(pp, sk, c, &mut rng) {
                            Ok(_) => true,
                            Err(e) => {
                                assert_eq!(e, Error::IssuanceCapReached);
                                false
                            }
                        })
                        .count()
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).sum()
    });
    assert_eq!(issued, 10);
    assert_eq!(sk.issued(), Q_MAX);
}

/// Every decoder of the base refuses or accepts arbitrary bytes without panicking, and `Verify`
/// rejects whatever decodes.
#[test]
fn decoders_never_panic_on_arbitrary_bytes() {
    let mut rng = StdRng::seed_from_u64(0x7515_0006);
    let pp = VSIS::setup(LABEL);
    let (vk, _) = VSIS::keygen(&mut rng);
    let usk = Ternary::sample(&mut rng);
    let mut decoded = [0usize; 6];
    for round in 0..64 {
        let lengths = [
            VSISParams::BYTES,
            VSISSigningKey::BYTES,
            VSISVerificationKey::BYTES,
            VSISTape::BYTES,
            VSISPreCredential::BYTES,
            VSISCredential::BYTES,
        ];
        for (k, &len) in lengths.iter().enumerate() {
            for delta in [0usize, 1, 2] {
                let mut bytes = vec![0u8; len + delta - 1];
                rng.fill_bytes(&mut bytes);
                if k == 1 && !bytes.is_empty() {
                    bytes[0] = 0xAA; // past the header check, into the trapdoor validation
                }
                if round % 2 == 0 && k >= 4 {
                    // past the ternary checks: every 2-bit code 10 after s becomes 00
                    let ternary = 2 * 2560;
                    for byte in bytes.iter_mut().skip(ternary) {
                        for shift in [0, 2, 4, 6] {
                            if (*byte >> shift) & 3 == 2 {
                                *byte &= !(3 << shift);
                            }
                        }
                    }
                }
                let ok = match k {
                    0 => from_bytes::<VSISParams>(&bytes).is_ok(),
                    1 => from_bytes::<VSISSigningKey>(&bytes).is_ok(),
                    2 => from_bytes::<VSISVerificationKey>(&bytes).is_ok(),
                    3 => from_bytes::<VSISTape>(&bytes).is_ok(),
                    4 => from_bytes::<VSISPreCredential>(&bytes).is_ok(),
                    _ => match from_bytes::<VSISCredential>(&bytes) {
                        Ok(cred) => {
                            assert!(!VSIS::verify(&pp, &vk, &usk, &cred));
                            true
                        }
                        Err(_) => false,
                    },
                };
                if ok {
                    assert_eq!(delta, 1, "only the exact length decodes");
                    decoded[k] += 1;
                }
            }
        }
    }
    // random trapdoors never validate; a masked (pre-)credential decodes unless one of its
    // 2048 coefficients of s is the code -2^19 (probability 2048 / 2^20 ≈ 0.2%), so about 31.9
    // of the 32; random R_q bytes decode with probability (q / 2^20)^1024 ≈ 0.9971 per element
    assert_eq!(decoded[1], 0);
    assert!(decoded[4] >= 28 && decoded[5] >= 28, "{decoded:?}");
    assert!(decoded[2] >= 56, "{decoded:?}");
    // canonical values decode whatever the Validate flag says
    let bytes = to_bytes(&vk).unwrap();
    let unchecked = VSISVerificationKey::deserialize_with_mode(
        &bytes[..],
        ark_serialize::Compress::Yes,
        ark_serialize::Validate::No,
    )
    .unwrap();
    assert_eq!(unchecked, vk);
    let mut bad = bytes;
    bad[0] = 0xff;
    bad[1] = 0xff;
    bad[2] |= 0x0f; // coefficient 0 = 2^20 − 1 ≥ q
    assert!(
        VSISVerificationKey::deserialize_with_mode(
            &bad[..],
            ark_serialize::Compress::Yes,
            ark_serialize::Validate::No,
        )
        .is_err()
    );
}
