//! Integration tests of the credential base `Σ-vSIS` (`cred::VSIS`, building-blocks.tex
//! sec:inst-base-vsis) through the PUBLIC API only, with ONE real helper key per test (TrapGen of
//! `ntru-trapdoor`, about 6 ms): the encoded-issuance flow of Def. "Credential base" in code that
//! is generic over [`CredentialBase`], the wire sizes of every base object, the helper secret key
//! `HelperSecretKey<VSIS>` with the issuance counter of the cap $`Q_{\max}`$, and decoders fed
//! with arbitrary bytes. The unit tests of `cred::vsis` cover the algorithms in detail.
//!
//! Fast: nothing here runs a Jali proof.

#![cfg(feature = "lattice")]
#![allow(clippy::upper_case_acronyms)] // naming policy: see src/lib.rs

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use predicate_credential_system::{
    Error,
    cred::{
        CredentialBase, VSIS,
        vsis::{
            VSISCredential, VSISHiddenMessage, VSISIssuanceState, VSISPublicParams, VSISSigningKey,
            VSISVerificationKey,
        },
    },
    lattice::{BinaryPoly, Q_MAX, Rq, S_BOUND, Ternary},
    pcs::HelperSecretKey,
    serialization::{WireFormat, from_bytes, to_bytes},
};
use rand::{RngCore, SeedableRng, rngs::StdRng};

const LABEL: &[u8] = b"PCS-VSIS-INTEGRATION";

/// The encoded-issuance flow (Def. "Credential base", correctness) for ANY base: the user
/// commits, the signer issues blindly, the user unblinds and verifies.
fn encoded_issuance<B: CredentialBase, R: RngCore + rand::CryptoRng>(
    pp: &B::PublicParams,
    vk: &B::VerificationKey,
    sk: &B::SigningKey,
    m_hid: &B::HiddenMessage,
    m_pub: &B::PublicMessage,
    r: &B::IssuanceState,
    rng: &mut R,
) -> Result<(B::Message, B::Credential), Error> {
    let c = B::issuance_encoding(pp, vk, m_hid, m_pub, r)?;
    let c = from_bytes::<B::IssuanceEncoding>(&to_bytes(&c)?)?; // over the wire
    let pre = B::blind_issue(pp, sk, &c, m_pub, rng)?;
    let pre = from_bytes::<B::PreCredential>(&to_bytes(&pre)?)?; // over the wire
    let m = B::encode_message(pp, m_hid, m_pub)?;
    let cred = B::unblind(pp, vk, &m, &pre, r)?;
    assert!(B::verify(pp, vk, &m, &cred));
    Ok((m, cred))
}

fn message(rng: &mut StdRng) -> (VSISHiddenMessage, BinaryPoly, VSISIssuanceState) {
    let usk = Ternary::sample(rng);
    let x0 = [Ternary::sample(rng), Ternary::sample(rng)];
    let mut phi = [0u8; BinaryPoly::BYTES];
    rng.fill_bytes(&mut phi);
    (
        VSISHiddenMessage::new(usk, x0.clone()),
        BinaryPoly::from_bytes(phi),
        VSISIssuanceState::new(x0),
    )
}

#[test]
fn encoded_issuance_and_signing_through_the_public_api() {
    let mut rng = StdRng::seed_from_u64(0x7515_0001);
    let pp = VSIS::setup(LABEL).unwrap();
    let (vk, sk) = VSIS::keygen(&pp, &mut rng);
    assert!(VSIS::is_well_formed_key(&pp, &vk));
    let (m_hid, phi, r) = message(&mut rng);
    let (m, cred) = encoded_issuance::<VSIS, _>(&pp, &vk, &sk, &m_hid, &phi, &r, &mut rng).unwrap();
    assert!(cred.norm_sq() <= S_BOUND);
    let signed = VSIS::sign(&pp, &sk, &m, &mut rng).unwrap();
    assert!(VSIS::verify(&pp, &vk, &m, &signed));
    let ((), omega) = VSIS::rerand(&pp, &vk, &m, &signed, &mut rng).unwrap();
    assert_eq!(omega, signed);
    assert_eq!((sk.issued(), sk.remaining()), (2, Q_MAX - 2));
    // the credential of one key does not verify under another
    let (vk2, _) = VSIS::keygen(&pp, &mut rng);
    assert!(!VSIS::verify(&pp, &vk2, &m, &cred));
}

/// The sizes of design §5.4 / §11, which the construction's codec builds on.
#[test]
fn wire_sizes_of_the_base_objects() {
    let mut rng = StdRng::seed_from_u64(0x7515_0002);
    let pp = VSIS::setup(LABEL).unwrap();
    let (vk, sk) = VSIS::keygen(&pp, &mut rng);
    let (m_hid, phi, r) = message(&mut rng);
    let c = VSIS::issuance_encoding(&pp, &vk, &m_hid, &phi, &r).unwrap();
    let pre = VSIS::blind_issue(&pp, &sk, &c, &phi, &mut rng).unwrap();
    let sizes = [
        (
            pp.to_bytes().unwrap().len(),
            VSISPublicParams::BYTES,
            12_800,
        ),
        (to_bytes(&sk).unwrap().len(), VSISSigningKey::BYTES, 5_897),
        (
            vk.to_bytes().unwrap().len(),
            VSISVerificationKey::BYTES,
            2_560,
        ),
        (to_bytes(&c).unwrap().len(), Rq::BYTES, 2_560),
        (to_bytes(&r).unwrap().len(), VSISIssuanceState::BYTES, 512),
        (pre.to_bytes().unwrap().len(), VSISCredential::BYTES, 5_376),
        (phi.to_bytes().unwrap().len(), BinaryPoly::BYTES, 128),
    ];
    for (actual, constant, expected) in sizes {
        assert_eq!((actual, constant), (expected, expected));
    }
    // serialized_size agrees with the bytes written
    assert_eq!(pp.compressed_size(), 12_800);
    assert_eq!(sk.compressed_size(), 5_897);
    assert_eq!(pre.compressed_size(), 5_376);
    // round trips
    assert_eq!(
        VSISPublicParams::from_bytes(&pp.to_bytes().unwrap()).unwrap(),
        pp
    );
    assert_eq!(
        VSISVerificationKey::from_bytes(&vk.to_bytes().unwrap()).unwrap(),
        vk
    );
    assert_eq!(
        VSISCredential::from_bytes(&pre.to_bytes().unwrap()).unwrap(),
        pre
    );
}

/// `hsk = (sk, hvk)` with the parameter digest: 5897 + 2560 + 32 = 8489 bytes; the issuance
/// counter travels with it, and a decoded key signs under the same `hvk`.
#[test]
fn the_helper_secret_key_carries_the_issuance_count() {
    let mut rng = StdRng::seed_from_u64(0x7515_0003);
    let pp = VSIS::setup(LABEL).unwrap();
    let (vk, sk) = VSIS::keygen(&pp, &mut rng);
    let (m_hid, phi, r) = message(&mut rng);
    let c = VSIS::issuance_encoding(&pp, &vk, &m_hid, &phi, &r).unwrap();
    let hsk = HelperSecretKey::<VSIS>::new(sk, vk.clone(), [7; 32]);
    for _ in 0..5 {
        VSIS::blind_issue(&pp, hsk.signing_key(), &c, &phi, &mut rng).unwrap();
    }
    let bytes = hsk.to_bytes().unwrap();
    assert_eq!(bytes.len(), 8_489);
    let back = from_bytes::<HelperSecretKey<VSIS>>(&bytes).unwrap();
    assert_eq!(back.verification_key(), &vk);
    assert_eq!(back.parameters_digest(), &[7; 32]);
    assert_eq!(back.signing_key().issued(), 5);
    assert_eq!(back.signing_key().verification_key().unwrap(), vk);
    let m = VSIS::encode_message(&pp, &m_hid, &phi).unwrap();
    let pre = VSIS::blind_issue(&pp, back.signing_key(), &c, &phi, &mut rng).unwrap();
    assert!(VSIS::unblind(&pp, &vk, &m, &pre, &r).is_ok());
    assert_eq!(back.signing_key().issued(), 6);
    assert_eq!(format!("{back:?}"), "HelperSecretKey(<redacted>)");
}

/// The cap (construction.tex, "Issuance cap"): a key stored with Q_max − 1 calls used answers
/// once more, then refuses, also after another round trip; a stored count above Q_max is no key.
#[test]
fn a_key_restored_near_the_cap_answers_once_more() {
    let mut rng = StdRng::seed_from_u64(0x7515_0004);
    let pp = VSIS::setup(LABEL).unwrap();
    let (vk, sk) = VSIS::keygen(&pp, &mut rng);
    let (m_hid, phi, r) = message(&mut rng);
    let c = VSIS::issuance_encoding(&pp, &vk, &m_hid, &phi, &r).unwrap();
    let mut bytes = to_bytes(&sk).unwrap();
    let count = bytes.len() - 8;
    bytes[count..].copy_from_slice(&(Q_MAX - 1).to_le_bytes());
    let restored: VSISSigningKey = from_bytes(&bytes).unwrap();
    assert_eq!(restored.remaining(), 1);
    assert!(VSIS::blind_issue(&pp, &restored, &c, &phi, &mut rng).is_ok());
    assert_eq!(
        VSIS::blind_issue(&pp, &restored, &c, &phi, &mut rng).unwrap_err(),
        Error::IssuanceCapReached
    );
    let m = VSIS::encode_message(&pp, &m_hid, &phi).unwrap();
    assert_eq!(
        VSIS::sign(&pp, &restored, &m, &mut rng).unwrap_err(),
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
    let pp = VSIS::setup(LABEL).unwrap();
    let (vk, sk) = VSIS::keygen(&pp, &mut rng);
    let mut bytes = to_bytes(&sk).unwrap();
    let count = bytes.len() - 8;
    bytes[count..].copy_from_slice(&(Q_MAX - 10).to_le_bytes());
    let sk: VSISSigningKey = from_bytes(&bytes).unwrap();
    let (m_hid, phi, r) = message(&mut rng);
    let c = VSIS::issuance_encoding(&pp, &vk, &m_hid, &phi, &r).unwrap();
    let issued: usize = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..16u64)
            .map(|i| {
                let (pp, sk, c, phi) = (&pp, &sk, &c, &phi);
                scope.spawn(move || {
                    let mut rng = StdRng::seed_from_u64(1000 + i);
                    (0..3)
                        .filter(|_| match VSIS::blind_issue(pp, sk, c, phi, &mut rng) {
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
    let pp = VSIS::setup(LABEL).unwrap();
    let (vk, _) = VSIS::keygen(&pp, &mut rng);
    let (m_hid, phi, _) = message(&mut rng);
    let m = VSIS::encode_message(&pp, &m_hid, &phi).unwrap();
    let mut decoded = [0usize; 5];
    for round in 0..64 {
        let lengths = [
            VSISPublicParams::BYTES,
            VSISSigningKey::BYTES,
            VSISVerificationKey::BYTES,
            VSISIssuanceState::BYTES,
            VSISCredential::BYTES,
        ];
        for (k, &len) in lengths.iter().enumerate() {
            for delta in [0usize, 1, 2] {
                let mut bytes = vec![0u8; len + delta - 1];
                rng.fill_bytes(&mut bytes);
                if k == 1 && !bytes.is_empty() {
                    bytes[0] = 0xAA; // past the header check, into the trapdoor validation
                }
                if round % 2 == 0 && k == 4 {
                    // past the ternary check of x_1: every 2-bit code 10 becomes 00
                    let x1 = len - Ternary::BYTES;
                    for byte in bytes.iter_mut().skip(x1).take(Ternary::BYTES) {
                        for shift in [0, 2, 4, 6] {
                            if (*byte >> shift) & 3 == 2 {
                                *byte &= !(3 << shift);
                            }
                        }
                    }
                }
                let ok = match k {
                    0 => from_bytes::<VSISPublicParams>(&bytes).is_ok(),
                    1 => from_bytes::<VSISSigningKey>(&bytes).is_ok(),
                    2 => from_bytes::<VSISVerificationKey>(&bytes).is_ok(),
                    3 => from_bytes::<VSISIssuanceState>(&bytes).is_ok(),
                    _ => match from_bytes::<VSISCredential>(&bytes) {
                        Ok(cred) => {
                            assert!(!VSIS::verify(&pp, &vk, &m, &cred));
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
    // random trapdoors never validate; a masked credential decodes unless one of its 2048
    // coefficients is the code -2^19 (probability 2048 / 2^20 ≈ 0.2%), so about 31.9 of the 32;
    // random R_q bytes decode with probability (q / 2^20)^1024 ≈ 0.9971 per element
    assert_eq!(decoded[1], 0);
    assert!(decoded[4] >= 28, "{decoded:?}");
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
