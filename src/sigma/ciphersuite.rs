//! The ciphersuite identifiers that enter the tag of a Fiat–Shamir proof.
//!
//! `draft-irtf-cfrg-sigma-protocols-04` ("Sigma -04") defines its non-interactive argument over
//! ONE prime-order group, and §5.1 requires the tag to contain the flavor marker and the
//! ciphersuite identifier of §8 verbatim. Its only pairing-friendly ciphersuite is
//! `sigma-proofs_Shake128_BLS12381`: the group `G_1` of BLS12-381 with the codecs of §8.2 and the
//! SHAKE128 duplex sponge of `draft-irtf-cfrg-fiat-shamir-04`. Every other relation this crate
//! proves is outside the draft and carries an identifier of this crate, which never contains the
//! draft's identifier:
//!
//! | the relation | identifier | defined by |
//! |---|---|---|
//! | equations over `G_1` of BLS12-381 only ([`GroupRelation`] over `G_1`, a [`PairingRelation`] without `G_2` and `G_T` equations) | `sigma-proofs_Shake128_BLS12381` | Sigma -04 §8.2 |
//! | equations over `G_2` of BLS12-381 only ([`GroupRelation`]) | `pcs-sigma-group_Shake128_BLS12381G2` | this crate |
//! | equations over `G_T` of BLS12-381 only ([`GroupRelation`]) | `pcs-sigma-group_Shake128_BLS12381GT` | this crate |
//! | equations over one group of another curve | `pcs-sigma-group_Shake128_G` and 32 hexadecimal digits | this crate |
//! | a [`PairingRelation`] over BLS12-381 with a `G_2` or a `G_T` equation (the extension, [`crate::sigma::relation`]) | `pcs-sigma-pairing_Shake128_BLS12381` | this crate |
//! | the same over another pairing | `pcs-sigma-pairing_Shake128_E` and 32 hexadecimal digits | this crate |
//!
//! The single-group relations over other groups follow the draft byte for byte (the same
//! `SerializeLinearRelation`, `DeriveChallenge` and compact NARG string) with that group's codec
//! ([`crate::sigma::codec`]). Only the identifier differs.
//!
//! The groups of BLS12-381 are recognized by their arkworks types (`ark_bls12_381`). A group of
//! any other type is named by a digest of its public description: the hexadecimal digits are
//! the first 16 bytes of `DeriveSessionID(desc)` (`draft-irtf-cfrg-fiat-shamir-04`, §5.1), for
//!
//! ```text
//! desc(G) = "PCS-V01 group" ‖ LE(N_s, 4) ‖ I2OSP(p, N_s) ‖ LE(N_e, 4) ‖ serialize(generator)
//! desc(E) = "PCS-V01 pairing" ‖ desc(G_1) ‖ desc(G_2) ‖ LE(N_e of G_T, 4)
//! ```
//!
//! with the order `p` of the group, `N_s` and `N_e` the lengths of a scalar and of an element and
//! `serialize` the codec of the group. Tests use this for BN254, which is not a supported
//! deployment.
//!
//! [`GroupRelation`]: crate::sigma::GroupRelation
//! [`PairingRelation`]: crate::sigma::PairingRelation

use core::any::TypeId;

use ark_bls12_381::{Bls12_381, G1Projective, G2Projective};
use ark_ec::{
    PrimeGroup,
    pairing::{Pairing, PairingOutput},
};
use ark_ff::{BigInteger, PrimeField};

use super::codec::{element_len, scalar_len};
use crate::hash::duplex_sponge::derive_session_id;

/// The ciphersuite identifier of Sigma -04 §8.2: `G_1` of BLS12-381, SHAKE128.
pub const SIGMA_BLS12381: &str = "sigma-proofs_Shake128_BLS12381";

/// The prefix of this crate's identifiers of single-group relations outside the draft.
pub const GROUP_PREFIX: &str = "pcs-sigma-group_Shake128_";

/// The prefix of this crate's identifiers of the pairing extension.
pub const PAIRING_PREFIX: &str = "pcs-sigma-pairing_Shake128_";

fn same_type<A: 'static, B: 'static>() -> bool {
    TypeId::of::<A>() == TypeId::of::<B>()
}

/// The identifier of a single-group relation over `G` (module docs).
#[must_use]
pub fn group_suite<G: PrimeGroup>() -> String {
    if same_type::<G, G1Projective>() {
        SIGMA_BLS12381.to_owned()
    } else if same_type::<G, G2Projective>() {
        format!("{GROUP_PREFIX}BLS12381G2")
    } else if same_type::<G, PairingOutput<Bls12_381>>() {
        format!("{GROUP_PREFIX}BLS12381GT")
    } else {
        let mut desc = b"PCS-V01 group".to_vec();
        describe_group::<G>(&mut desc);
        format!("{GROUP_PREFIX}G{}", digest_hex(&desc))
    }
}

/// The identifier of a relation of the pairing extension over `E` (module docs).
#[must_use]
pub fn pairing_suite<E: Pairing>() -> String {
    if same_type::<E, Bls12_381>() {
        format!("{PAIRING_PREFIX}BLS12381")
    } else {
        let mut desc = b"PCS-V01 pairing".to_vec();
        describe_group::<E::G1>(&mut desc);
        describe_group::<E::G2>(&mut desc);
        desc.extend_from_slice(&len4(element_len::<PairingOutput<E>>()));
        format!("{PAIRING_PREFIX}E{}", digest_hex(&desc))
    }
}

/// `LE(N_s, 4) ‖ I2OSP(p, N_s) ‖ LE(N_e, 4) ‖ serialize(generator)`.
fn describe_group<G: PrimeGroup>(desc: &mut Vec<u8>) {
    let ns = scalar_len::<G::ScalarField>();
    desc.extend_from_slice(&len4(ns));
    let modulus = G::ScalarField::MODULUS.to_bytes_be();
    desc.extend_from_slice(&modulus[modulus.len() - ns..]);
    desc.extend_from_slice(&len4(element_len::<G>()));
    // arkworks encodes every point of its groups. A failure would leave the description shorter,
    // which still names the type deterministically
    let _ = G::generator().serialize_compressed(&mut *desc);
}

/// A length as `LE(n, 4)`, saturated (lengths of encodings are far below `2^32`).
fn len4(n: usize) -> [u8; 4] {
    u32::try_from(n).unwrap_or(u32::MAX).to_le_bytes()
}

/// The first 16 bytes of `DeriveSessionID(desc)`, as 32 lower-case hexadecimal digits.
fn digest_hex(desc: &[u8]) -> String {
    derive_session_id(desc)[..16]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_serialize::CanonicalSerialize;

    use super::*;

    #[test]
    fn the_groups_of_bls12_381_have_their_names() {
        assert_eq!(
            group_suite::<G1Projective>(),
            "sigma-proofs_Shake128_BLS12381"
        );
        assert_eq!(
            group_suite::<G2Projective>(),
            "pcs-sigma-group_Shake128_BLS12381G2"
        );
        assert_eq!(
            group_suite::<PairingOutput<Bls12_381>>(),
            "pcs-sigma-group_Shake128_BLS12381GT"
        );
        assert_eq!(
            pairing_suite::<Bls12_381>(),
            "pcs-sigma-pairing_Shake128_BLS12381"
        );
    }

    /// The draft's identifier is claimed for `G_1` of BLS12-381 alone, and the identifiers of this
    /// crate never contain it.
    #[test]
    fn only_g1_of_bls12_381_claims_the_draft_identifier() {
        let others = [
            group_suite::<G2Projective>(),
            group_suite::<PairingOutput<Bls12_381>>(),
            group_suite::<<Bn254 as Pairing>::G1>(),
            group_suite::<<Bn254 as Pairing>::G2>(),
            pairing_suite::<Bls12_381>(),
            pairing_suite::<Bn254>(),
        ];
        for id in &others {
            assert!(!id.contains(SIGMA_BLS12381), "{id}");
            assert!(id.is_ascii() && !id.contains("-ctx-"), "{id}");
        }
        // pairwise distinct
        for (i, a) in others.iter().enumerate() {
            for b in &others[i + 1..] {
                assert_ne!(a, b);
            }
        }
        // the generic names are digests of the descriptions: fixed length, deterministic
        let bn = group_suite::<<Bn254 as Pairing>::G1>();
        assert_eq!(bn.len(), GROUP_PREFIX.len() + 1 + 32);
        assert_eq!(bn, group_suite::<<Bn254 as Pairing>::G1>());
        assert!(pairing_suite::<Bn254>().starts_with("pcs-sigma-pairing_Shake128_E"));
    }

    /// The draft's identifier names the group whose generator §8.2.1 prints, with 48-byte elements
    /// and the order of §8.2.1: arkworks' `G_1` encodes exactly that.
    #[test]
    fn g1_of_arkworks_is_the_group_of_section_8_2_1() {
        let mut generator = Vec::new();
        G1Projective::generator()
            .serialize_compressed(&mut generator)
            .unwrap();
        let hex: String = generator.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
        );
        assert_eq!(element_len::<G1Projective>(), 48);
        assert_eq!(
            scalar_len::<<G1Projective as PrimeGroup>::ScalarField>(),
            32
        );
        // order() of §8.2.1, in decimal
        assert_eq!(
            <G1Projective as PrimeGroup>::ScalarField::MODULUS.to_string(),
            "52435875175126190479447740508185965837690552500527637822603658699938581184513"
        );
    }
}
