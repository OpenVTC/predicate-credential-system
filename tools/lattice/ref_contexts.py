#!/usr/bin/env python3
"""Independent reference (Python hashlib) for the digest of the public parameters of the lattice
backend and for its identifier and recipient points: `PublicParameters::<LatticeBackend>::digest`
(src/pcreds/context.rs over the encoding of `LatticeParams`, src/pcreds/lattice/mod.rs), the
`H_id` transcript of `Protocol::identifier_point` and the `H_req` transcript of
`Protocol::recipient_point` (src/pcreds/context.rs).

Reuses the oracle reference ref_oracles.py (same directory) for pp_Sigma and Jali's pp_seed, and
reads the embedded parameter sets from src/lattice/sets/ of this repository. By default it
computes the values of the default, extractable build, whose encoding of `LatticeParams` ends with
the argument system and the pins of the extraction sets, and with --plain those of the plain build
(feature `lattice-plain`). The Rust unit
test `pcreds::lattice::tests::known_answers_of_the_digest_and_the_points` pins the output of the
build it runs in.

    python3 tools/lattice/ref_contexts.py [--plain]
"""
import argparse
import hashlib
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ref_oracles as ro  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
JALI_VERSION = b"0.3.0"
PLACEMENT = b"R_att:s=bdlop;R_Possess:s=bdlop"
ARGUMENT = b"jali-extractable:rom"
SETS = ["tag-beta443", "att-lr3-beta439", "iss-lr3-beta439", "possess-lr3-beta439"]
# format version 3, d, q, gamma, p, q_t, m, floor(gamma/2), e_deg, beta_u, beta_x, beta_r, ell_r,
# floor(beta_s^2), the proof degree, Q_max
FORMAT = [3, 1024, 1_048_573, 15, 65_536, 983_040, 168, 7, 128, 1, 1, 1, ro.ELL_R, 90_803_788_942,
          128, 1 << 48]


def frame(label: bytes, data: bytes) -> bytes:
    return struct.pack("<Q", len(label)) + label + struct.pack("<Q", len(data)) + data


def transcript(suffix: bytes, items) -> bytes:
    h = hashlib.sha256()
    h.update(frame(b"dst", b"PCS-V1" + suffix))
    for label, data in items:
        h.update(frame(label, data))
    return h.digest()


def pack20(values) -> bytes:
    """20-bit little-endian packing (Rq::to_bytes)."""
    acc = 0
    for i, v in enumerate(values):
        assert 0 <= v < (1 << 20)
        acc |= v << (20 * i)
    n = (20 * len(values) + 7) // 8
    return acc.to_bytes(n, "little")


def vec_bytes(data: bytes) -> bytes:
    """The canonical encoding of a Vec<u8> in arkworks: LE64(len) || bytes."""
    return struct.pack("<Q", len(data)) + data


def pins(kind: str) -> bytes:
    """The SHA-256 pins of the embedded files `<kind>-<name>.json`, in the order of SETS."""
    out = b""
    for name in SETS:
        with open(f"{ROOT}/src/lattice/sets/{kind}-{name}.json", "rb") as f:
            out += hashlib.sha256(f.read()).digest()
    return out


def lattice_params(deployment: bytes, extractable: bool = False) -> bytes:
    """The canonical encoding of LatticeParams for the deployment label, of the plain build or of
    the extractable one."""
    sigma = b"".join(pack20(ro.pp_element(deployment, name)) for name in ro.pp_names())
    assert len(sigma) == (2 + ro.ELL_R) * 2560
    out = (
        vec_bytes(deployment)
        + b"".join(struct.pack("<Q", w) for w in FORMAT)
        + sigma
        + ro.jali_pp_seed(deployment)
        + pins("params")
        + vec_bytes(JALI_VERSION)
        + vec_bytes(PLACEMENT)
    )
    if extractable:
        out += vec_bytes(ARGUMENT) + pins("extraction")
    return out


def pp_digest(deployment: bytes, extractable: bool = False) -> bytes:
    """PublicParameters::digest: label, backend name, params."""
    return transcript(
        b"/PCREDS-PP",
        [
            (b"label", deployment),
            (b"backend", b"vSIS+LWR"),
            (b"params", lattice_params(deployment, extractable)),
        ],
    )


def identifier_digest(pp: bytes, hvk: bytes) -> bytes:
    """The digest d of x_0 = H_id(<hvk>) = H_mat("hid" || d)."""
    return transcript(b"/PCREDS-HID", [(b"pp", pp), (b"hvk", hvk)])


def recipient_digest(pp: bytes, hvk: bytes, ident: bytes, counter: int = 0) -> bytes:
    """The digest d of x_Q = H_req(<pp, hvk, id_Q, j_Q>) = H_mat("req" || d)."""
    return transcript(
        b"/PCREDS-HREQ",
        [(b"pp", pp), (b"hvk", hvk), (b"id", ident), (b"counter", struct.pack("<Q", counter))],
    )


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="known answers of the lattice backend's contexts")
    ap.add_argument("--plain", action="store_true",
                    help="the values of the plain build (feature lattice-plain)")
    a = ap.parse_args()
    extractable = not a.plain
    dep = b"PCS-LATTICE-KAT"
    params = lattice_params(dep, extractable)
    print("build:", "extractable" if extractable else "plain")
    print("LatticeParams encoding: %d bytes, sha256 %s" % (len(params), hashlib.sha256(params).hexdigest()))
    d = pp_digest(dep, extractable)
    print("pp digest (PCS-LATTICE-KAT):", d.hex())
    # the fixed inputs of the known answer (the Rust test builds the same values)
    hvk = pack20([5] * 1024)               # h = 5 + 5X + ... (every coefficient 5)
    ident = bytes(range(256)) + bytes(80)  # an identifier of 336 bytes
    print("identifier digest:", identifier_digest(d, hvk).hex())
    print("recipient digest (counter 0):", recipient_digest(d, hvk, ident).hex())
