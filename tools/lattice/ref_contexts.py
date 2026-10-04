#!/usr/bin/env python3
"""Independent reference (Python hashlib) for the digest of the lattice pp and the contexts of
the lattice construction (src/pcs/lattice/context.rs).

Reuses the oracle reference ref_oracles.py (same directory) for pp_Sigma, c_0 and Jali's
pp_seed, and reads the embedded parameter sets from src/lattice/sets/ of this repository.

    python3 tools/lattice/ref_contexts.py
"""
import hashlib
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ref_oracles as ro  # noqa: E402

PCS = os.path.normpath(os.path.join(HERE, "..", ".."))
JALI_REVISION = b"0cd24f38bd84e2e48d2dcb63f34d2d17cba2a90d"


def frame(label: bytes, data: bytes) -> bytes:
    return struct.pack("<Q", len(label)) + label + struct.pack("<Q", len(data)) + data


def transcript(suffix: bytes, items) -> bytes:
    h = hashlib.sha256()
    h.update(frame(b"dst", b"PCS-V1" + suffix))
    for label, data in items:
        h.update(frame(label, data))
    return h.digest()


def pack20(values) -> bytes:
    """20-bit little-endian packing (Rq::to_bytes, TagMatrix::to_bytes)."""
    acc = 0
    for i, v in enumerate(values):
        assert 0 <= v < (1 << 20)
        acc |= v << (20 * i)
    n = (20 * len(values) + 7) // 8
    return acc.to_bytes(n, "little")


def pp_digest(deployment: bytes) -> bytes:
    fmt = [1, 1024, 1_048_573, 15, 65_536, 983_040, 168, 7, 128, 1, 1, 1, 2, 90_803_788_942, 128]
    pp_sigma = b"".join(
        pack20(ro.pp_element(deployment, name))
        for name in [b"v", b"b_u", b"b_phi", b"B_r[0]", b"B_r[1]"]
    )
    assert len(pp_sigma) == 12_800
    c0 = pack20(ro.identity_point(deployment))
    assert len(c0) == 430_080
    sets = b""
    for name in ["att", "issue", "issue-root"]:
        with open(f"{PCS}/src/lattice/sets/params-{name}-beta439.json", "rb") as f:
            sets += hashlib.sha256(f.read()).digest()
    return transcript(
        b"/LATTICE-PP-DIGEST",
        [
            (b"label", deployment),
            (b"format", b"".join(struct.pack("<Q", w) for w in fmt)),
            (b"pp-sigma", pp_sigma),
            (b"c0", c0),
            (b"jali-pp-seed", ro.jali_pp_seed(deployment)),
            (b"jali-sets", sets),
            (b"jali", JALI_REVISION),
            (b"placement", b"R_att:s=bdlop"),
        ],
    )


def ctx(suffix: bytes, digest: bytes, hvk: bytes, items) -> bytes:
    return transcript(suffix, [(b"pp", digest), (b"hvk", hvk)] + items)


def att_bytes(tag: bytes, phi: bytes, proof: bytes) -> bytes:
    return tag + phi + struct.pack("<I", len(proof)) + proof


if __name__ == "__main__":
    dep = b"PCS-LATTICE-KAT"
    d = pp_digest(dep)
    print("pp digest (PCS-LATTICE-KAT):", d.hex())
    # the fixed inputs of the context known answers (the Rust test builds the same values)
    hvk = pack20([5] * 1024)             # h = 5 + 5X + ... (every coefficient 5)
    c = pack20([7] * 1024)               # C, every coefficient 7
    tag_id = bytes(range(256)) + bytes(80)          # 336 bytes
    tag_t = bytes([0x11]) * 336
    tag_t0 = bytes([0x22]) * 336
    phi = bytes([0x5A]) * 128
    f = struct.pack("<I", 2) + struct.pack("<Q", 7) + b"members"
    f_root = struct.pack("<I", 0) + struct.pack("<Q", 8) + b"founders"
    print("ctx_j:", ctx(b"/LATTICE-CTX-ATT", d, hvk,
                        [(b"id", tag_id), (b"phi", phi), (b"T", tag_t), (b"cred*", b"")]).hex())
    print("ctx_0:", ctx(b"/LATTICE-CTX-ISSUE", d, hvk,
                        [(b"f", f), (b"id", tag_id), (b"C", c), (b"T0", tag_t0),
                         (b"att", att_bytes(tag_t, phi, b"\x01\x02\x03"))]).hex())
    print("ctx_root:", ctx(b"/LATTICE-CTX-ROOT", d, hvk,
                           [(b"f", f_root), (b"id", tag_id), (b"C", c), (b"T0", tag_t0)]).hex())
