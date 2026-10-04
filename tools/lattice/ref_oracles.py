#!/usr/bin/env python3
"""Independent reference (Python hashlib) for the byte-level oracles of the lattice PCS.

Specification: docs/encodings.md, "Lattice instantiation (feature `lattice`)". Used to pin known
answers in the Rust unit tests (src/lattice/xof.rs; src/lattice/oracles.rs pins H_mat / H_0 /
c_0 / EncPred against the same functions).

    python3 tools/lattice/ref_oracles.py            # prints the known answers
"""
import hashlib
import struct

DOMAIN_PREFIX = b"PCS-V1"
PP_SUFFIX = b"/LATTICE-PP"
HMAT_SUFFIX = b"/LATTICE-HMAT"
PREDENC_SUFFIX = b"/LATTICE-PREDENC"
JALI_SEED_SUFFIX = b"/LATTICE-JALI-SEED"

D = 1024
Q = 1_048_573
Q_T = 983_040
M = 168


def frame(label: bytes, data: bytes) -> bytes:
    return struct.pack("<Q", len(label)) + label + struct.pack("<Q", len(data)) + data


def xof_input(suffix: bytes, items) -> bytes:
    out = frame(b"dst", DOMAIN_PREFIX + suffix)
    for label, data in items:
        out += frame(label, data)
    return out


def stream(suffix: bytes, items, nbytes: int) -> bytes:
    return hashlib.shake_128(xof_input(suffix, items)).digest(nbytes)


def uniform_20(data: bytes, modulus: int, count: int):
    """Consecutive 20-bit little-endian chunks of the little-endian bit string `data`,
    accepted when below `modulus`."""
    assert (1 << 19) < modulus <= (1 << 20)
    bits = int.from_bytes(data, "little")
    out = []
    i = 0
    total = len(data) * 8
    while len(out) < count:
        assert (i + 1) * 20 <= total, "not enough stream"
        chunk = (bits >> (20 * i)) & 0xFFFFF
        i += 1
        if chunk < modulus:
            out.append(chunk)
    return out


def pp_element(deployment: bytes, name: bytes):
    data = stream(PP_SUFFIX, [(b"deployment", deployment), (b"element", name)], 4096)
    return uniform_20(data, Q, D)


def jali_pp_seed(deployment: bytes) -> bytes:
    return stream(JALI_SEED_SUFFIX, [(b"deployment", deployment)], 32)


def h_mat(deployment: bytes, y: bytes):
    """m x n matrix over Z_{q_t}, row-major."""
    nbytes = 600_000  # 5 * ceil(m n / (2 * 0.9375)) with margin
    data = stream(HMAT_SUFFIX, [(b"deployment", deployment), (b"input", y)], nbytes)
    return uniform_20(data, Q_T, M * D)


def h0(deployment: bytes, x: bytes):
    return h_mat(deployment, b"tag" + x)


def identity_point(deployment: bytes):
    return h0(deployment, b"identity")


def predicate_bytes(threshold: int, label: bytes) -> bytes:
    """<f> = LE32(threshold) || LE64(len(label)) || label (Predicate::canonical_bytes)."""
    return struct.pack("<I", threshold) + struct.pack("<Q", len(label)) + label


def pred_enc(deployment: bytes, threshold: int, label: bytes) -> bytes:
    """128 bytes; bit i (LSB first) is coefficient i of phi."""
    y = b"predicate" + predicate_bytes(threshold, label)
    return stream(PREDENC_SUFFIX, [(b"deployment", deployment), (b"input", y)], D // 8)


if __name__ == "__main__":
    dep = b"PCS-LATTICE-KAT"
    print("xof_input(PP, v) hex prefix:", xof_input(PP_SUFFIX, [(b"deployment", dep), (b"element", b"v")]).hex())
    print("jali_pp_seed:", jali_pp_seed(dep).hex())
    for name in [b"v", b"b_u", b"b_phi", b"B_r[0]", b"B_r[1]"]:
        e = pp_element(dep, name)
        print(f"pp {name.decode()}: first 4 = {e[:4]}, last = {e[-1]}, sum mod 2^32 = {sum(e) % (1 << 32)}")
    c0 = identity_point(dep)
    print(f"c0: first 4 = {c0[:4]}, row 167 last = {c0[-1]}, sum mod 2^32 = {sum(c0) % (1 << 32)}")
    phi = pred_enc(dep, 5, b"members")
    print("pred_enc(5, members) first 16 bytes:", phi[:16].hex())
    raw = stream(PP_SUFFIX, [(b"deployment", dep), (b"element", b"v")], 10)
    print("pp v raw stream first 10 bytes:", raw.hex())
