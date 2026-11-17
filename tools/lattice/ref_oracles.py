#!/usr/bin/env python3
"""Independent reference (Python hashlib) for the byte-level oracles of the lattice backend.

Specification: docs/encodings.md, "Lattice instantiation (feature `lattice`)". Used to pin known
answers in the Rust unit tests (src/lattice/xof.rs; src/lattice/oracles.rs pins H_mat, H_id and
H_req against the same functions).

    python3 tools/lattice/ref_oracles.py            # prints the known answers
"""
import hashlib
import struct

DOMAIN_PREFIX = b"PCS-V1"
PP_SUFFIX = b"/LATTICE-PP"
HMAT_SUFFIX = b"/LATTICE-HMAT"
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


def identifier_point(deployment: bytes, digest: bytes):
    """x_0 = H_id(<hvk>) = H_mat("hid" || d) for the 32-byte digest d of the protocol's
    H_id transcript."""
    assert len(digest) == 32
    return h_mat(deployment, b"hid" + digest)


def request_point(deployment: bytes, digest: bytes):
    """x_Q = H_mat("req" || d) for a 32-byte transcript digest d."""
    assert len(digest) == 32
    return h_mat(deployment, b"req" + digest)


# ell_r, the number of columns of B_r (lattice::ELL_R)
ELL_R = 3


def pp_names():
    """The element names of pp_Sigma in the order of its encoding: v, b_u, B_r[0..ell_r]."""
    return [b"v", b"b_u"] + [b"B_r[%d]" % k for k in range(ELL_R)]


if __name__ == "__main__":
    dep = b"PCS-LATTICE-KAT"
    print("xof_input(PP, v) hex prefix:", xof_input(PP_SUFFIX, [(b"deployment", dep), (b"element", b"v")]).hex())
    print("jali_pp_seed:", jali_pp_seed(dep).hex())
    for name in pp_names():
        e = pp_element(dep, name)
        print(f"pp {name.decode()}: first 4 = {e[:4]}, last = {e[-1]}, sum mod 2^32 = {sum(e) % (1 << 32)}")
    c0 = identifier_point(dep, hashlib.sha256(b"x_0 of the known answers").digest())
    print(f"x0: first 4 = {c0[:4]}, row 167 last = {c0[-1]}, sum mod 2^32 = {sum(c0) % (1 << 32)}")
    xq = request_point(dep, bytes(range(32)))
    print(f"x_Q(00..1f): first 4 = {xq[:4]}, last = {xq[-1]}, sum mod 2^32 = {sum(xq) % (1 << 32)}")
    raw = stream(PP_SUFFIX, [(b"deployment", dep), (b"element", b"v")], 10)
    print("pp v raw stream first 10 bytes:", raw.hex())
