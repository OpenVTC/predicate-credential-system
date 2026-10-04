#!/usr/bin/env python3
"""Independent reference (Python hashlib + exact rationals) for the lattice tag and its oracles:
H_mat, H_0, c_0, s = H_0(<id>), EncPred and the short-key Tag_LWR (src/lattice/oracles.rs,
src/kiprf/lwr.rs).

Normative text: the paper's predicate encoding EncPred and random oracles H_mat, H_0 (with c_0
and s_i) of the lattice construction, and its short-key Tag_LWR (rounding to the nearest element
mod p, ValidTag, AK + e = gamma T mod q with |e| <= floor(gamma/2)). The concrete bytes are those
of docs/encodings.md, "Lattice instantiation (feature `lattice`)".

Deliberately NOT a copy of the Rust code or of ref_oracles.py:
- 20-bit sampling reads each 5-byte group as one 40-bit little-endian integer and splits it
  into its low and high 20 bits (two consecutive chunks of the little-endian bit string);
  ref_oracles.py shifts one big integer, the Rust code assembles nibbles;
- TagEval rounds with fractions.Fraction (floor(x/gamma + 1/2)), not with the integer formula
  floor((2x + gamma)/(2 gamma)) of the Rust code.

    python3 tools/lattice/ref_tag.py > tools/lattice/ref_tag.out
"""
import hashlib
import struct
from fractions import Fraction

DOMAIN_PREFIX = b"PCS-V1"
HMAT_SUFFIX = b"/LATTICE-HMAT"
PREDENC_SUFFIX = b"/LATTICE-PREDENC"

D = 1024          # n = d
GAMMA = 15
P = 1 << 16
Q_T = GAMMA * P   # 983,040
M = 168
E_BOUND = (GAMMA - 1) // 2

KAT_DEPLOYMENT = b"PCS-LATTICE-KAT"


def frame(label: bytes, data: bytes) -> bytes:
    return struct.pack("<Q", len(label)) + label + struct.pack("<Q", len(data)) + data


def shake(suffix: bytes, items, nbytes: int) -> bytes:
    data = frame(b"dst", DOMAIN_PREFIX + suffix)
    for label, value in items:
        data += frame(label, value)
    return hashlib.shake_128(data).digest(nbytes)


def uniform_20(stream: bytes, modulus: int, count: int):
    assert (1 << 19) < modulus <= (1 << 20)
    out = []
    for k in range(0, len(stream) - 4, 5):
        v = int.from_bytes(stream[k:k + 5], "little")
        for chunk in (v & 0xFFFFF, v >> 20):
            if chunk < modulus and len(out) < count:
                out.append(chunk)
        if len(out) == count:
            return out
    raise AssertionError("stream too short")


def h_mat(deployment: bytes, y: bytes):
    """m x n over Z_{q_t}, row-major (entry (j, i) at index n j + i)."""
    stream = shake(HMAT_SUFFIX, [(b"deployment", deployment), (b"input", y)], 600_000)
    return uniform_20(stream, Q_T, M * D)


def h0(deployment: bytes, x: bytes):
    return h_mat(deployment, b"tag" + x)


def identity_point(deployment: bytes):
    return h0(deployment, b"identity")


def tag_bytes(tag) -> bytes:
    assert len(tag) == M and all(0 <= t < P for t in tag)
    return b"".join(struct.pack("<H", t) for t in tag)


def tag_point(deployment: bytes, tag):
    return h0(deployment, tag_bytes(tag))


def predicate_bytes(threshold: int, label: bytes) -> bytes:
    return struct.pack("<I", threshold) + struct.pack("<Q", len(label)) + label


def pred_enc(deployment: bytes, threshold: int, label: bytes) -> bytes:
    y = b"predicate" + predicate_bytes(threshold, label)
    return shake(PREDENC_SUFFIX, [(b"deployment", deployment), (b"input", y)], D // 8)


def matrix_bytes(a) -> bytes:
    """TagMatrix::to_bytes: 20-bit little-endian packing, row-major."""
    acc = 0
    for i, x in enumerate(a):
        acc |= x << (20 * i)
    return acc.to_bytes(len(a) * 20 // 8, "little")


def kat_key():
    """k_i = ((i * 0x9E3779B1 mod 2^32) >> 16) mod 3 - 1 (the Rust tests use the same formula)."""
    return [(((i * 0x9E3779B1) & 0xFFFFFFFF) >> 16) % 3 - 1 for i in range(D)]


def centred(x: int, m: int) -> int:
    r = x % m
    return r - m if r > m // 2 else r


def tag_eval(key, a):
    """(T, e): T_j = round(<a_j, K> mod q_t / gamma) mod p, e_j = gamma T_j - <a_j, K> mod+- q_t."""
    assert len(key) == D and all(k in (-1, 0, 1) for k in key)
    tag, err = [], []
    for j in range(M):
        row = a[D * j:D * (j + 1)]
        w = sum(x * k for x, k in zip(row, key))
        x = w % Q_T
        t = int((Fraction(x, GAMMA) + Fraction(1, 2)) // 1) % P
        e = centred(GAMMA * t - w, Q_T)
        assert abs(e) <= E_BOUND
        assert (w + e - GAMMA * t) % Q_T == 0
        tag.append(t)
        err.append(e)
    return tag, err


def summary(name, a):
    print(f"{name}: first 4 = {a[:4]}, entry[{D}] = {a[D]}, last = {a[-1]}, "
          f"sum mod 2^32 = {sum(a) % (1 << 32)}, sha256(to_bytes) = "
          f"{hashlib.sha256(matrix_bytes(a)).hexdigest()}")


if __name__ == "__main__":
    L = KAT_DEPLOYMENT
    c0 = identity_point(L)
    summary("c0 = H0(identity)", c0)
    summary("H_mat(input = empty)", h_mat(L, b""))
    zero = [0] * M
    summary("s(zero tag) = H0(<0^168>)", tag_point(L, zero))
    summary("c0 under deployment PCS-LATTICE-KAT2", identity_point(b"PCS-LATTICE-KAT2"))

    key = kat_key()
    print("kat key: counts (-1, 0, 1) =", [key.count(v) for v in (-1, 0, 1)], "first 8 =", key[:8])
    ident, e0 = tag_eval(key, c0)
    print(f"id = Tag(K, c0): first 8 = {ident[:8]}, last = {ident[-1]}, "
          f"sha256(<id>) = {hashlib.sha256(tag_bytes(ident)).hexdigest()}")
    print(f"e0: first 8 = {e0[:8]}, sum = {sum(e0)}, sum of squares = {sum(x * x for x in e0)}")
    s = tag_point(L, ident)
    summary("s = H0(<id>)", s)
    t0, e1 = tag_eval(key, s)
    print(f"T0 = Tag(K, s): first 8 = {t0[:8]}, last = {t0[-1]}, "
          f"sha256(<T0>) = {hashlib.sha256(tag_bytes(t0)).hexdigest()}")
    print(f"e1: first 8 = {e1[:8]}, sum = {sum(e1)}, sum of squares = {sum(x * x for x in e1)}")

    print("pred_enc(5, members) =", pred_enc(L, 5, b"members").hex())
    print("pred_enc(0, root)    =", pred_enc(L, 0, b"root").hex())
    print("pred_enc(1, '') first 16 =", pred_enc(L, 1, b"")[:16].hex())
