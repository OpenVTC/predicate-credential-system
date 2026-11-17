# Test vectors of the IETF CFRG drafts

These JSON files hold the test vectors of two Internet-Drafts of the IRTF Crypto Forum Research
Group, extracted from the text form of each draft by `tools/kat/ietf_vectors.py`. The files are
byte for byte the output of that tool on the draft texts whose SHA-256 is given below, and each
file records that hash in its field `source.sha256`.

| file | draft | vectors | SHA-256 of the draft text |
|---|---|---|---|
| `sigma-protocols-04.json` | `draft-irtf-cfrg-sigma-protocols-04`, Appendix A | 95 | `1a03f4fd8ab81a288bee4731f52e077e28f680a2f20ff438fdfee278d8e946f5` |
| `fiat-shamir-04.json` | `draft-irtf-cfrg-fiat-shamir-04`, Appendix C | 35 | `d0764022bb92b717ab7ecbf985235e88c9ed088363a77bacd44b8a6bf6fdc193` |

The drafts are at <https://datatracker.ietf.org/doc/draft-irtf-cfrg-sigma-protocols/> and
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-fiat-shamir-04>. To regenerate a file from
the text form of its draft:

```sh
python3 tools/kat/ietf_vectors.py draft-irtf-cfrg-sigma-protocols-04.txt \
    --output kat/ietf/sigma-protocols-04.json
python3 tools/kat/ietf_vectors.py draft-irtf-cfrg-fiat-shamir-04.txt \
    --output kat/ietf/fiat-shamir-04.json
```

## Origin and terms

The vectors are part of the two drafts by M. Orrù and C. Yun, Copyright (c) 2026 IETF Trust and
the persons identified as the document authors. The drafts are subject to BCP 78 and the IETF
Trust's Legal Provisions Relating to IETF Documents (<https://trustee.ietf.org/license-info>),
which also govern these copies. They are reproduced here unchanged, as test data.

## What runs them

`tests/ietf_vectors.rs` (`cargo test --test ietf_vectors`):

* the 23 vectors of `fiat-shamir-04.json` for the suite SHAKE128 and the suite-independent codecs
  (the 12 TurboSHAKE128 vectors are out of scope: this crate uses SHAKE128 only),
* the 47 vectors of `sigma-protocols-04.json` for the ciphersuite
  `sigma-proofs_Shake128_BLS12381`, both flavors, valid proofs reproduced byte for byte with the
  draft's seeded generator (Appendix A.1) and every adversarial vector against its baseline (the
  48 vectors of `sigma-proofs_Shake128_P256` are out of scope: this crate has no P-256 group).
