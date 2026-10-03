# Reproduce the public evidence checks

Only Python's standard library is needed. From this directory:

```sh
python3 check_core.py
python3 check_complement.py
python3 verify_bundle.py
```

The first two checks print exact arithmetic results without changing the package. They include original shift and parity identities, exact cyclotomic orthogonality, coefficient convolutions, strict length margins, shell accounting and error exponents. Source/HEAD checks from the historical reviews are recorded separately in PROVENANCE.json and SOURCE_HASHES.json. Reproduction at the published revision preserves those pins. None of these commands invokes Lean, proves stationary phase, establishes the missing mixed moment, or supplies a favorable signed constant.
