# Reproducing the public evidence

Use Python 3 and the installed packages listed in `requirements.txt`. The recorded reruns used Python 3.12.14, mpmath 1.3.0 and SymPy 1.14.0. Dependencies are not installed automatically.

1. Run `python verify_bundle.py` to verify the detached manifest digest, every listed local file's byte count and SHA256, and each original/rerun PASS receipt.
2. Run `python verify_bundle.py --rerun` to execute every finite checker from an unrelated temporary working directory. Each checker writes a new temporary receipt; stable counts and exact budget fields are compared with the recorded rerun. Floating-point maxima need not be bit-identical across supported platforms, but each check enforces its own tolerance.
3. To retain one new output, run `python checks/check_author.py --output my-author-check.json` or the corresponding independent checker. Keep new receipts separate from the frozen original and recorded rerun files.

The public proof, public review, and adapted check scripts deliberately have different hashes from their historical originals. `PROVENANCE.json` preserves the original hashes and states the editorial changes. `MANIFEST.json` records only this public edition's current local files; historical external dependency hashes are provenance, not falsely verified by the portable checker. This is a integrity/reproduction aid, not a digital signature or a transitive proof certificate.

## Finite check scopes

- `checks/check_author.py`: finite convolution/tail identities, exact rational budgets and leading-scale length examples; numerical root cancellation and Fourier change of variable
- `checks/check_independent.py`: exact Gaussian-integer Euler/tail identities, ramified-deletion identities, exact cyclotomic Gauss products, divisor inequalities, rational budgets and six numerical Fourier change-of-variable checks for both signs

The original author receipt's `strong_length_example` suppresses the fixed profile width. It is retained only as historical evidence. The adapted author script and its rerun explicitly add `profile_width=1/2000` and upper exponent `3601/2000`; both exact T3 length inequalities remain mandatory. These examples never certify eligibility on their own.

Uniformity at actual height `L^519` and the discarded infinite Fourier-tail bound are proved in the independent review's Sections 3–4, with Section 4 reproduced in the public proof. Moderate-height numerical checks are not evidence for that uniformity by themselves.
