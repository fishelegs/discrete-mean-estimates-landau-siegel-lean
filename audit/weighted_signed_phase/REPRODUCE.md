# Reproducing the public evidence

Use Python 3 and the installed packages listed in `requirements.txt`. The recorded reruns used Python 3.12.14, mpmath 1.3.0 and SymPy 1.14.0. Dependencies are not installed automatically.

1. Run `python verify_bundle.py` to verify the detached manifest digest, every listed local file's byte count and SHA256, and each original/rerun PASS receipt.
2. Run `python verify_bundle.py --rerun` to execute every finite checker from an unrelated temporary working directory. Each checker writes a new temporary receipt; stable counts and exact budget fields are compared with the recorded rerun. Floating-point maxima need not be bit-identical across supported platforms, but each check enforces its own tolerance.
3. To retain one new output, run `python checks/check_author.py --output my-author-check.json` or the corresponding independent checker. Keep new receipts separate from the frozen original and recorded rerun files.

The public proof, public review, and adapted check scripts deliberately have different hashes from their historical originals. `PROVENANCE.json` preserves the original hashes and states the editorial changes. `MANIFEST.json` records only this public edition's current local files; historical external dependency hashes are provenance, not falsely verified by the portable checker. This is a integrity/reproduction aid, not a digital signature or a transitive proof certificate.

## Finite check scopes

- `checks/check_author.py`: numerical parity Gauss moments, CRT and double Fourier regressions
- `checks/check_independent.py`: exact rational convolution, prime-power, deletion-mask and normalization/Poisson-margin checks
- `checks/check_algebra.py`: 10,950 exact cyclotomic cubic/primitive-brace Fourier identities; Gauss moments, CRT, subset corrections and high-precision branch tests are numerical regressions, explicitly labeled in the receipt

`ALGEBRA_REVIEW.md` supplies independent finite-sum derivations, including all Fourier zero modes and both parities. Neither checker substitutes for the analytic contour and tail proofs.
