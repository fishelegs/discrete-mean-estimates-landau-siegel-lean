# Finite mathematical diagnostics

These scripts are supporting finite checks, not asymptotic proofs or Lean certificates. Their original bytes and output labels are retained for reproducibility; the first-sector label “REPORT section 8” means Section 8 of `02_short_sector.md` in this publication. They require Python 3 with the already available packages mpmath and sympy. No software installation is part of this checkpoint.

To rerun without changing tracked files, copy one sector's `checks.py` to a fresh temporary directory and run `PYTHONDONTWRITEBYTECODE=1 python3 checks.py` there. Compare its generated `CHECKS.json` with the corresponding `EXPECTED_CHECKS.json`. Floating-point details may vary with library versions; the checkpoint assembly replay records whether its own environment matched byte-for-byte.

The first-sector script checks rational exponent bookkeeping, local Euler majorants including ramification, shifted prime powers, finite convolution/Mellin masks, parity projectors, divisor covering and finite four-gamma contour examples. The second checks signed-real-part perturbations, mixed head/dual identities, finite sector partitioning, functional-equation scalars for both character parities and the Gaussian Mellin/CDF kernel, including its half-weight at the endpoint.

The proof obligations involving all moduli, arbitrarily large integration heights, and sufficiently large D are addressed in the mathematical notes, not certified by finite examples.
