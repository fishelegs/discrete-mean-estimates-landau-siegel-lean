# Reproducing the audit checks

The package is standalone. No repository, Lean toolchain, external source file, network request, or private path is needed to execute the checks. Use Python 3.10 or newer with SymPy 1.14.0 and mpmath 1.3.0; the recorded run used Python 3.12.14. Requirements are pinned in requirements.txt. If dependencies are not already installed, install them in a separate environment using the normal package installer.

From this directory:

    python -B run_all_checks.py
    python -B verify_bundle.py

Both entry points locate the package through their own file paths, so they also work from an unrelated current working directory. Do not use Python's -O flag. The runner stops on a failed assertion or nonzero exit, writes a log for each script in results/, and regenerates results/check-summary.json and the adjacent JSON results. It executes the independent phase check last because that check hashes the packaged phase reports and newly generated phase outputs.

The shipped results are the completed run, not an intended command list. The runner output is recorded in [results/check-summary.json](results/check-summary.json). Repeating the run with the recorded environment produces the same result bytes; the integrity checker confirms this against the published hashes. A different Python or library version can change result rendering or floating-point formatting without changing a mathematical conclusion; review such differences rather than regenerating the manifest silently.

## What is checked

- check_extension.py: exact 3×3 completion boundary identities at (1/2,9/4,11/4), (1,3,4), (1,4,5), and (1,2,3)
- check_general_extension.py: all nine entries of the rational phase completion identity and the interpolation determinant for independent symbolic parameters
- check_spectral_bounds.py: both all-integer interior coercivity bounds, using exact finite cases and positive-coefficient infinite-tail certificates; beta matrices for k=2,3,4
- derive_cross_flux.py: arbitrary independent function-jet identity and integrated high/low cross cancellation, including the cumulative tail
- check_direct_extension.py: an independent all-parameter completion certificate by direct exponential integration, without the derivation's boundary-flux formula
- check_spectral_and_target.py: independent all-integer bounds, exact source target constants, and the general null-mode beta derivative
- check_algebra.py: exact rational exponent budgets and elementary finite coefficient/parity checks; the report contains their universal arguments
- check_gauss_identities.py: 50-digit floating-point CRT, phase, and C₀ sanity checks, tolerance 10⁻⁴⁰; this is supplemental numerical regression only
- exact_checks.py: symbolic elementary/parity identities and exact cyclotomic CRT, C₀, C₁, and T₁ regressions over the displayed finite prime/discriminant list

The symbolic all-parameter identities are not finite frequency extrapolations. The finite character regressions, in contrast, are not universal proofs: the CRT and orthogonality proofs in the review establish those identities. No script certifies actual weighted-zero means, analytic error terms, a complete signed ratio, the source's final theorem, or a formalized Lean result.

## Integrity and contents

MANIFEST.json lists every payload file with byte count and SHA-256. It excludes itself and SHA256SUMS to avoid a circular hash. SHA256SUMS covers all files except itself, including MANIFEST.json. verify_bundle.py checks exact coverage, file hashes/sizes, local Markdown links, and the completed nine-check result. It does not re-prove the mathematical claims.

ORIGINAL_INPUT_SHA256.json separately identifies the pre-packaging input reports and scripts. Public-edition changes are listed in [PACKAGING.md](PACKAGING.md). Reports and scripts use package-relative references; all historical absolute locations and stale result inventories were excluded.
