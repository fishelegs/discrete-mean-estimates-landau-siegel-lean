# Annular covariance audit bundle

Start with [STATUS](STATUS.md). The [frozen dyadic report](reports/DYADIC_REPORT.md) and [independent review](reviews/DYADIC_REVIEW.md) establish the limited scope recorded there. Read [corrections](CORRECTIONS.md) and [provenance](PROVENANCE.md) before using the result.

## Reproduce

Python 3.12, mpmath 1.3.0, and sympy 1.14.0 were used. Dependencies are pinned in [requirements.txt](requirements.txt). Install them in an environment you control, then from this directory run:

    python -B scripts/verify_bundle.py
    python -B scripts/run_checks.py

Both scripts locate inputs relative to their own files and work from a different current directory after relocation. The check runner reads the bundle without changing it. Default runs explicitly skip the external source-file SHA256 check. To include that separate identity check, obtain the official v1 TeX described in [source input instructions](sources/CITATION.md), then run:

    python -B scripts/run_checks.py --source path/to/source.tex

Only the additional source identity check needs this external input. Finite checks test algebra, exact rational budgets, support exponents, and numerical identities; they do not prove the uniform analytic estimates or signed gain.

## Integrity and source

[SHA256SUMS](SHA256SUMS) lists every regular file in the bundle except itself, with relative names. That standard self-exclusion avoids a circular hash; the archive and manifest hashes are supplied alongside the archive. [INPUT_RECORD.json](INPUT_RECORD.json) distinguishes the accepted input hashes from the public path-normalized copy hashes. See [the version-pinned external source citation and input instructions](sources/CITATION.md). The full third-party paper is not included.

The bundle is source-level mathematical evidence. No Lean theorem, repository integration, arithmetic main-term evaluation, or actual mu-normalization is certified by it.
