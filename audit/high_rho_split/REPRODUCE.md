# Reproduce the high-rho evidence checks

Use Python 3.9 or later, `sympy`, and `mpmath`. The author checker uses only the standard library. The independent checker uses exact symbolic algebra and 45-digit numerical quadrature. No Lean installation, compiler, network access, or exceptional-character simulation is required.

From this directory run:

    python3 verify_bundle.py --require-accepted

For exact repository-source and public-dependency checks, run:

    python3 verify_bundle.py --require-accepted --repo /path/to/repository

The verifier checks the manifest checksum, complete file inventory, byte lengths and SHA256 hashes, then runs both portable checkers. All exact mathematical receipt fields must match. Only the raw Gauss and Fourier error measurements may vary, and each must retain the original strict `1e-35` tolerance. The scripts print JSON and do not modify files. Do not run Python with optimization enabled, since the finite checkers use assertions.

`--require-accepted` binds the exact finalized independent-review identity and its source-only mathematical scope. The optional repository check validates every source and public dependency in `SOURCE_HASHES.json`, including the separately accepted half-norm evidence used only to state the current remaining target.

The author checker covers 120,000 coefficient cases for six primitive real characters and five strict cutoffs through 4000. The independent checker covers 61,440 integer-cutoff cases for eight discriminants and five cutoffs through 1536, local envelopes through exponent 1000, all 120 scale orderings, seven squaring-family moment examples, normalized Gauss sums, twenty normalized Fourier substitutions, and all rational power/logarithmic budgets.

`AUTHOR_ORIGINAL.json` and `INDEPENDENT_ORIGINAL.json` preserve the original receipt bytes. `AUTHOR_RERUN.json` and `INDEPENDENT_RERUN.json` are portable reruns. The original independent receipt records nine historical input checks; those checks are represented in the source manifests and performed by the bundle verifier, rather than the portable mathematical checker. Each original manifest entry survives with its exact hash and a neutral source identifier. Original manifest byte hashes are recorded separately in `PROVENANCE.json`.

The complete analytic argument is in `PROOF.md` and `INDEPENDENT_REVIEW.md`. Finite fixtures check universal algebra; they do not claim to satisfy hypothesis (A), prove uniform stationary phase, supply an asymptotic threshold, or prove the remaining signed estimate. Hashes establish integrity relative to this package, not external authorship or authenticity.
