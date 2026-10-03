# Reproduce the half-norm evidence checks

Python 3.9 or later and its standard library suffice. No compiler, Lean installation, external package, network connection, or exceptional-character simulation is used.

From this directory run:

    python3 verify_bundle.py --require-accepted

For an exact repository-source check, run:

    python3 verify_bundle.py --require-accepted --repo /path/to/repository

The verifier checks the manifest digest, exact file inventory, byte lengths and SHA256 digests, then runs both portable mathematical checkers and compares their JSON output exactly against `AUTHOR_RERUN.json` and `INDEPENDENT_RERUN.json`. The optional repository check verifies all entries in `SOURCE_HASHES.json`, including the public versions of accepted dependency documents. It never modifies the repository.

`--require-accepted` requires the exact finalized independent-review identity and its source-only scope. It also binds the original and public proof/review hashes through `PROVENANCE.json`. A source-only mathematical review is not a Lean certificate. The final strict high-rho estimate remains open even when every check passes.

The author checker covers 16 finite coefficient fixtures through 600 and 19,600 Ramanujan pairs. The independent checker covers 35 genuinely complex coefficient fixtures through 840, 32,400 Ramanujan pairs, six exact local-ratio polynomial expansions, the finite principal-row reindexing, and rational exponent budgets. Finite fixtures test universally stated algebra, not the existence of a character satisfying (A).

`AUTHOR_ORIGINAL.json` and `INDEPENDENT_ORIGINAL.json` preserve the original receipt bytes. They record historical source-hash checks that the portable mathematical scripts do not repeat. `AUTHOR_SOURCE_MANIFEST.json` and `INDEPENDENT_SOURCE_MANIFEST.json` preserve every original manifest entry under a neutral source identifier. `PROVENANCE.json` records their original byte hashes and all curation changes. Original hashes and current public-file hashes are deliberately distinct.

The complete analytic argument and its independent verification remain in `PROOF.md` and `INDEPENDENT_REVIEW.md`. The scripts do not certify uniform asymptotic analysis, perform a transitive theorem audit, or prove a strict gain. A digest establishes byte integrity relative to this package, not external authorship or authenticity.
