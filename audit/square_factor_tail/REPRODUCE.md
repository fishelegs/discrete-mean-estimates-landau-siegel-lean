# Reproduce the source audit

Requirements: Python 3.9 or later and the public repository files listed in INPUTS.json. The scripts use only the Python standard library. No Lean compiler, network call, external Python package, historical original archive or unstated local input is needed.

From this directory, run:

    python3 -I verify_bundle.py --repo-root /path/to/repository --rerun

The verifier checks the package manifest and checksum, all eleven public source byte pins, the original-to-public edition hashes, SOURCE ONLY scope, and exact agreement with fresh receipts from all three finite checkers. Each checker runs in a new temporary directory and leaves the package and repository unchanged. Omit --rerun to check only saved receipts and integrity.

The recorded source commit is cbcfbcbc7ceafaafcf3e711b7216d2f059da192d. A later repository checkout is usable if every pinned source has identical bytes. A full git checkout is unnecessary: --repo-root may instead be a clean directory containing just those eleven files at their repository-relative paths. The verifier makes no git or network call.

For an explicit relocation test, copy this entire package to a fresh directory, construct a separate input directory containing only the eleven pinned public files, then run its copied verify_bundle.py from an unrelated working directory with --repo-root pointing to that input directory. The saved package was checked in exactly that arrangement. Provenance originals are deliberately outside the verifier's input contract.

Expected totals:

- Author mathematical checker: 6,072 assertions
- Independent checker: 307,346 assertions
- Additional scope checker: 10,661 assertions
- Combined: 324,079 assertions

The independent script and its receipt are byte-identical to the original independent review's accepted versions. The author script retains its mathematical assertions; only the historical archive paths, six archive-integrity assertions, and output receipt plumbing were changed. Package and source integrity are now the verifier's responsibility. PROVENANCE.json records all changed hashes and editorial changes.

A successful run verifies these bytes and finite regressions. Universal source proofs are in PROOF.md and REVIEW.md. It does not prove an asymptotic claim by finite testing, certify new Lean declarations, establish transitive axiom closure, change the 51/51 Spec count, or prove the global signed half-norm gain or exponent-2024 theorem.

The mathematical review is dated 2026-10-04. Later evidence of formalization belongs in a separately verified audit and may be linked from a later edition; this source-only bundle contains no such claim.
