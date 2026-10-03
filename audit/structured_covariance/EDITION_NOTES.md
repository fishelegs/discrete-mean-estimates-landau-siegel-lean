# Public-edition provenance

This portable edition is derived from the revised derivation, author revision log, independent review, and their finite checks dated 2026-10-03. The reviewed mathematical derivation was identified before editing by SHA256:

    1ae639db7a00f45c59af8fa4d6521d7332c7eeff155b85e0c86eedac568b1ff4

All original input digests are recorded in [ORIGINAL_INPUT_SHA256.json](ORIGINAL_INPUT_SHA256.json). Those identify the original received bytes. The public-edition documents necessarily have different hashes because of the portability edits below. Current bundle bytes are identified by [SHA256SUMS](SHA256SUMS); it covers every distributed file except itself. Hashes are integrity checks, not signatures, identity authentication, or mathematical proof.

Editorial changes made for this edition:

1. Replaced machine-specific file references with relative links to the included derivation, revision record, independent review, scripts, and saved outputs. Replaced the unversioned paper URL with the explicit v1 citation.
2. Replaced the unbundled prior finite-check reference for T₁ with the same identity's checks already contained in this independent review and its script.
3. Removed a reference to an unbundled earlier bilinear report. The limitation it conveyed is retained: a fixed-ℓ bound alone does not pay the ℓ sum or evaluate the right congruence contribution. No external bilinear result is needed by the accepted H representation in this bundle.
4. Removed nonmathematical workflow wording from the review and removed repository file paths. Historical formalization-interface observations are explicitly labelled as limitations from the original inspection; no version-pinned repository snapshot or compilation certificate is supplied.
5. Added this provenance record, a short status, explicit correction record, immutable source citations, reproducibility instructions, and a check runner. Mathematical claims in the accepted derivation/review were not expanded. Subsequent unfinalized C₁/T₁ work is excluded.

The two mathematical check scripts are byte-for-byte unchanged. They were rerun from this bundle, and both outputs matched the originals exactly. The new runner was exercised both in place and from a relocated copy with a different working directory. It fails if required packages are unavailable or either saved output differs, so the author's optional mpmath skip cannot silently count as a successful full-bundle run.

The initial C₁ overclaim remains visible in [CORRECTIONS.md](CORRECTIONS.md), the [review verdict](INDEPENDENT_REVIEW.md), and the [author's revision log](REVIEW_REVISIONS.md). This editorial edition does not replace a fresh independent mathematical review of new claims; there are no new analytic claims here.
