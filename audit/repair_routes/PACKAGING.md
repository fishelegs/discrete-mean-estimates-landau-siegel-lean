# Public edition and retained provenance

This package contains the reviewed mathematical reports and the assertion-bearing checks needed to reproduce their algebraic certificates. It contains no Lean changes or compilation result.

Editorial changes are explicit:

1. Private absolute locations in prose and the phase review's hash reader were replaced with package-relative references. Reproduction no longer depends on the originating filesystem or current working directory.
2. Zhang citations were pinned to arXiv:2211.02515v1. SOURCES.md consolidates the fixed versions and the source-file hash for TeX line offsets. Internal references to derivation line numbers refer to the reviewed pre-packaging edition; section numbers remain the stable report locators.
3. Public-edition notices and links to CORRECTIONS.md were added. The phase addendum's incomplete C₀-versus-C₁ wording is retained with a nearby correction, rather than silently rewritten. The squarefree deletion specialization is retained with a labeled review extension to all real primitive conductors.
4. The independent exact arithmetic checker additionally tests the C₁ congruence identity by exact cyclotomic reduction alongside its existing C₀ and T₁ tests. This is a finite regression check, not a substitute for the universal orthogonality proof.
5. All included checks were rerun, and results were regenerated. The two phase scripts that print JSON have their output saved by the runner. Reproduction instructions and a bundle integrity checker were added.

The raw exploratory boundary-printing script is excluded: it supplied no standalone assertion certificate, and the retained general, sample, and independent checks cover the accepted claims. Old machine-specific hash inventories and stale generated outputs were replaced by new package-relative provenance and fresh results.

ORIGINAL_INPUT_SHA256.json records the pre-packaging report/script hashes under logical document identifiers. It does not assert that the public edition is byte-identical. MANIFEST.json and SHA256SUMS identify the actual public-edition files. Mathematical proofs are in the reports; symbolic checks, finite exact character checks, and floating-point sanity checks have different evidentiary roles, stated in REPRODUCIBILITY.md.
