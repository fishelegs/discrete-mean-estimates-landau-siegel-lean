# Packaging revision: external primary-source input

This revision changes reproducibility packaging only; all independently reviewed mathematics and accepted original report hashes remain unchanged.

1. Removed the complete third-party paper TeX from the public directory and archive. The original source file used in the audits remains separately retained.
2. Replaced links to bundled paper bytes with the fixed arXiv v1 source-download URL, the original extracted-file SHA256, and explicit local-input instructions.
3. Made source-file identity verification an optional --source argument. Default runs complete finite algebra and explicitly report that source-file hashing was skipped.
4. Recorded both modes accurately: default algebra-only output and an explicit external-input run that verified the original source hash. Original historical check logs remain unchanged.
5. Updated the public dyadic report copy's citation links and the corresponding public-copy hash check. No mathematical text was changed; accepted original hashes remain fixed.
6. Updated source provenance, scope statements, public-copy input records, all file hashes, and the archive. Relative links and relocation are checked again.

See [source input instructions](sources/CITATION.md), [provenance](PROVENANCE.md), and [validation results](results/BUNDLE_VALIDATION.txt).
