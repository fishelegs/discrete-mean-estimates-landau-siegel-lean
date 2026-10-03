# Reproduce the public mathematical package

From the repository root:

```sh
python3 audit/joint_signed_operator/verify_bundle.py --repo .
```

For a separate draft, run that draft's verify_bundle.py with --repo pointing to a checkout containing the pinned public dependencies. No compiler or third-party Python package is required. All checkers print full JSON to standard output and never write source or receipt files. Shell redirection to a new temporary file is optional.

The verifier checks every curated file against [MANIFEST.json](MANIFEST.json), every public dependency against [SOURCE_HASHES.json](SOURCE_HASHES.json), local Markdown link targets, and the complete historical manifest-to-source mapping. It reruns every checker listed in [COMPARISON.json](COMPARISON.json) and compares fresh results with both the saved portable receipt and the historical receipt. Integer counts, inventories, rational exponents, tolerance values, signs, status and mathematical scope match literally. Only explicitly named raw floating error fields may vary: all historical, saved and fresh values must be finite, nonnegative and strictly below the original tolerance. These are diagnostic regressions, not universal analytic proofs.

Historical path-dependent input checks have moved to this verifier. Their counts and hashes are validated against [AUTHOR_SOURCE_MANIFEST.json](AUTHOR_SOURCE_MANIFEST.json), [INDEPENDENT_SOURCE_MANIFEST.json](INDEPENDENT_SOURCE_MANIFEST.json), and [SOURCE_HISTORY.json](SOURCE_HISTORY.json) before removal from mathematical receipt comparison. No mathematical field is ignored. Only the named timestamp and checker path/hash identity fields differ by design; checker hashes are verified through the appropriate historical and public manifest instead.

Original source fingerprints were verified against original bytes at curation. Original reports and raw manifests may have different bytes from the public versions, so historical identities do not purport to hash current public files. For each curated dependency, its historical identity is also present in the pinned public provenance carrier. The portable verifier cannot reconstruct an omitted raw historical document from its hash; it verifies the published mapping and the actual curated bytes. An opaque nonmathematical historical-context fingerprint, when present, is not an analytic dependency.

The original author receipts retain historical review-status wording. The current mathematical verdict is in [STATUS.md](STATUS.md) and [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md). Acceptance remains source-only. Finite character examples are not asserted to satisfy hypothesis (A), and no checker proves the missing actual signed half-norm estimate or the final exponent-2024 theorem.
