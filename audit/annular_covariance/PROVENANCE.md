# Acceptance and editorial provenance

## Independently accepted source records

- Frozen dyadic report, accepted original SHA256: `1839df7636ee4adcdacae99228c5ecf4b089556815fcc6c17d5b0888e3a91ea2`; [public copy](reports/DYADIC_REPORT.md)
- Independent dyadic review, original SHA256: `d30a11ab40462aa22965a6f6f479a6490faddaa6e47abe19e0f423833cc25cef`; [public copy](reviews/DYADIC_REVIEW.md)
- Separate fixed-log addendum, accepted original SHA256: `c457ac0dfb91b14a9bd45dee4615fa489cb98c2a90c0569d00a8ca3e0873c52e`; [public copy](reports/FIXED_LOG_ADDENDUM.md)
- Independent extension review, original SHA256: `9e94741392cb94abdf0cb0bccc23e3f9b023b920e45b47be4f7f92658d11edc1`; [public copy](reviews/FIXED_LOG_REVIEW.md)

The dyadic review explicitly accepts the dyadic report at its listed source hash. The extension review explicitly accepts the separate addendum at its listed source hash and rechecks the frozen dyadic hash. No pending or unaccepted mathematical extension is included.

## Public-copy normalization

The accepted source files were not edited. Copies in this bundle replace machine-specific source references with relative document links or provenance references, replace local check commands with links to the portable scripts and results, identify original hashes as pre-normalization source hashes, and normalize nonmathematical execution-scope wording in the review headers. No formula, inequality, hypothesis, quantified support, mathematical argument, verdict, or stopping condition was changed.

The author scripts are byte-identical except that the new fixed-window author script has a distinct packaged filename. The independent dyadic script runs all finite algebra without the paper, and optionally checks the accepted TeX hash when given an explicit external --source path. Without that input it reports the source identity check as skipped. The independent fixed-window script resolves the public dyadic copy from its own location and checks that copy's SHA256; its original input checked the original dyadic source hash. This is an explicitly documented path-normalization adaptation, not a claim that the normalized copy has the original byte hash.

[INPUT_RECORD.json](INPUT_RECORD.json) records each input's original hash and its public copy's hash. Original finite-check outputs are included unchanged. The three suites not using the source match their originals byte for byte. The default independent rerun replaces the source-hash output with an explicit skipped-check notice; its finite algebra output is unchanged. A separate rerun with the originally audited external TeX matches the original source-bearing independent output byte for byte. [SHA256SUMS](SHA256SUMS) pins every bundled file other than that manifest itself. Full source records and check outputs were retained only when relevant to the accepted mathematical audit.

## Prior bridge

The frozen report cites a preceding structured-covariance bridge as background: derivation SHA256 `1ae639db7a00f45c59af8fa4d6521d7332c7eeff155b85e0c86eedac568b1ff4`, independent review SHA256 `dc2ef2a8c901ebdfddda3e536cb3d0ef1f2e9a6ce2d38b7053e55c89c0729986`. These earlier records are not reproduced in this bundle and do not establish the new completion rates. The present report proves its own Euler bounds, annular tail moves, C1/T1 completion, and three-Gauss target kernel; its independent review audits those arguments directly.

## Primary source and scope

See the [version-specific primary citation and license](sources/CITATION.md). The full third-party TeX is not bundled. The originally audited local source input was retained outside the public package and reverified at its original hash in a separate explicit-input run. The version-specific arXiv title, author, submission date, and license link were checked on 3 October 2026. This package does not certify the paper's final contradiction or an integration with any formal theorem library.
