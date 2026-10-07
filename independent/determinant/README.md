# Isolated determinant lower bounds

This independently pinned Lean project verifies an alternative determinant-based lower-bound proof for actual real primitive Dirichlet characters. It coexists with the repository's Lean 4.30.0 paper formalization; it does not change that project's toolchain or supply an importable proof inside its old kernel environment.

## Results

For D ≥ 2^24, the real part of the genuine analytic L(1,χ), and its norm, are strictly greater than 1/(1536 log D).

For every D ≥ 3 and every actual real primitive character, the positive rational
c = EffectiveConstantSearch.constant (2^24) satisfies both:
- c / (log D)^2022 < Re L(1,χ)
- c / log D < Re L(1,χ)

The exported declarations are EffectiveConstantSearch.effective_global_bound and EffectiveConstantSearch.effective_global_log_bound. The large-conductor declarations are in LargeConductorTheorem.lean. GlobalFiniteClosure.lean also retains the independent existential real/rational versions.

The constant is defined by ordinary executable rational arithmetic and a certified terminating finite search. Its numerical value at the target cutoff has **not been evaluated**. Only searchIndex 4 was evaluated, returning 12. The exhaustive table family is prohibitively large; no practical runtime is claimed. Do not evaluate constant (2^24) or turn it into an eager module initializer.

## Verification and scope

The 87 proof modules were compiled under Lean 4.34.1 with pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Audited exports use only propext, Classical.choice and Quot.sound. The historical source/object hashes, successful exit codes and axiom summaries are in verification/baseline.json. Independent source/evidence reviews checked the actual analytic object, character hypotheses, common determinant witness, finite closure and executable search.

Historical local verification is distinct from this branch's hosted CI. The dedicated workflow rebuilds the complete selected local source closure and its audits. The official pinned Mathlib cache is a trusted dependency boundary, not an independent rebuild of all Mathlib.

This is an alternative lower-bound proof. It does not repair the original paper's unfinished signed-mean chain, change the paper's 40/51 ledger, certify its 2024 zero-free-region target, or verify the entire upstream OpenAI project and its full 7/8 theorem. The prime-mass estimate containing a 7/8 term is only a component of the proof here.

Connecting to the original ZhangLS.Spec.Theorem1Target requires a tested common-toolchain bridge: map the character structure and analytic value, translate the negative integer power, and handle the impossible primitive-character case D = 2. No such root-project bridge is claimed.

## Replay

Use an isolated Linux x86_64 directory with Python 3, Git, curl, tar and zstd. Budget roughly 10 GB RAM and at least 12 GiB free disk; the build requires at least 8 GiB measured available memory before each compiler process.

For these exact pins, measured allocated disk usage is 11,792,220,160 bytes (10.983 GiB): toolchain 3,114,192,896; dependency source/build cache 7,518,867,456; compressed Mathlib cache 469,790,720; required Lean archive 580,440,064; and local proof objects 108,929,024. The 12 GiB CI preflight leaves just over 1 GiB headroom and logs actual storage before and after setup. The unrelated upstream source archive is not downloaded by replay. This is designed for a standard free public-repository Ubuntu runner, documented with 14 GB storage and 16 GB RAM; runner resource checks remain authoritative. See [GitHub's runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

1. sha256sum --check SOURCE_SHA256SUMS
2. python3 replay.py --setup --trim-download-cache
3. python3 replay.py --build

Setup downloads the exact official Lean archive and checks its SHA-256, obtains the nine detached package revisions in project/lake-manifest.json, and explicitly restores the pinned official Mathlib cache. The no-hook Lake configuration does not import upstream OpenAI Lake hooks. Automatic Mathlib update caching is disabled, and inherited cache-URL overrides are removed.

The optional --trim-download-cache flag, used in CI, deletes only this replay directory's verified Lean archive after extraction/version verification, then its compressed .ltar files after successful restoration. This saves approximately 1 GiB. Setup records minimum sampled free disk space during each subprocess in logs/setup-resources.json; the measured final footprint is not a guarantee of transient peak or hosted-runner success. Clean hosted setup remains to be established by the new CI run. Omit the flag to retain download archives for offline reuse.

Build is serial, with -j1 -M6656, a sampled 7.25 GiB process-tree RSS watchdog and a 1 GiB available-memory floor. This is a watchdog, not an OS-enforced cgroup limit. On a guard failure, stop rather than silently raising the cap.

A guarded Lake invocation resolves the exact compiler environment once, then exits before the proof compilers run. Each proof uses the absolute pinned Lean executable directly, avoiding a resident Lake wrapper. The full environment is kept only in memory; diagnostics contain an allowlisted subset. Guard tests cover forced failure, process cleanup and private output capture. Every guard stop is a failed invocation, and cleanup checks for running owned descendants even after their leader exits.

Fresh receipts, logs and axiom reports are written under logs/. The default targets are EffectiveConstantSearch and the full raw/analytic audits; their local dependencies are compiled from source. Importing the effective module only repeats the tiny searchIndex 4 test.

A plain lake build is not the acceptance command: the minimal Lake configuration intentionally declares only enough libraries to resolve the replay environment. The replay helper selects and verifies the final proof closure explicitly.

## Provenance

The 69 unchanged raw modules come from OpenAI math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, including 12 support modules reconstructed from that commit's PrimeNumberTheoremAnd patch. Exact original paths, Git blob hashes, SHA-256 hashes and source URLs are in provenance/upstream-sources.json.

Splice/MertensSupport.lean retains verbatim proof chunks with narrow imports and a separate namespace; provenance/mertens-extraction.json records the ranges, hashes and upstream attribution. See NOTICE.md and licenses/ for retained licenses.

The original repository toolchain, source, generated import files and CI jobs remain separate. All new runtime outputs are ignored by this subproject's .gitignore. The original lexical source scanners nevertheless recurse into untracked toolchain sources after local setup. Run the root gate in a separate fresh checkout, and replay this subproject in another directory; the two CI jobs already use separate workspaces. Do not treat .gitignore as a scan exclusion.
