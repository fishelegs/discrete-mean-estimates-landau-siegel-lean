# Cloud milestone: original Lemma 11.1

Verified 2026-10-02, Linux x86_64, pinned Lean 4.30.0 / mathlib v4.30.0.

`lemma111_proved : Lemma111Target` proves the original Gaussian-smoothed tent approximation. The actual Gaussian, paper P=exp((log D)^9), tent breakpoints 0.5/0.502/0.504, both closed interior intervals, all three open transition neighborhoods and uniform quantifier order are retained. Absolute constants are C=4000 and c=1. A stronger uniform error 4000/(log D)^24 holds for every positive y. No character or Assumption (A) hypothesis is needed.

## Verified

- Four new modules separately compiled; focused `lake build +ZhangLS.Spec.Lemma111:olean` passed (3584 dependency jobs)
- Eight regression examples, including the fully expanded original target, passed
- All 32 public theorem interfaces use only `propext`, `Classical.choice`, `Quot.sound`
- Independent paper-to-Lean review accepted against arXiv:2211.02515v1, (2.28), (4.1), pp62–64; actual integrability/continuity and derivative cancellation precede FTC
- Both generated import-coverage checks passed: 632 Spec imports and 897 full-project imports
- Source structure and placeholder checks passed for 987 Lean files
- Strict semantic heuristic audit still reports the same 357 historical review candidates, exit code 1; it is not relabeled as a clean audit
- Source SHA256 values are recorded in `cloud_lemma111_source_hashes.json`

## Scope of this validation

This is a fresh check of the complete new lemma and its necessary dependency graph. A fresh cloud check of every old Spec module and every old audit regression has not yet completed. The prior repository-wide PASS belongs to baseline Step137 on macOS; it is not claimed as a new Linux full PASS. Remote CI is checked after publication. Historical 24 completed results are carried forward, giving 25/51 completed numbered results.

The ongoing 3.6, 8.1 and 17.1 branches are not part of this proof or this completion claim. Literal 5.6 retains its unresolved modulus-one branch.

## Reproduce

Use the pinned toolchain and lockfile. Run `lake build +ZhangLS.Spec.Lemma111:olean`, then `lake env lean audit/CloudLemma111Regression.lean`. Run both `tools/generate_*_all_imports.py --check`, `tools/check_no_placeholders.py`, and `tools/check_lean_structure.py`. The full-project command remains `tools/verify_all_lean.sh`.

## Historical status conflict

Use source content and audit evidence rather than the largest step number: `audit/STEP137_STATUS.md` and the original full verification report establish completion of 3.2 at baseline, whereas root `STEP141_STATUS.md` describes older temporary work frozen at Step127. That old note does not reverse the completed 3.2 result.
