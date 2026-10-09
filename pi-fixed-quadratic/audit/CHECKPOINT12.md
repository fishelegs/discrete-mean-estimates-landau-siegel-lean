# Checkpoint 12: independent fresh Linux final-target replay

This checkpoint adds a portable replay script and dedicated CI workflow for
`FixedQuadraticFixedFieldPi`. It changes no mathematical theorem, old Lean 4.30
pin, or protected proof. The new CI is not considered verified merely because
its plan passes locally or the arithmetic-core CI succeeds.

## Fixed dependency plan

- Lean 4.34.1 and the nine exact dependency revisions in `dependency-pins.json`.
- Upstream `openai/math` source at
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, cloned clean in the runner temp area.
- Exactly 843 upstream PiExponent modules and 65 local modules (908 total,
  including two expected compilation failures), selected recursively from the
  final public aggregate, its sqrt(2) regression, final type/axiom audit, and
  missing-exponent/wrong-field-degree negative regressions.
- External imports in this proof closure are only Lean and Mathlib.

`scripts/full-target-closure.json` records topological dependencies and reviewed
source SHA-256 hashes. `scripts/replay_full_target.py` reconstructs and checks
that closure, pins, compiler version, clean dependency sources, proof-token
scan, audit declaration coverage, every compiler result, final elaborated type
and the standard-only transitive axiom reports. It refuses an existing output
directory. Every OAI and local module is compiled from source into one initially
empty library directory using ordinary Lean, one worker and a 8192 MiB limit.

Only official mathlib cache artifacts at the exact package pins may be reused.
There is no OAI/local artifact cache, no copying of old Mac receipts or oleans,
and no use of the upstream monorepo Lake configuration or its patch hooks.
The upstream source is never modified. The full closure's earlier Mac elapsed
sum was about 59 minutes; the independent Ubuntu job allows 240 minutes.

## Reproduction

From this isolated subproject, provision `lake exe cache get` and check the pin
files are unchanged. Clone the upstream source at the displayed pin into a
separate temp directory, without running its Lake configuration. Then run:

```sh
python3 scripts/replay_full_target.py --lean "$(elan which lean)" \
  --mathlib "$PWD/.lake/packages/mathlib" \
  --packages-dir "$PWD/.lake/packages" \
  --upstream /path/to/clean/pinned/openai-math \
  --out /path/to/new/absent/output-directory
```

`--plan-only` performs preflight checks without compiling or creating output.
Local preflight passes: 908 modules, 843 upstream, 65 local, two negatives.
This preflight is not a fresh proof build.

The dedicated workflow is `.github/workflows/pi-fixed-quadratic-full.yml`.
Its artifact `fixed-quadratic-full-theorem-verification` preserves all compiler
logs, incremental receipt, exact actual theorem type, final axiom audit, closure
manifest and dependency pins. Remote completion and artifact validation will
be recorded separately after an actual successful run. The existing arithmetic
workflow continues to cover its own 50 checks and 265 type/axiom reports.

## First Linux run and resource correction

Run `37905342242` at commit `9bd2f696017f49ca0175721525d43b14474c7d07`
passed preflight and the first eight freshly compiled modules. The ninth,
`OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology`, stopped with
Lean's `memory_exception` at the initial 6144 MiB interpreter limit. This run
is a failure, not final-theorem evidence. The previous Mac ordinary build used
8192 MiB successfully for this module and the whole closure. The portable
script now uses that established 8192 MiB budget, still one compiler worker.
The corrected workflow will start again with no OAI/local build cache.

## Successful independent Linux result

Corrected replay commit: `d261f45e66f49df4eb4eec8f895cb8855bc484d1`.
Run: https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/actions/runs/37905909230

The run completed successfully on x86_64 Linux, Lean 4.34.1. All 908 receipt
entries and uploaded source/log hashes were independently checked against the
reviewed closure: 843 upstream and 63 local modules compiled successfully from
source, and two local final-theorem negative tests failed as expected. The
sqrt(2) positive specialization and final aggregate compiled. All six actual
type/axiom reports match CP11; their only axioms are `propext`, `Classical.choice`,
and `Quot.sound`. The exact final theorem type also matches CP11, with no extra
interpolation, integrality, analytic or parameter-margin hypotheses.

The ordinary compiler elapsed sum is 3945.879 seconds (about 65.8 minutes). The
runner reported 15 GiB RAM and 3 GiB swap; every compiler call used one worker
and the established 8192 MiB limit. Only the pinned mathlib official package
cache was reused. All OAI and local oleans were newly produced in the initially
empty runner output directory. No old Mac receipt was a replay input.

`fresh-linux-full-target-receipt.json` preserves the complete raw receipt and
`fresh-linux-full-target-validation.json` records the independent artifact
validation. `fresh-linux-final-logs/` preserves actual final types, transitive
axioms and both expected failures; all remaining compiler logs are in the run's
`fixed-quadratic-full-theorem-verification` artifact.

The initial 6144 MiB failure remains part of the history, not success evidence.
This evidence-only commit skips redundant push-triggered jobs: it changes no
proof source, pin, replay script or workflow. The successful full-target run is
explicitly tied to the corrected replay commit above. CP6--CP9 root aggregates
have also completed successfully and their downloaded reports and all 1565
individual trusted Spec logs were checked. CP10--CP12 subsequently completed successfully with all aggregate reports
and 1565 individual logs verified. See `CI_COMPLETION.md` and
`ci-completion.json` for the final terminal-state ledger.

The original failed attempt is also preserved in the repository as
`fresh-linux-initial-memory-failure-receipt.json` and
`fresh-linux-initial-memory-failure.log`. No proof source or replay code changed
in this final evidence-only closeout. All old-project protection checks pass.
