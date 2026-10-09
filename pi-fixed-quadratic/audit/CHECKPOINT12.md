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
