# Pi endpoint obstruction: a small Lean checkpoint

**This is not a proof that pi is badly approximable.** It is a standalone,
source-only checkpoint with 12 elementary theorems in the namespace
`PiEndpointObstruction`.

## What is proved

1. For arbitrary real `A` and `theta`, `A^2 < theta` implies
   `2*(A-theta) < 1-theta`. Thus the original strict endpoint parameter
   inequalities are inconsistent. Their weak versions force `A = theta = 1`.
2. A nonzero integer determinant has absolute value at least one, and the
   corresponding triangle-inequality estimate bounds it by the two linear
   approximation errors.
3. If an integer pair `(p,q)`, with `q > 0`, has an independent integer companion
   `(P,Q)` satisfying `0 <= Q <= B*q`, `B > 0`, and
   `q*|Q*alpha-P| <= 1/2`, then
   `|alpha-p/q| >= (1/(2*B))/q^2`.
4. Consequently, **assuming** a uniform construction of such companions, or of
   two independent approximants at every positive integer scale, the same
   quadratic lower bound holds globally.

The two-pair hypothesis is quantified precisely: a single fixed `B > 0` works
for every positive integer `q`; at that scale there exist positive integer
`Q1,Q2 <= B*q` and integer `P1,P2` with both
`q*|Qi*alpha-Pi| <= 1/2` and `P1*Q2-P2*Q1 != 0`.
The construction is an argument to the theorem. **It is not proved here.**

There is no instance of that construction for pi, no imported upstream pi
theorem, no proof of the converse BA criterion, and no extension from eventual
scales to all scales. The stronger finite-dimensional analytic obstruction is
also outside this checkpoint. The conditional criterion records the missing
construction requirement; it does not remove it.

## Source and checks

- `src/PiEndpointObstruction.lean`: all definitions and exact theorem types
- `src/PiEndpointObstructionAudit.lean`: prints the two construction predicates,
  all 12 theorem types, and all theorem axiom dependencies
- `src/PiEndpointObstructionRegression.lean`: positive regressions, including a
  concrete single-companion example and rejection of the uniform hypothesis
  for the rational real number zero
- `src/ExpectedFailure*.lean`: must fail if the construction hypothesis is
  omitted or the nonzero-denominator requirement is violated
- `verification/`: exact source hashes, compiler receipt, and audit/error logs

The main source, audit, and positive regressions compiled with warnings treated
as errors. Both negative tests failed for their intended hypotheses. All 12
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, `native_decide`, custom axiom, or unsafe declaration
in the main theorem source.

## Exact pins

- Lean: `leanprover/lean4:v4.34.1`
- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- All transitive source revision pins are in `dependency-pins.json`

Only four mathlib modules are imported. No determinant-project modules or
large determinant dependency sources are included.

## Replay using an existing mathlib cache

This directory intentionally does not replace the containing repository's Lake
configuration. Use an existing project whose `lean-toolchain` and
`lake-manifest.json` match the supplied pins and whose `.lake/packages/` contains
the corresponding precompiled packages. The script checks those pins, checks
the executable version and source hashes, and refuses missing direct imports.
It runs no Lake command or hook, performs no downloads or installations, and
never builds dependency sources.

After ensuring no other compiler is using the available memory, run:

```sh
python3 scripts/replay.py \
  --lean /absolute/path/to/lean-4.34.1/bin/lean \
  --existing-mathlib-project /absolute/path/to/pinned-project \
  --out /tmp/pi-endpoint-replay
```

All five checks run serially with `-j1 -M4096`; outputs and logs stay under
`--out`, which must be outside the dependency project. The final
`replay-receipt.json` contains source/output hashes and the checked axiom set.
The existing compiler and dependency cache are trusted inputs, not rebuilt by
this route. An empty machine first needs those pinned dependencies provisioned
separately.

The packaged Lean files are byte-for-byte identical to the compiled files.
The portable replay script has passed Python syntax checks but has not itself
been rerun after packaging. No binary `.olean` files are distributed.
