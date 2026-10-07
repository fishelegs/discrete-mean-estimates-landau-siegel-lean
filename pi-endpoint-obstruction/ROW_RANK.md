# Finite weighted-row and explicit-period checkpoint

This source-only extension contains eight main Lean theorems. It is independent
of the earlier endpoint-obstruction file and leaves that checkpoint unchanged.
It does **not** prove that pi is badly approximable.

## What is proved

`PiRowRank.lean` proves four generic statements:

1. On a finite type, if `f : iota -> iota` is injective and every moved index has
   strictly smaller real weight, then `f i = i` for every index.
2. A nonidentity map satisfying that decrease condition has a collision.
3. Row reindexing by such a nonidentity map makes a square determinant zero.
4. The same vanishing holds after arbitrary separate scalar factors on the rows.

The determinant results work over any commutative ring. Weights need not be
injective. The self-map type is essential: it assumes closure in the same finite
packet. Strict decrease is required only for moved indices, but weak decrease
alone is insufficient. The determinant-vanishing results require movement.

`PiQualityFreeExample.lean` displays the exact 8-by-8 diagnostic matrix and proves:

- its determinant is `x^8` for every complex number `x`;
- its determinant is nonzero whenever `x` is nonzero;
- `period = 2 * (Real.pi : Complex) * Complex.I` is nonzero;
- the displayed matrix is nonzero in determinant at this actual period.

The last result uses only pi's nonzeroness, not its transcendence. The symbolic
determinant is checked by mathlib's certificate-producing `eval_det` tactic and
`ring`; all resulting proof terms are kernel checked.

The matrix uses rows `(j,s,beta)` with `j = 0,1` and, within each block,
`(s,beta) = (0,0),(1,0),(2,0),(0,1)`. Its columns are
`(h,alpha) = (0,0),(1,0),(0,1),(1,1),(0,2),(1,2),(0,3),(1,3)`.
The motivating finite parameters are `K=2`, `H=5`, `v0=2`, `w0=w1=1`, and
`theta=1/3`. The matrix entries match all 64 rational-polynomial entries in the
separately computed research diagnostic; this transcription check is not a Lean
proof of their Taylor-series origin.

## What is not proved

- The logarithmic/Taylor-coefficient derivation of the displayed matrix
- The full source row formula, its tail-support hypotheses, or its attachment to
  the generic finite-map theorem in any dimension
- The general one-coordinate same-selected-minor transcendence theorem
- The mixed-term zero-center-block theorem or aggregate quality/tail budget
- The asymptotic interpolation/separation hypotheses for the finite example
- A lower bound on the surviving determinant's size, cancellation control, any
  uniform approximation construction, or bad approximability of pi

In particular, the generic theorem exposes its hypotheses instead of claiming
that this extension has established them for the analytic source.

## Verification

Use the existing Lean 4.34.1 and mathlib revision pinned by `dependency-pins.json`.
No installs, dependency builds, Lake hooks, or network access are required.
Coordinate exclusive compiler use before running:

```sh
python3 scripts/replay-row-rank.py \
  --lean /path/to/existing/lean \
  --existing-mathlib-project /path/to/existing/pinned/project \
  --out /path/to/private/row-rank-replay
```

The script runs serially with `-j1 -M4096 -DautoImplicit=false
-DwarningAsError=true`. It checks source hashes and dependency pins, compiles four
positive modules, and verifies three intentional failures:

- dropping strict decrease (a swap with constant weights)
- dropping the nonidentity/movement hypothesis
- dropping the nonzero-center hypothesis at `x=0`

Positive regressions include a genuine downward row collision, scalar-weighted
vanishing over the rationals, repeated weights, the symbolic identity, centers
`0`, `1`, `6*i` (determinant `1679616`), and the actual period. The eight main
axiom audits admit only `propext`, `Classical.choice`, and `Quot.sound`.
No new axioms, incomplete proofs, or native proof shortcuts are used.

`verification/row-rank-types-and-axioms.log` records the fully printed theorem
types and definitions. The receipt and source hashes identify the exact checked
sources. Compiled artifacts, caches, and local paths are not publication payloads.
