# Migration Step 27 — direct finite-sum API alignment

This step continues source-level alignment with the pinned mathlib v4.30.0 API.
It does not claim Lean kernel verification because this execution environment
still has no `lean`/`lake` executable.

## Repairs

1. `Lemma57SmoothedSummability.lean`
   - replaces a manually coerced `Complex.reCLM` + generic `map_sum` rewrite with
     mathlib's dedicated `[simp] theorem Complex.re_sum`;
   - removes an unused local coefficient-nonnegativity proof.

2. `DivisorCharacterSum.lean`
   - changes the `Finset.sum_eq_single` proof from a tactic `rw` form with a
     separate value goal to a direct `apply` form;
   - this matches the theorem's standard usage: only the off-diagonal vanishing
     condition and membership of the selected index are supplied, while the
     selected summand remains the theorem result itself.

## Upstream facts checked

- mathlib v4.30.0 defines `Complex.re_sum` as
  `(∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re`.
- current mathlib examples use `Finset.sum_eq_single i` with the two expected
  side conditions after the main equality has been reduced to the selected term.

## Verification status

Static placeholder and structural checks are rerun for this package. Kernel
verification remains `NOT_RUN`/`FAIL` until a real Lean executable is available.
