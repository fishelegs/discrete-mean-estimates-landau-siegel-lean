# Migration Step 07 — derivative compatibility at `s = 1`

## Goal

Bridge the complex analytic derivative supplied by mathlib with the real derivative used by the paper.

## Implemented

- Added `ZhangLS/Spec/RealAxisDerivativeAtOne.lean`.
- Added a local imaginary-part counterpart of mathlib's `HasDerivAt.real_of_complex`.
- Proved, at source level, that `Im L'(1,χ)=0` using one-sided uniqueness on `Set.Ici 1`.
- Proved `realLDerivAtOne χ = Re (LDerivAtOne χ)` using mathlib's `HasDerivAt.real_of_complex`.
- Discharged `RealAxisDerivativeTheoremTarget`.

## Mathematical dependency

The imaginary-part proof uses no reflection principle.  It uses:

1. complex differentiability of the nontrivial Dirichlet L-function;
2. `Im L(x,χ)=0` for all real `x>1` (Step 05);
3. `Im L(1,χ)=0` (Step 06);
4. uniqueness of the derivative within the right half-line `Ici 1`.

## Verification status

The execution container still has no Lean toolchain and cannot download one, so this file is not yet kernel-verified.  The proof was written against current mathlib source APIs, notably `HasDerivAt.real_of_complex`, `ofRealCLM`, `imCLM`, and `uniqueDiffOn_Ici`.
