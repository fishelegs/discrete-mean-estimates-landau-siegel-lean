# Step 77 — Full product Mellin inversion and finite contour deformation

Date: 2026-09-30.

## Proved results

Six new trusted modules use the genuine characters, coefficients and paper
parameters. The Section 4 threshold remains `D₀=3^(3^200)`.

1. `Lemma44ProductMellin.lean` proves Gaussian inversion for arbitrary
   coefficients with an absolutely convergent shifted L-series. A common
   Gaussian majorant gives actual vertical integrability and summable
   integrals of the coefficientwise norms. The product wrapper discharges
   convergence using the already proved genuine `ν(n)ψ(n)` series. The
   resulting identity includes summability of the complete smoothed series.
2. `Lemma44SmoothedTruncation.lean` proves Gaussian inversion symmetry and
   an explicit exponential tail bound. For `n≤D⁴`, the endpoint at
   `B=P^(9/5)` is at least `L^24`. Removing smoothing from the actual short
   polynomial therefore costs at most `L^-180` when `Re s≥0`.
3. `Lemma44SmoothedTail.lean` proves, for `n>P²`,
   `g(B/n)≤exp(-L^24/10)n^-3`. The actual coefficient norm is at most `n`,
   giving a summable inverse-square majorant. The complete original
   smoothed tail is at most `C₂ L^-180`, where
   `C₂=Σ_{n≥0}(n²)^-1` is a fixed convergent real series.
4. `Lemma44RightMellinApproximation.lean` proves the exact short/middle/tail
   decomposition and `Re s>0` on the paper's entire `Ω₃`. Combining the
   three established bounds gives the actual full right vertical integral
   equal to `F(s,ψ)+O(L^-180)`, with constant
   `1+5 exp(2π)+C₂`, from the defining hypothesis `ψ∈Ψ₁`.
5. `Lemma44ProductResidue.lean` proves a general entire-numerator simple
   residue theorem on the verified rectangle. The actual product numerator
   is entire: nontriviality of both characters follows from their genuine
   primitive conductors. Its residue is the actual L-function product.
6. `Lemma44FiniteProductShift.lean` attaches a pole-free rectangle and proves
   the residue identity for every left side `a≤-1/2`. In particular, the
   right truncated integral equals the actual product plus the truncated
   integral at `a=-Re s-1/2` plus an explicit horizontal contribution.
   On this left contour, within `|Im w|≤L^20`, the actual functional equation
   identifies the integrand with `Ztilde(s+w)` times the inverse-character
   product series. Its reflected real part is `3/2`, and its absolute
   convergence is independently proved. No good-set membership of `ψ⁻¹`
   is assumed.

## Remaining obligations

Lemma 4.4 remains **in progress**. The original smoothed tail estimate above
does not replace an estimate for the reflected tail after deformation.

- Bound the full right vertical integral outside `|Im w|≤L^20` using only
  its absolutely convergent product series and Gaussian damping.
- Split the reflected series on the initial left side into `n≤D⁴`,
  `D⁴<n≤P²`, and `n>P²`.
- Move the reflected short part to `Re w=10`, extracting
  `Ztilde(s)F(1-s,ψ⁻¹)` with the correct orientation and bounding its new
  vertical segment and horizontal sides.
- Move the reflected middle part to `Re w=-α` and connect it to the
  previously proved truncated middle integral, including horizontal sides.
- Bound the reflected infinite tail and the initial rectangle's horizontal
  contribution, then combine all errors into the full uniform `O(L^-179)`.

The reflected short numerator involves `Ztilde`, which is holomorphic on the
relevant high rectangle but is not asserted to be entire. Its residue argument
must therefore use a local rectangular version, rather than assuming the
global entire-numerator hypothesis of the new generic theorem.

## Constructive next route (not yet a Lean theorem)

Finite rectangles may avoid extending the Gamma modulus estimate to arbitrary
imaginary height. All deformed segments remain within the already verified
local Gamma strip. Only the original right vertical tail uses infinite height,
where absolute convergence gives a direct bound.

On the initial left side, the reflected real part is `3/2`. Compare its tail
to the fixed absolutely convergent divisor series at `5/4`:

`Σ_{n>P²} d(n)n^-3/2 ≤ P^-1/2 Σ_{n≥1}d(n)n^-5/4`.

The existing local bound at total real part `-1/2` is
`|Ztilde(s+w)|≤exp(3L)P²`. Multiplication by `B^w` and the `Ω₃` lower real
boundary leaves at most `exp(3L+9π/5)P^(1/5)`. Thus the reflected tail has
remaining decay `P^-3/10=exp(-3L^9/10)`. The finite interval length `L^20`
is absorbed into this decay; the comparison with `L^-180` can be checked
elementarily for `L≥3`. This is a proposed proof, not an audited interface.

For the initial horizontal sides, general complex-character Abel bounds on
`Re z≥1/2`, together with the actual functional equation on the left, would
give the needed polynomial height/conductor bound. The existing Abel module
is specialized to real primitive characters and cannot yet be applied to
general `ψ`. Extend this machinery honestly rather than supplying the desired
L-function bound as an extra hypothesis.

## Verification

All six modules pass individual kernel checks and module builds. The new
`Step77ProductMellinRegression.lean` checks the paper-facing right approximation,
finite deformation and reflected-series interfaces at the original computable
threshold. It passes. All nine printed principal interfaces use only
`propext`, `Classical.choice`, and `Quot.sound`.

The aggregate imports cover 85 trusted Spec modules and 163 project modules.
Placeholder and source-structure checks pass for all 192 Lean files.
Repository-wide kernel verification: **PASS**. All 85 individual trusted Spec
modules, the trusted aggregate, the full project and all 26 regressions pass.
The audit ran from 15:33:41 to 15:41:32 Asia/Shanghai on 2026-09-30
(07:33:41–07:41:32 UTC), as recorded in `lean_kernel_verification.txt`.

Paper reference: [Zhang, arXiv:2211.02515v1, Section 4](https://arxiv.org/html/2211.02515v1#S4).
