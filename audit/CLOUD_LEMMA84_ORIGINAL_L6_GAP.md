# Exact remaining L^-6 budget obligation

## Where the Π term enters

Source TeX 2411 asserts the L quotient Q(s) equals its linear model V(s) plus
O(L^-15) on |s|=5α. TeX 2413–2415 multiplies this by U and claims the integrated
error is O(L^-6).

The proved algebraic inequality is `lemma84_product_error_bound` in
`Lemma84CircleError.lean`:

  ‖q*u - v*p‖ ≤ E*(‖p‖+δ) + M*δ

Here p=Π(d,r), δ bounds U−Π, E=8*C58*L^-15 bounds Q−V, and M=13*‖L′(1,χ)‖*α
bounds V. This estimate uses no division by p, including when χ(2)=1 makes p=0.

The normalized 5α-circle length and squared smoothing denominator contribute

  (5α) * exp(5π)/(4α²).

Thus the first summand E*‖Π‖ becomes exactly

  (10*C58*exp(5π)/π) * L^-6 * ‖Π‖,

since α=πL^-9. This exact transformation is kernel-checked in
`lemma84_circle_budget_algebra` (`Lemma84CircleBudget.lean`). The exposed constant
is `lemma84TaylorCircleConstant`.

The genuine 8.3 proof gives the stronger δ=O(α*(1+9logL)^(K+2)), so the remaining
arithmetic-perturbation error is O(L^-7*polylog(L)), already absorbed into L^-6.
The entire actual Perron-to-circle error is also already ≤L^-6. Only the displayed
Taylor multiplier ‖Π‖ remains at the borderline exponent.

## A sufficient strengthening

Any fixed ε>0 strengthening of the actual full-radius-10α Taylor estimate

  ‖L(1+w,χ) - L′(1,χ)w‖ ≤ Cε * L^(-15-ε)

would suffice. The existing quotient algebra would give E=O(L^(-15-ε)); its circle
integral times Π would be O(L^(-6-ε)*polylog(L)), hence O(L^-6) with a uniform
threshold. In particular either L^-16 (one power) or L^(-31/2) (half a power)
is sufficient. The L(1,χ) contribution under (A) is negligible at either scale.

The exact current input is `lemma58_actual_full_disk_linear_error`. Its proof
uses `lemma55_actual_taylor_remainder_bound`, whose actual second-derivative
majorant is 128*exp(1)*L^3. Replacing that L^3 by L^(3-ε) uniformly on the relevant
local disk would yield the sufficient Taylor strengthening above. A direct
improvement of the quotient error itself, or a joint Π-weighted Taylor bound,
would also suffice without strengthening the whole Taylor theorem.

Even a suitable fixed inverse-polylog improvement would be enough: the proved
bound is ‖Π‖≤S*(1+9logL)^K, so an O(L^-15/(1+9logL)^K) quotient error would close
this exact proof path.

## Mathematical status of that strengthening

It has NOT been proved here, and it does not follow merely by relabeling the
existing O(L^-15) bound. The current periodic-character Abel/Cauchy estimates
supply L^3 for the second derivative and no fixed positive logarithmic-power
saving. The completed 5.5 nonvanishing/reciprocal estimates likewise do not
supply such a Taylor gain as a corollary in this development. No claim is made
that the strengthening is impossible or that original Lemma 8.4 is false; a new
analytic/arithmetic argument or a genuinely joint estimate is still required.

## What is actually proved instead

The unchanged actual sum/main term satisfies

  error ≤ (2+C1*‖Π(d,r)‖)*L^-6.

Uniformly absorbing its proved polylog factor gives the explicitly labeled
repaired error ≤3L^-5. When Π=0 the original scale ≤2L^-6 holds. The original
`Lemma84Target` remains frozen and unproved.

The immediate §8 exponent-budget observation (normalization by log P and a
companion O(L^-7) term leaving room after harmonic weights) is NOT a theorem in
this packet. In particular no actual λ₀ⱼ weighted total-error theorem is claimed;
that requires independent verification before relying on the repair downstream.
