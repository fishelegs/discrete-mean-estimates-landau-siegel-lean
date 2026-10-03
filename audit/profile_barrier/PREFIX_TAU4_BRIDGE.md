# A feasible narrow improvement of the exceptional-family budget

This is an independently checked mathematical/source derivation for the source-specific coefficients, not a new Lean theorem. It preserves the actual short prime window and its `P² <= 4 M L^77` lower-mass consequence. It improves only the finite long prefix `n<=P²`; the existing global tau5 estimates remain in force for the infinite tail.

## Arithmetic reduction

For purely imaginary beta let `z_beta(n)=n^-beta` for n>0, and let `rho_beta(n)=sum_(d|n) mu(d)d^beta`, exactly `lemma151Rho` in `Lemma151Arithmetic.lean`. Then

```
(mu*z_beta)(n) = n^-beta rho_beta(n).
```

The identity follows directly by pulling n^-beta out of the divisor sum. Thus their absolute values agree. The proposed actual rho bound `|rho_beta(n)|<=exp(|beta| log n)` is also elementary: multiplicativity gives `rho_beta(n)=prod_(p|n)(1-p^beta)`; each factor is at most `|beta| log p`, hence at most `exp(|beta| log p)`. Their product is at most `exp(|beta| log rad(n))<=exp(|beta| log n)`. At n=1 both sides are one. This argument includes prime powers and does not postulate an independent rho envelope.

For n<=P² and |beta|<=5 alpha, `|beta| log n<=10π`. Hence `|mu*z_beta|<=C`, with the fixed absolute constant `C=exp(10π)`, on this prefix. Every positive divisor or factor in a convolution at n<=P² is itself inside the same prefix. The actual source betas satisfy an even smaller bound eventually.

| Actual long coefficient | Exact source/declaration | Prefix consequence |
|---|---|---|
| P7 kappa | `lemma83Kappa = mu*z_beta1*z_beta2*z_beta3`, `Proposition71CoefficientEnergy.lean`; source Section 7 | Group `mu*z_beta1`, leaving two modulus-one factors: `|kappa|<=C tau3` |
| P7 kappa*a1 | `proposition71ArithmeticSequence a1`, same file; actual bounded source a1 | `|kappa*a1|<=C B1 tau4` |
| Section 15 kappa1*bpsi | `lemma152Kappa = mu*z_beta1*z_beta2`; `b_source_ratio_convolution` in `BRatioConvolution.lean` | Group `mu*z_beta1` to get `|kappa1|<=C tau2`; then `|kappa1*bpsi|<=C B tau4` |
| Section 16 kappa2*b1 | `lemma161Kappa = mu*z_beta1`; source definitions before (16.2) and expansion before (16.14) | `b1=bpsi*v3`, `v3(n)=n^-beta3 g*(T²/n)`, so `|b1|<=B tau3`; then `|kappa2*b1|<=C B tau4` |

The Section 15 coefficient basis is important: the actual psi coefficient is `bpsi(n)=chi(n)b0(n)`, as proved in `b_source_product_eq_psi_series`. `b_source_ratio_convolution` uses `bPsiArithmetic`, not the unmodified chi-psi coefficient b0. The existing `b_psi_norm_le_tau_two` in `BCoefficientBounds.lean` proves `|bpsi|<=B tau2` with D-independent `bCoefficientConstant`. This coefficient distinction does not change the bound but must not be omitted from the exact source identity.

The Section 16 claim is tied to the same psi basis. The source has `B(s,psi)=sum bpsi(n)psi(n)n^-s` and `N(s+beta3,psi)=sum v3(n)psi(n)n^-s`. Therefore their finite polynomial product has coefficient bpsi*v3. `lemma61_gaussian_star_norm_le_one` in `Lemma61GaussianWeights.lean` proves `|g*(y)|<=1` for the actual Gaussian cutoff. Pure imaginary beta3 then gives `|v3|<=1`. The complete named Lean attachment for this b1 identity was not located/claimed in this review; it is an elementary source bridge to add, rather than an assumption that b1 is arbitrary tau3.

These same bounds continue to work for any explicitly fixed bounded profile coefficients with the same two-factor b construction, once that construction and its support are actually attached. They do not establish the generalized moment formula.

## Moment power count with the actual prime mass

The divisor inequality `tau4(n)^2<=tau16(n)` follows primewise from the same multichoose induction already used for tau5: its recurrence inequality is

```
(e+4)^2 <= (e+1)(e+16),
```

whose difference is `9e>=0`. Multiplicativity gives the full inequality, and the existing harmonic divisor-sum argument gives

```
sum_(n<=X) tau4(n)^2/n <= (1+log X)^16.
```

At X=floor(P²), the long second moment therefore has L exponent `9*16=144`, replacing 225. The short inverse fourth moment remains exponent 36; the genuine exceptional family cardinality saving is exponent 739; conversion of P^6 to M³ still costs `3*77=231`. Consequently

```
E^4 / M^4 <= C L^(2*144+36+231-739) = C L^-184,
E/M <= C L^-46.
```

With eventual a>1/2, this is also O(L^-46) on the aM scale, well below L^-8. Bounded phase weights and the actual Gaussian mass preserve the exponent. The horizontal contour and infinite-tail errors already have more than enough decay.

No ordinary dyadic prime-mass assumption has been made. Replacing the true 77 by 9 would be unjustified in this problem and is unnecessary.

## Smallest implementation/verification scope

1. Prove the exact `(mu*z_beta)=n^-beta rho_beta` bridge and the finite-prefix exponential bound, or reuse the independently verified actual rho theorem with its exact hypotheses.
2. Add a tau4-prefix second-moment and exceptional-family budget using the current actual mean/Hölder attachments. Keep a separate global tau5 hypothesis for all steps using the infinite coefficient tail.
3. Instantiate with P7 kappa*a1, the already attached Section 15 kappa1*bpsi, and the literal Section 16 bpsi*v3 coefficient identity. Keep all B constants fixed before D/chi thresholds.
4. Export the actual source exceptional contribution on the aM scale, retaining the L^-46 rate rather than weakening immediately to an epsilon-only statement.

Do not rewrite `Proposition141Target` to claim this for every arbitrary tau5 sequence. The stronger statement applies to source sequences that additionally have the proved tau4 prefix property. It closes one error-budget gap and leaves the Section 8 weighted ξ and full actual mean identification gaps untouched.
