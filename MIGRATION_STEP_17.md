# Migration Step 17 — unconditional positivity of the divisor-character coefficient

Step 17 closes the last arithmetic sign hypothesis introduced in Step 16.

Mathlib v4.30.0 already defines, for a complex Dirichlet character `χ`,

```lean
DirichletCharacter.zetaMul χ = ArithmeticFunction.zeta * toArithmeticFunction (χ ·)
```

and proves

```lean
DirichletCharacter.zetaMul_nonneg (hχ : χ ^ 2 = 1) (n : ℕ) :
  0 ≤ χ.zetaMul n
```

by proving nonnegativity on prime powers and then using multiplicative factorization.
This is exactly the standard argument needed for Zhang's coefficient

\[
  \nu_\chi(n)=\sum_{d\mid n}\chi(d).
\]

The new module `ZhangLS/Spec/DivisorCharacterSumNonnegative.lean` first proves
`divisorCharacterSum_eq_zetaMul`, using `ArithmeticFunction.coe_zeta_mul_apply` and
`DirichletCharacter.apply_eq_toArithmeticFunction_apply`.  It then transfers
`DirichletCharacter.zetaMul_nonneg χ.quadratic n` to the real-valued coefficient
`divisorCharacterSumReal χ n`.

Consequently the Step-16 interface

```lean
DivisorCharacterSumNonnegative χ
```

is discharged by the unconditional theorem

```lean
divisorCharacterSumNonnegative_proved χ
```

and the finite Gaussian arithmetic bound becomes unconditional:

\[
  \frac18\frac D{\varphi(D)}
  \le
  \sum_{1\le n\le D}\frac{\nu_\chi(n)}n g_D(D^4/n).
\]

This is exposed as `lemma57_initial_gaussian_arithmetic_scale_proved`, and
`lemma57InitialArithmeticLowerBound_proved` packages the same result as the
`Lemma57ArithmeticLowerBound` input used by the contour-transfer layer.

The remaining work for Lemma 5.7 is now analytic rather than arithmetic: relate the
full smoothed Dirichlet series / Mellin integral to this finite lower bound, move the
contour, and control the error so that the main term is `realLDerivAtOne χ`.

No Lean executable is available in the current container, so these additions are
source-level only and are not claimed to be kernel-verified.
