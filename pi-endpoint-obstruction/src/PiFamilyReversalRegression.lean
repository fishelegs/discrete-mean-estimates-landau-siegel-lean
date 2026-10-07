import PiFamilyReversal

set_option autoImplicit false

open PiFamilyReversal

example : exponent 0 = 2 := by norm_num [exponent]
example : exponent 1 = 12 := by norm_num [exponent]
example : exponent 2 = 38 := by norm_num [exponent]
example : exponent 3 = 88 := by norm_num [exponent]
example : exponent 4 = 170 := by norm_num [exponent]
example : coefficient 2 = 11460 := by norm_num [coefficient]
example : coefficient 3 = 26740 := by norm_num [coefficient]
example : familyPolynomial 2 =
    Polynomial.C 4 * Polynomial.X^38 *
      (Polynomial.C 289 * Polynomial.X^2 + Polynomial.C 11460) := by
  norm_num [familyPolynomial, exponent, coefficient]

example : ‖family 3 (2 * (Real.pi : ℂ) * Complex.I)‖ <
    ‖family 3 ((44 : ℂ)/7 * Complex.I)‖ := family_reversal 3 (by norm_num)

example : ‖(familyPolynomial 3).eval (2 * (Real.pi : ℂ) * Complex.I)‖ <
    ‖(familyPolynomial 3).eval ((44 : ℂ)/7 * Complex.I)‖ := by
  simpa only [familyPolynomial_eval] using family_reversal 3 (by norm_num)

example : signedGain 3 < 0 := signedGain_neg 3 (by norm_num)
example : signedGain 4 < 0 := signedGain_neg 4 (by norm_num)
example : ∀ N : ℕ, 3 ≤ N → ¬ 0 < signedGain N := not_positive_signedGain

example {u t : ℝ} (hu : 0 < u) (hut : u < t) (ht : t ≤ 7) :
    u^4*(26740-289*u^2) < t^4*(26740-289*t^2) :=
  radial_strict (by norm_num) (by norm_num) hu hut ht
