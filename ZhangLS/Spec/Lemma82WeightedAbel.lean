import ZhangLS.Spec.Lemma82ScaledTail

namespace ZhangLS.Spec
open Complex Finset MeasureTheory Set
open scoped Real
set_option maxHeartbeats 1000000

noncomputable def lemma82WeightedPolynomial {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    χ.evalNat n * (n : ℂ)^(-s) * (Real.log (x/(n:ℝ)) : ℂ)

lemma lemma82_scaled_polynomial_hasDerivAt {D : ℕ}
    (χ : RealPrimitiveCharacter D) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun z => (x:ℂ)^z * lemma82FinitePolynomial χ x z)
      ((x:ℂ)^s * lemma82WeightedPolynomial χ x s) s := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
      HasDerivAt (fun z : ℂ => (x:ℂ)^z * (χ.evalNat n * (n:ℂ)^(-z)))
        ((x:ℂ)^s * (χ.evalNat n * (n:ℂ)^(-s) *
          (Real.log (x/(n:ℝ)) : ℂ))) s := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hh := (Complex.hasStrictDerivAt_const_cpow (y := s) (Or.inl hx0)).hasDerivAt.mul
      ((((hasDerivAt_id s).neg).const_cpow (Or.inl hnC)).const_mul (χ.evalNat n))
    simp only [Pi.neg_apply, id_eq] at hh
    convert hh using 1
    rw [Real.log_div hx.ne' hnR.ne', Complex.ofReal_sub,
      ← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hnR.le]
    ring
  have hh := HasDerivAt.fun_sum hterm
  simpa only [lemma82FinitePolynomial, lemma82WeightedPolynomial, Finset.mul_sum] using hh

lemma lemma82_scaled_remainder_deriv {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    deriv (lemma82ScaledRemainder χ x) s = (x:ℂ)^s *
      ((Real.log x : ℂ) * dirichletLFunction χ s +
        deriv (dirichletLFunction χ) s - lemma82WeightedPolynomial χ x s) := by
  have hL := (Complex.hasStrictDerivAt_const_cpow (y := s)
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).hasDerivAt.mul
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD) s).hasDerivAt
  have hh := hL.sub (lemma82_scaled_polynomial_hasDerivAt χ hx s)
  have heq : (fun z : ℂ => (x:ℂ)^z * dirichletLFunction χ z -
      (x:ℂ)^z * lemma82FinitePolynomial χ x z) = lemma82ScaledRemainder χ x := by
    funext z
    unfold lemma82ScaledRemainder
    ring
  change HasDerivAt (fun z : ℂ => (x:ℂ)^z * dirichletLFunction χ z -
      (x:ℂ)^z * lemma82FinitePolynomial χ x z) _ s at hh
  rw [heq] at hh
  rw [hh.deriv, ← Complex.ofReal_log hx.le]
  ring

/-- An actual finite-to-analytic bridge on Re s=1, with no assumed Perron,
contour, conditional differentiation or endpoint identity. -/
lemma lemma82_weighted_abel_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ}
    (hs : s.re = 1) (hsnorm : ‖s‖ ≤ 2) :
    ‖lemma82WeightedPolynomial χ x s -
      ((Real.log x : ℂ) * dirichletLFunction χ s + deriv (dirichletLFunction χ) s)‖ ≤
      16 * (D:ℝ) / x := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hh := lemma82_scaled_remainder_deriv_norm χ hD hx hs hsnorm
  rw [lemma82_scaled_remainder_deriv χ hD hxp s, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxp, hs, Real.rpow_one] at hh
  rw [norm_sub_rev]
  apply (le_div_iff₀ hxp).mpr
  simpa only [mul_comm] using hh

/-- The integer endpoint contributes zero, so strict and inclusive cutoffs
agree exactly for the logarithmic kernel. -/
lemma lemma82_strict_weighted_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n:ℝ) < x),
      χ.evalNat n * (n:ℂ)^(-s) * (Real.log (x/(n:ℝ)) : ℂ)) =
      lemma82WeightedPolynomial χ x s := by
  unfold lemma82WeightedPolynomial
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Icc.mp hn).2
  have hnn : ¬ (n:ℝ) < x := by
    intro hlt
    exact hnot (Finset.mem_filter.mpr ⟨hn,hlt⟩)
  have heq : (n:ℝ) = x := le_antisymm hnle (le_of_not_gt hnn)
  simp [heq, hx.ne']

end ZhangLS.Spec
