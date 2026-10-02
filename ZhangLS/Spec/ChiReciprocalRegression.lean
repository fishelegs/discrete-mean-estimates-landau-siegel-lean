import ZhangLS.Spec.ChiReciprocalContour

namespace ZhangLS.Spec
open Complex

/-- Literal shifted contour, with the original variable s and actual L(1+s,χ). -/
theorem chi_actual_shifted_polynomial_reciprocal :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), D₀ ≤ D → NormalizedAssumptionA χ →
        ∀ s : ℂ,
          ((s.re = -1/Real.log (D:ℝ) ∧ |s.im| ≤ D) ∨
           (|s.im| = D ∧ -1/Real.log (D:ℝ) ≤ s.re ∧ s.re ≤ 1/Real.log (D:ℝ))) →
          dirichletLFunction χ (1+s) ≠ 0 ∧
            ‖(dirichletLFunction χ (1+s))⁻¹‖ ≤ C*Real.log (D:ℝ)^26 := by
  obtain ⟨D₀,hD02,hmain⟩ := chi_actual_inverse_strip_under_A
  refine ⟨3*chiReciprocalConstant,mul_pos (by norm_num) chi_reciprocal_constant_pos,
    D₀,hD02,?_⟩
  intro D χ hDN hA s hs
  obtain ⟨ρ,_,_,_,_,_,_,hcontour⟩ := hmain χ hDN hA
  apply hcontour (1+s)
  rcases hs with ⟨hre,ht⟩ | ⟨ht,hlo,hhi⟩
  · apply Or.inl
    simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,zero_add]
    exact ⟨by rw [hre]; ring,ht⟩
  · apply Or.inr
    simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,zero_add]
    simp only [neg_div] at hlo
    exact ⟨ht,by linarith,by linarith⟩

/-- Genuine-object regression: the upper bound is on mathlib's continued
Dirichlet L-function, rather than a newly defined substitute. -/
theorem chi_actual_L_height_regression {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (hL : 8 ≤ Real.log (D:ℝ)) {s : ℂ}
    (hσ : 1-4/Real.log (D:ℝ) ≤ s.re) (ht : |s.im| ≤ (D:ℝ)+1) :
    ‖DirichletCharacter.LFunction χ.chi s‖ ≤ 14*Real.exp 16*Real.log (D:ℝ) := by
  exact chi_actual_L_uniform_height_bound χ hD hL hσ ht

/-- Genuine-object regression for the Euler reciprocal, at any height. -/
theorem chi_actual_inverse_right_regression {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 1 < s.re) :
    ‖(DirichletCharacter.LFunction χ.chi s)⁻¹‖ ≤ 1+(s.re-1)⁻¹ := by
  exact chi_actual_L_inverse_right_bound χ hs

/-- The finite sum used to control the analytic continuation is literally
χ(n)n^(−s), with cutoff floor(D⁴), not a model polynomial. -/
theorem chi_actual_truncation_regression {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    ‖dirichletLFunction χ s -
      ∑ n ∈ Finset.Icc 1 (D^4), χ.evalNat n*(n:ℂ)^(-s)‖ ≤
        ((D:ℝ)^4)^(-s.re)*(D:ℝ)*(‖s‖/s.re+1) := by
  have hx : 1 ≤ (D:ℝ)^4 := one_le_pow₀ (by exact_mod_cast hD.le)
  have hh := chi_actual_truncation_error χ hD hx hs
  simpa only [lemma82FinitePolynomial,←Nat.cast_pow,Nat.floor_natCast] using hh

end ZhangLS.Spec
