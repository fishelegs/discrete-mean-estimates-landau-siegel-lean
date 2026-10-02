import ZhangLS.Spec.Lemma44HorizontalGrowth

/-! # Uniform coarse bounds for the actual reflected finite polynomials -/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

theorem lemma44_finite_polynomial_coarse_bound {D N Q : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ Q)
    (S : Finset ℕ) (hN : 0 < N) (hS : S ⊆ Finset.Icc 1 N)
    {z : ℂ} (hz : -11 ≤ z.re) :
    ‖∑ n ∈ S, lemma23NuArithmeticFunction χ n * ψ (n : ZMod Q) *
      exp (-z * (Real.log (n : ℝ) : ℂ))‖ ≤ (N : ℝ) ^ 13 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpoint (n : ℕ) (hn : n ∈ S) :
      ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod Q) *
        exp (-z * (Real.log (n : ℝ) : ℂ))‖ ≤
        (N : ℝ) * Real.exp (11 * Real.log (N : ℝ)) := by
    have hi := Finset.mem_Icc.mp (hS hn)
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hi.1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hi.2
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnr
    have hlogN := Real.log_le_log (by linarith : (0 : ℝ) < n) hnN
    have hc : ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod Q)‖ ≤ N := by
      rw [norm_mul]
      have hnu : ‖lemma23NuArithmeticFunction χ n‖ ≤ n :=
        (lemma23NuArithmeticFunction_norm_le_card_divisors χ n).trans
          (by exact_mod_cast Nat.card_divisors_le_self n)
      exact (mul_le_mul hnu (ψ.norm_le_one _) (norm_nonneg _) (by positivity)).trans
        (by simpa using hnN)
    have he : ‖exp (-z * (Real.log (n : ℝ) : ℂ))‖ ≤
        Real.exp (11 * Real.log (N : ℝ)) := by
      rw [norm_exp, mul_re]
      simp only [neg_re, neg_im, ofReal_re, ofReal_im, mul_zero, sub_zero]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hz hlog0, hlogN]
    rw [norm_mul]
    exact mul_le_mul hc he (norm_nonneg _) (by positivity)
  have hcard : (S.card : ℝ) ≤ N := by
    have h := Finset.card_le_card hS
    have h1 : 1 ≤ N := hN
    simpa using (show (S.card : ℝ) ≤ ((Finset.Icc 1 N).card : ℝ) by exact_mod_cast h)
  calc
    _ ≤ ∑ n ∈ S, ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod Q) *
        exp (-z * (Real.log (n : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, (N : ℝ) * Real.exp (11 * Real.log (N : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * ((N : ℝ) * Real.exp (11 * Real.log (N : ℝ))) := by simp
    _ ≤ (N : ℝ) * ((N : ℝ) * Real.exp (11 * Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have he : Real.exp (11 * Real.log (N : ℝ)) = (N : ℝ) ^ 11 := by
        simpa [Real.exp_log hNr] using Real.exp_nat_mul (Real.log (N : ℝ)) 11
      rw [he]
      ring

theorem lemma44_short_polynomial_coarse_bound {D Q : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ Q)
    {z : ℂ} (hz : -11 ≤ z.re) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod Q)) z‖ ≤
      Real.exp (52 * lemma23PaperL D) := by
  have h := lemma44_finite_polynomial_coarse_bound χ ψ (Finset.Icc 1 (D ^ 4))
    (pow_pos χ.modulus_pos 4) (by rfl) hz
  unfold lemma23ActualSectionFourF lemma23SectionFourF lemma23FiniteDirichletPolynomial
  apply h.trans_eq
  rw [Nat.cast_pow, ← pow_mul]
  have hDr : (0 : ℝ) < D := by exact_mod_cast χ.modulus_pos
  simpa [lemma23PaperL, Real.exp_log hDr] using
    (Real.exp_nat_mul (Real.log (D : ℝ)) 52).symm

theorem lemma44_long_polynomial_coarse_bound {D Q : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ Q)
    (hL : 3 ≤ lemma23PaperL D) {z : ℂ} (hz : -11 ≤ z.re) :
    ‖lemma44LongDirichletSum χ ψ z‖ ≤ Real.exp (26 * lemma23PaperL D ^ 9) := by
  have hcut : D ^ 4 ≤ ⌊lemma23PaperP D ^ 2⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    simpa only [Nat.cast_pow] using lemma44_D4_le_P2 χ hL
  have hN : 0 < ⌊lemma23PaperP D ^ 2⌋₊ := lt_of_lt_of_le (pow_pos χ.modulus_pos 4) hcut
  have hS : Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊ ⊆
      Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊ := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have h := lemma44_finite_polynomial_coarse_bound χ ψ _ hN hS hz
  change ‖lemma44LongDirichletSum χ ψ z‖ ≤ _ at h
  apply h.trans
  calc
    _ ≤ (lemma23PaperP D ^ 2) ^ 13 := by
      apply pow_le_pow_left₀ (by positivity)
      exact Nat.floor_le (by positivity)
    _ = _ := by
      rw [← pow_mul, lemma23PaperP]
      simpa using (Real.exp_nat_mul (lemma23PaperL D ^ 9) 26).symm

theorem lemma44_short_polynomial_differentiable {D Q : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ Q) :
    Differentiable ℂ (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod Q))) := by
  unfold lemma23ActualSectionFourF lemma23SectionFourF lemma23FiniteDirichletPolynomial
  fun_prop

theorem lemma44_long_polynomial_differentiable {D Q : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ Q) :
    Differentiable ℂ (lemma44LongDirichletSum χ ψ) := by
  unfold lemma44LongDirichletSum
  fun_prop

end ZhangLS.Spec
