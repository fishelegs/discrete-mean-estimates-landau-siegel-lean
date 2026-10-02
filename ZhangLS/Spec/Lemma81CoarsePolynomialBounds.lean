import ZhangLS.Spec.Lemma81KernelBoundaryGrowth

/-! # Coarse actual polynomial and family bounds for boundary errors -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_actual_A_coarse_bound {D p : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hL : 3 ≤ lemma23PaperL D) (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a)
    (ψ : DirichletCharacter ℂ p) {s : ℂ} (hs : -1 ≤ s.re) :
    ‖lemma81Polynomial D a ψ s‖ ≤ B*lemma23PaperP D^2 := by
  rw [lemma81_actual_polynomial_eq_prefix hL a ha]
  unfold lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊) :
      ‖a n * ψ (n : ZMod p) * Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖ ≤ B*lemma23PaperP D := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have hnP : (n : ℝ) ≤ lemma23PaperP D :=
      (show (n : ℝ) ≤ ⌊lemma23PaperP D⌋₊ by exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
        (Nat.floor_le hP.le)
    have hlogn := Real.log_nonneg hn1
    have hexp : ‖Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖ ≤ lemma23PaperP D := by
      rw [Complex.norm_exp]
      have he : (-s*(Real.log (n : ℝ) : ℂ)).re = -s.re*Real.log (n : ℝ) := by
        simp only [mul_re,neg_re,neg_im,ofReal_re,ofReal_im,mul_zero,sub_zero]
      rw [he]
      calc
        _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith only [hs,hlogn])
        _ ≤ _ := by rw [Real.exp_log hnr]; exact hnP
    rw [norm_mul,norm_mul]
    have hc : ‖a n‖*‖ψ (n : ZMod p)‖ ≤ B := by
      exact (mul_le_mul (ha.1 n) (ψ.norm_le_one _) (norm_nonneg _) hB).trans_eq (mul_one B)
    exact mul_le_mul hc hexp (norm_nonneg _) hB
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊,
        ‖a n*ψ (n : ZMod p)*Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊, B*lemma23PaperP D := Finset.sum_le_sum hpoint
    _ = (⌊lemma23PaperP D⌋₊ : ℝ)*(B*lemma23PaperP D) := by simp
    _ ≤ lemma23PaperP D*(B*lemma23PaperP D) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hP.le) (mul_nonneg hB hP.le)
    _ = _ := by ring

lemma lemma81_actual_A_product_coarse_bound {D p : ℕ} {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hL : 3 ≤ lemma23PaperL D)
    (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ha₂ : Lemma81AdmissibleSequence D B₂ a₂) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hslo : -1 ≤ s.re) (hshi : s.re ≤ 2) :
    ‖lemma81Polynomial D a₁ ψ s*lemma81Polynomial D a₂ ψ⁻¹ (1-s)‖ ≤
      B₁*B₂*lemma23PaperP D^4 := by
  rw [norm_mul]
  apply (mul_le_mul (lemma81_actual_A_coarse_bound hB₁ hL a₁ ha₁ ψ hslo)
    (lemma81_actual_A_coarse_bound hB₂ hL a₂ ha₂ ψ⁻¹ (by simp; linarith only [hshi]))
    (norm_nonneg _) (by positivity)).trans_eq
  ring

/-- Actual character counting normalized directly by the actual prime mass. -/
lemma lemma81_actual_good_family_card_le_mass {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    (χ : RealPrimitiveCharacter D) : ((lemma81GoodFamily χ).card : ℝ) ≤ lemma33ActualPrimeMass D := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hP1 : 1 ≤ lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hLp.le 9)
  have hshort : 1 ≤ ⌊lemma23PaperP D⌋₊ := Nat.le_floor (by exact_mod_cast hP1)
  have hmean := lemma34_actual_short_mean_bound D 1 hshort (fun _ => (1 : ℂ))
  have hcard : ((lemma33ActualFamily D).card : ℝ) ≤ lemma33ActualPrimeMass D := by
    simpa [lemma33ActualMean] using hmean
  have hs : (lemma81GoodFamily χ).card ≤ (lemma33ActualFamily D).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact (show ((lemma81GoodFamily χ).card : ℝ) ≤ (lemma33ActualFamily D).card by exact_mod_cast hs).trans hcard

end ZhangLS.Spec
