import ZhangLS.Spec.Lemma81WideQuotientBound

/-! # Actual kernel growth on Gaussian-suppressed boundary bands

These deliberately coarse bounds retain the genuine L-functions and Z-factor.
Their exp(O(L^9)) size is absorbed by the original Gaussian exp(-c L^10).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_actual_phase_norm_one {D p : ℕ} [NeZero p] (c : ℝ)
    (hL : 0 < lemma23PaperL D) :
    ‖(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hT : 0 < lemma51PaperT0 D := pow_pos hL 519
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hp hT)]
  simp [lemma52PaperBetaThree]

/-- Coarse bound for actual C throughout the wide contour strip. -/
theorem lemma81_uniform_wide_actual_C_growth {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ}, Lemma81WideStrip D s →
      Lemma59ZeroSeparated (D := D) ψ s (1/4) →
      ‖lemma81ActualC D c ψ s‖ ≤ Real.exp (170000*lemma23PaperL D^9) := by
  obtain ⟨Nq,hNq,hquot⟩ := lemma81_uniform_wide_actual_quotient hc
  obtain ⟨Ns,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Nq Ns,hNq.trans (le_max_left _ _),?_⟩
  intro D p _ χ ψ hD hψ s hs hsep
  have hDq := (le_max_left Nq Ns).trans hD
  have hDs := (le_max_right Nq Ns).trans hD
  have hL := lemma81_section_log_hundred (hNq.trans hDq)
  have hL3 : 3 ≤ lemma23PaperL D := by linarith only [hL]
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hparam := lemma81_wide_strip_parameters hL3 hs
  have haq := lemma51_alpha_le_quarter hL3
  have hb := lemma52_offset_bounds hL3 hc (hsmall D hDs)
  have hshift (b : ℝ) (hbn : 0 ≤ b) (hbh : b ≤ 3*lemma44PaperAlpha D) :
      ‖ψ.LFunction (s+I*(b : ℂ))‖ ≤ Real.exp (100*lemma23PaperL D^9) := by
    apply lemma81_actual_L_coarse_exponential ψ hψ.1 hL
    · simpa using hparam.1
    · simpa using (show s.re ≤ 2 by linarith only [hs.2.1])
    · have hh := abs_add_le (s.im-(lemma23PaperCenter D).im) b
      rw [abs_of_nonneg hbn] at hh
      have he : (s+I*(b : ℂ)).im-(lemma23PaperCenter D).im =
          (s.im-(lemma23PaperCenter D).im)+b := by simp; ring
      rw [he]
      linarith only [hh,hs.2.2,hbh,haq]
  have h₂ := hshift _ hb.2.1.1 hb.2.1.2
  have h₃ := hshift _ hb.2.2.1 hb.2.2.2
  have hQ := hquot χ ψ hDq hψ hs hsep
  have hZ := lemma81_inverse_Z_coarse_exponential ψ hψ.1 hL3 hs
  have he : lemma81ActualC D c ψ s =
      -I * (((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c *
        (lemma23DirichletZ ψ s)⁻¹ *
        (ψ.LFunction (s+lemma52PaperBetaOne D c)/ψ.LFunction s) *
        ψ.LFunction (s+lemma52PaperBetaTwo D c) * ψ.LFunction (s+lemma52PaperBetaThree D c) := by
    unfold lemma81ActualC
    ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,norm_neg,norm_I,
    lemma81_actual_phase_norm_one c hLp,one_mul,one_mul]
  calc
    _ ≤ Real.exp (37*lemma23PaperL D^9) * Real.exp (166550*lemma23PaperL D^9) *
        Real.exp (100*lemma23PaperL D^9) * Real.exp (100*lemma23PaperL D^9) :=
      mul_le_mul (mul_le_mul (mul_le_mul hZ hQ (norm_nonneg _) (Real.exp_nonneg _))
        h₂ (norm_nonneg _) (by positivity)) h₃ (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [pow_nonneg hLp.le 9]

noncomputable def lemma81BoundaryGrowthConstant : ℝ := 170001+lemma52ErrorConstant

lemma lemma81_boundary_growth_constant_pos : 0 < lemma81BoundaryGrowthConstant := by
  unfold lemma81BoundaryGrowthConstant
  linarith only [lemma52_error_constant_pos]

/-- Actual normalized C̃ has a common coarse bound on the thin strip,
including both moved horizontal edges and both short vertical end pieces. -/
theorem lemma81_uniform_thin_actual_Ctilde_growth {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      N ≤ D → Lemma23InPsi1 χ ψ → ∀ (Y : ℂ → ℂ), Lemma23ActualBranch ψ Y →
      ∀ {s : ℂ}, |s.re-1/2| ≤ lemma44PaperAlpha D →
      |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 →
      Lemma59ZeroSeparated (D := D) ψ s (1/4) →
      ‖lemma81ActualCtilde D c ψ Y s‖ ≤ Real.exp (lemma81BoundaryGrowthConstant*lemma23PaperL D^9) := by
  obtain ⟨Nc,hNc,hC⟩ := lemma81_uniform_wide_actual_C_growth hc
  obtain ⟨Ns,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Nc Ns,hNc.trans (le_max_left _ _),?_⟩
  intro D p _ χ ψ hD hψ Y hY s hsre hsim hsep
  have hDc := (le_max_left Nc Ns).trans hD
  have hDs := (le_max_right Nc Ns).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hNc.trans hDc)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hwide : Lemma81WideStrip D s := by
    have hr := abs_le.mp hsre
    have ha := lemma51_alpha_le_quarter hL
    exact ⟨by linarith only [hr.1],by linarith only [hr.2,ha],hsim⟩
  have hbound := hC χ ψ hDc hψ hwide hsep
  obtain ⟨e,he,hfactor⟩ := lemma52_actual_product_estimate ψ hψ.1.2.1 hψ.1.1.ne_one Y hY
    hL hc (hsmall D hDs) ⟨hsre,by linarith only [hsim]⟩
  have hinv : lemma23PaperL D^(-123 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hL1 (by norm_num)
  have hen : ‖e‖ ≤ lemma52ErrorConstant := he.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv lemma52_error_constant_pos.le)
  have hsum : ‖1+e‖ ≤ 1+lemma52ErrorConstant := by
    have hh := norm_add_le (1 : ℂ) e
    norm_num only [norm_one] at hh
    linarith only [hh,hen]
  have hconst : 1+lemma52ErrorConstant ≤ Real.exp (1+lemma52ErrorConstant) := by
    linarith only [Real.add_one_le_exp (1+lemma52ErrorConstant)]
  rw [lemma81_Ctilde_eq_C_mul_relative_error ψ Y c s e hfactor,norm_mul]
  apply (mul_le_mul hbound (hsum.trans hconst) (norm_nonneg _) (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold lemma81BoundaryGrowthConstant
  have h9 : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL1
  have hh := mul_le_mul_of_nonneg_left h9 (by linarith only [lemma52_error_constant_pos] : 0 ≤ 1+lemma52ErrorConstant)
  nlinarith only [hh]

end ZhangLS.Spec
