import ZhangLS.Spec.Lemma45HorizontalQuotient
import ZhangLS.Spec.Lemma45ErrorBudget

/-! # Lemma 4.5: zero exclusion for the actual normalized product -/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

/-- The exact open region in the statement of Lemma 4.5. -/
def Lemma45InRegion (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 + lemma44PaperAlpha D ^ 2 < s.re ∧ s.re < 1 ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2

theorem lemma45_parameters_at_threshold {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) :
    200 ≤ lemma23PaperL D ∧ 281600 * lemma23PaperL D ≤ lemma23PaperL D ^ 9 := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hL : 200 ≤ lemma23PaperL D :=
    hp.2.trans (Real.log_le_self (by linarith : 0 ≤ lemma23PaperL D))
  have h8 : 281600 ≤ lemma23PaperL D ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 200) hL 8
    norm_num at h
    linarith
  refine ⟨hL, ?_⟩
  calc
    _ ≤ lemma23PaperL D ^ 8 * lemma23PaperL D :=
      mul_le_mul_of_nonneg_right h8 (by linarith)
    _ = _ := by ring

theorem lemma45_region_subsets {D : ℕ} {s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hs : Lemma45InRegion D s) :
    Lemma23InOmega1 D s ∧ Lemma44InOmega3 D s ∧
      Lemma44InExtendedGammaRegion D s ∧ 1 / 2 < s.re := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have ha := lemma44_alpha_pos_le_one hp.1
  have hre : 1 / 2 < s.re := by linarith [sq_nonneg (lemma44PaperAlpha D), hs.1]
  have hr : 0 < Real.log (lemma23PaperL D) / (100 * lemma23PaperL D) :=
    div_pos (by linarith only [hp.2])
      (mul_pos (by norm_num) (by linarith only [hp.1]))
  have hs3 : Lemma44InOmega3 D s :=
    ⟨by linarith, by linarith [hs.2.1], by linarith [hs.2.2]⟩
  exact ⟨⟨by linarith, by linarith [hs.2.1], by linarith [hs.2.2]⟩,
    hs3, lemma44_omega3_subset_extended_gamma_region hp.1 hs3, hre⟩

theorem lemma45_B_bound_near {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma45InRegion D s)
    (hnear : s.re < 1 / 2 + (lemma23PaperL D)⁻¹) :
    ‖lemma45ActualB χ ψ s‖ ≤
      Real.exp (-(s.re - 1 / 2) * lemma23PaperL D ^ 9) := by
  have hr := lemma45_region_subsets hD hs
  have hZ := lemma44ActualZtilde_norm_le_right χ ψ hD hψ.1 hr.2.2.1 hr.2.2.2.le
  have hF := lemma45_horizontal_F_quotient_bound χ ψ hD hψ
    hr.2.2.2.le hnear hs.2.2
  have he : ‖lemma45ActualB χ ψ s‖ = ‖lemma44ActualZtilde χ ψ s‖ *
      ‖lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) /
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ := by
    simp only [lemma45ActualB, norm_div, norm_mul]
    ring
  rw [he]
  apply (mul_le_mul hZ hF (norm_nonneg _) (Real.exp_nonneg _)).trans
  rw [← Real.exp_add, lemma23PaperP, Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right (lemma45_parameters_at_threshold hD).2
    (sub_nonneg.mpr hr.2.2.2.le)
  nlinarith only [hm]

theorem lemma45_B_bound_far {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma45InRegion D s)
    (hfar : 1 / 2 + (lemma23PaperL D)⁻¹ ≤ s.re) :
    ‖lemma45ActualB χ ψ s‖ ≤ Real.exp (-(lemma23PaperL D ^ 8)) := by
  let L := lemma23PaperL D
  have hp := lemma45_parameters_at_threshold hD
  have hL : 200 ≤ L := hp.1
  have hLp : 0 < L := by linarith
  have hr := lemma45_region_subsets hD hs
  have hZ := lemma44ActualZtilde_norm_le_right χ ψ hD hψ.1 hr.2.2.1 hr.2.2.2.le
  have hF := lemma44_short_polynomial_coarse_bound χ ψ⁻¹
    (z := 1 - s) (by simp only [sub_re, one_re]; linarith [hs.2.1])
  have hi := lemma45_omega1_F_inv_bound χ ψ s (by linarith) hψ hr.1
  have hiexp : 4 * L ^ 79 ≤ Real.exp (82 * L) := by
    have hself : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hpow := pow_le_pow_left₀ hLp.le hself 79
    have h4 : (4 : ℝ) ≤ Real.exp (3 * L) := by
      linarith [Real.add_one_le_exp (3 * L)]
    calc
      _ ≤ Real.exp (3 * L) * (Real.exp L) ^ 79 :=
        mul_le_mul h4 hpow (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have h8 : 134 * L ≤ L ^ 8 := by
    have h7 : 134 ≤ L ^ 7 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 200) hL 7
      norm_num at h
      linarith
    calc
      _ ≤ L ^ 7 * L := mul_le_mul_of_nonneg_right h7 hLp.le
      _ = _ := by ring
  have hdelta : L ^ 8 ≤ (s.re - 1 / 2) * L ^ 9 := by
    have hd : L⁻¹ ≤ s.re - 1 / 2 := by linarith
    calc
      L ^ 8 = L⁻¹ * L ^ 9 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)
  have hbound : ‖lemma45ActualB χ ψ s‖ ≤
      Real.exp ((1 - 2 * s.re) * L ^ 9) * Real.exp (52 * L) * Real.exp (82 * L) := by
    unfold lemma45ActualB
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    have hZ' : ‖lemma44ActualZtilde χ ψ s‖ ≤ Real.exp ((1 - 2 * s.re) * L ^ 9) := by
      simpa only [lemma23PaperP, Real.log_exp] using hZ
    exact mul_le_mul (mul_le_mul hZ' hF (norm_nonneg _) (Real.exp_nonneg _))
      (hi.trans hiexp) (norm_nonneg _) (by positivity)
  apply hbound.trans
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [h8, hdelta])

theorem lemma45_B_uniform_gap {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma45InRegion D s) :
    ‖lemma45ActualB χ ψ s‖ ≤ Real.exp (-(lemma23PaperL D ^ 9)⁻¹) := by
  let L := lemma23PaperL D
  have hL : 3 ≤ L := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hLp : 0 < L := by linarith
  by_cases hnear : s.re < 1 / 2 + L⁻¹
  · apply (lemma45_B_bound_near χ ψ hD hψ hs hnear).trans
    apply Real.exp_le_exp.mpr
    have ha : lemma44PaperAlpha D * L ^ 9 = Real.pi := by
      simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
      dsimp only [L]
      field_simp [show lemma23PaperL D ≠ 0 from hLp.ne']
    have hd : lemma44PaperAlpha D ^ 2 ≤ s.re - 1 / 2 := by linarith [hs.1]
    have hm := mul_le_mul_of_nonneg_right hd (pow_nonneg hLp.le 18)
    have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith only [Real.one_le_pi_div_two]
    have hprod : 1 ≤ (s.re - 1 / 2) * L ^ 9 * L ^ 9 := by
      have he : lemma44PaperAlpha D ^ 2 * L ^ 18 = Real.pi ^ 2 := by
        rw [← ha]; ring
      rw [he] at hm
      calc
        1 ≤ (s.re - 1 / 2) * L ^ 18 := hpi.trans hm
        _ = _ := by ring
    have hh : (L ^ 9)⁻¹ ≤ (s.re - 1 / 2) * L ^ 9 := by
      rw [← one_div]
      exact (div_le_iff₀ (pow_pos hLp 9)).mpr (by nlinarith only [hprod])
    linarith
  · apply (lemma45_B_bound_far χ ψ hD hψ hs (le_of_not_gt hnear)).trans
    apply Real.exp_le_exp.mpr
    have hi : (L ^ 9)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ L))
    have h8 : 1 ≤ L ^ 8 := one_le_pow₀ (by linarith : 1 ≤ L)
    linarith

theorem lemma45_exp_gap {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    q / 2 ≤ 1 - Real.exp (-q) := by
  have he := Real.add_one_le_exp q
  have hep : 0 < Real.exp (-q) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_right he hep.le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have hdiv : Real.exp (-q) ≤ 1 / (1 + q) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + q)).mpr
    nlinarith only [hm]
  have hbound : 1 / (1 + q) ≤ 1 - q / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + q)).mpr
    nlinarith
  linarith

/-- A quantitative form of Lemma 4.5, valid at the same closed, computable
threshold as Lemmas 4.1--4.4. -/
theorem lemma45_actual_A_lower_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma45InRegion D s) :
    (lemma23PaperL D ^ 9)⁻¹ / 4 ≤ ‖lemma45ActualA χ ψ s‖ := by
  have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hr := lemma45_region_subsets hD hs
  have he := (lemma45_equation410 χ ψ hD hψ hr.2.1 hr.1).trans
    (lemma45_normalized_error_budget hL)
  have hB := lemma45_B_uniform_gap χ ψ hD hψ hs
  have hq : 0 ≤ (lemma23PaperL D ^ 9)⁻¹ := by positivity
  have hq1 : (lemma23PaperL D ^ 9)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D))
  have hg := lemma45_exp_gap hq hq1
  have ht := norm_sub_norm_le (1 + lemma45ActualB χ ψ s) (lemma45ActualA χ ψ s)
  rw [norm_sub_rev] at ht
  have hb : 1 - ‖lemma45ActualB χ ψ s‖ ≤ ‖1 + lemma45ActualB χ ψ s‖ := by
    simpa only [norm_one, sub_neg_eq_add, norm_neg] using
      norm_sub_norm_le (1 : ℂ) (-lemma45ActualB χ ψ s)
  linarith

/-- The original Lemma 4.5. All zero-free and error estimates are derived
from genuine `Ψ₁` membership, without Assumption (A). -/
theorem lemma45_actual_A_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma45InRegion D s) : lemma45ActualA χ ψ s ≠ 0 := by
  intro hz
  have hb := lemma45_actual_A_lower_bound χ ψ hD hψ hs
  rw [hz, norm_zero] at hb
  have hp : 0 < (lemma23PaperL D ^ 9)⁻¹ / 4 := by
    have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
    positivity
  linarith

theorem lemma45_actual_product_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma45InRegion D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s ≠ 0 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  intro hz
  apply lemma45_actual_A_ne_zero χ ψ hD hψ hs
  simp only [lemma45ActualA, hz, zero_div]

end ZhangLS.Spec
