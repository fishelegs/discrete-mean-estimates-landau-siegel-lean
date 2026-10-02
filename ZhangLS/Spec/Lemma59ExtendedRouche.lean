import ZhangLS.Spec.Lemma59ExtendedNormalizedProduct

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext48_omega_height_pos {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma59ExtendedZeroOmega D s) : 0 < s.im := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  apply (lemma44_extended_gamma_region_height hL ?_).2.2.1
  exact ⟨by linarith [hs.1], by
    linarith [hs.2, pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405]⟩

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext48_omega_reflection {D : ℕ} {s : ℂ} (hs : Lemma59ExtendedZeroOmega D s) :
    Lemma59ExtendedZeroOmega D (1 - conj s) := by
  simp only [Lemma59ExtendedZeroOmega, sub_re, one_re, conj_re, sub_im, one_im,
    conj_im, zero_sub, neg_neg]
  have he : 1 - s.re - 1 / 2 = -(s.re - 1 / 2) := by ring
  rw [he, abs_neg]
  exact hs

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext48_thin_slab_regions {D : ℕ} {s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hs : Lemma59ExtendedZeroOmega D s)
    (hslab : |s.re - 1 / 2| ≤ lemma44PaperAlpha D ^ 2) :
    Lemma59ExtendedOmega3 D s ∧ Lemma59InExtendedOmega1 D s ∧
      Lemma59ExtendedOmega3 D (1 - conj s) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have ha := lemma46_alpha_parameters hD
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hsre : |s.re - 1 / 2| < lemma44PaperAlpha D := by
    apply hslab.trans_lt
    nlinarith only [ha.1, ha.2.1]
  have hre := abs_lt.mp hsre
  have hs3 : Lemma59ExtendedOmega3 D s :=
    ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hr3 : Lemma59ExtendedOmega3 D (1 - conj s) := by
    simp only [Lemma59ExtendedOmega3, sub_re, one_re, conj_re, sub_im,
      one_im, conj_im, zero_sub, neg_neg]
    exact ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hs2 : Lemma59InExtendedOmega2 D s :=
    ⟨by linarith [ha.2.2.1], by linarith [ha.2.2.1], by linarith [hs.2]⟩
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  exact ⟨hs3, lemma59_extended_disk_subset_omega1 hL100 hp.2 hs2
    (mem_ball_self hR), hr3⟩

open Complex Set in
theorem lemma59_ext45_B_bound_far {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroFreeRegion D s)
    (hfar : 1 / 2 + (lemma23PaperL D)⁻¹ ≤ s.re) :
    ‖lemma45ActualB χ ψ s‖ ≤ Real.exp (-(lemma23PaperL D ^ 8)) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  let L := lemma23PaperL D
  have hp := lemma45_parameters_at_threshold hD
  have hL : 200 ≤ L := hp.1
  have hLp : 0 < L := by linarith
  have hr := lemma59_ext45_region_subsets hD hs
  have hZ := lemma44ActualZtilde_norm_le_right χ ψ hD hψ.1 hr.2.2.1 hr.2.2.2.le
  have hF := lemma44_short_polynomial_coarse_bound χ ψ⁻¹
    (z := 1 - s) (by simp only [sub_re, one_re]; linarith [hs.2.1])
  have hi := lemma59_ext45_omega1_F_inv_bound χ ψ s (by linarith) hψ hr.1
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

open Complex Set in
theorem lemma59_ext45_B_bound_near {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroFreeRegion D s)
    (hnear : s.re < 1 / 2 + (lemma23PaperL D)⁻¹) :
    ‖lemma45ActualB χ ψ s‖ ≤
      Real.exp (-(s.re - 1 / 2) * lemma23PaperL D ^ 9) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hr := lemma59_ext45_region_subsets hD hs
  have hZ := lemma44ActualZtilde_norm_le_right χ ψ hD hψ.1 hr.2.2.1 hr.2.2.2.le
  have hF := lemma59_ext45_horizontal_F_quotient_bound χ ψ hD hψ
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

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext46_actual_A_reflected_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedLocalStrip D s)
    (hzero : lemma45ActualA χ ψ s = 0) :
    lemma45ActualA χ ψ (1 - conj s) = 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma59_ext46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma59_extended_F_ne_zero χ ψ s hL100 hψ.2
    (lemma59_extended_disk_subset_omega1 hL100 hp.2 hr.1 (mem_ball_self hR))
  have hprod : DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s = 0 := by
    change _ / lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s = 0 at hzero
    exact (div_eq_zero_iff).mp hzero |>.resolve_right hF
  have hfe := lemma44_equation44 χ ψ hp.1 hψ.1 hr.2.2.2
  rw [hprod] at hfe
  have hZ := lemma44ActualZtilde_ne_zero χ ψ hp.1 hψ.1 hr.2.2.2
  have hbar := (mul_eq_zero.mp hfe.symm).resolve_left hZ
  have hψne : ψ ≠ 1 := by
    intro he
    have hh := hψ.1.2.1
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hh
    exact hψ.1.1.ne_one hh.symm
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.1.2.1
    (lemma44_family_coprime χ ψ hp.1 hψ.1)
  have htwne : lemma44CharacterTwist χ ψ ≠ 1 := by
    intro he
    rw [he, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at htwist
    have hdvp : p ∣ 1 := htwist ▸ Nat.dvd_mul_left p D
    exact hψ.1.1.ne_one (Nat.dvd_one.mp hdvp)
  rw [dirichletLFunction_inv_eq_conj_at_conj ψ hψne,
    dirichletLFunction_inv_eq_conj_at_conj (lemma44CharacterTwist χ ψ) htwne,
    ← map_mul, map_sub, map_one] at hbar
  have hz : DirichletCharacter.LFunction ψ (1 - conj s) *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (1 - conj s) = 0 :=
    (map_eq_zero conj).mp hbar
  simp only [lemma45ActualA, hz, zero_div]

open Complex ComplexConjugate Set in
theorem lemma59_ext46_actual_B_differentiable_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedLocalStrip D s) :
    DifferentiableAt ℂ (lemma45ActualB χ ψ) s ∧ lemma45ActualB χ ψ s ≠ 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma59_ext46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma59_extended_F_ne_zero χ ψ s hL100 hψ.2
    (lemma59_extended_disk_subset_omega1 hL100 hp.2 hr.1 (Metric.mem_ball_self hR))
  have hFr := lemma59_extended_F_ne_zero χ ψ (conj (1 - s)) hL100 hψ.2
    (lemma59_extended_disk_subset_omega1 hL100 hp.2 hr.2.1 (Metric.mem_ball_self hR))
  have hFi : lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) ≠ 0 := by
    rw [lemma45_short_sum_inv_eq_conj]
    exact (map_ne_zero conj).2 hFr
  have hZ := lemma44ActualZtilde_ne_zero χ ψ hp.1 hψ.1 hr.2.2.2
  constructor
  · exact ((lemma44ActualZtilde_differentiableAt χ ψ hr.2.2.2.ne').mul
      ((lemma44_short_polynomial_differentiable χ ψ⁻¹ (1 - s)).comp s
        (by fun_prop))).div (lemma44_short_polynomial_differentiable χ ψ s) hF
  · exact div_ne_zero (mul_ne_zero hZ hFi) hF

open Complex ComplexConjugate Set in
theorem lemma59_ext46_equation411 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedLocalStrip D s) :
    ‖logDeriv (lemma45ActualB χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)‖ ≤
        341600 * lemma23PaperL D := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma59_ext46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma59_extended_F_ne_zero χ ψ s hL100 hψ.2
    (lemma59_extended_disk_subset_omega1 hL100 hp.2 hr.1 (Metric.mem_ball_self hR))
  have hFr := lemma59_extended_F_ne_zero χ ψ (conj (1 - s)) hL100 hψ.2
    (lemma59_extended_disk_subset_omega1 hL100 hp.2 hr.2.1 (Metric.mem_ball_self hR))
  have hFi : lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) ≠ 0 := by
    rw [lemma45_short_sum_inv_eq_conj]
    exact (map_ne_zero conj).2 hFr
  have hZ := lemma44ActualZtilde_ne_zero χ ψ hp.1 hψ.1 hr.2.2.2
  have hid := lemma23_logDeriv_reflection_quotient
    (lemma44ActualZtilde_differentiableAt χ ψ hr.2.2.2.ne')
    (lemma44_short_polynomial_differentiable χ ψ⁻¹ (1 - s))
    (lemma44_short_polynomial_differentiable χ ψ s) hZ hFi hF
  change logDeriv (lemma45ActualB χ ψ) s = _ at hid
  rw [hid]
  have hb := lemma59_ext_F_logDeriv_at_threshold χ ψ s hD hψ hr.1
  have hbr := lemma59_ext_F_logDeriv_at_threshold χ ψ (conj (1 - s)) hD hψ hr.2.1
  have hbi : ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
      (1 - s)‖ ≤ 140800 * lemma23PaperL D := by
    rw [lemma46_inverse_F_logDeriv, norm_conj]
    exact hbr
  have hz := lemma59_ext44_equation46 χ ψ hp.1 hψ.1 hr.2.2.1
  have heq : logDeriv (lemma44ActualZtilde χ ψ) s -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) (1 - s) -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ) =
      (logDeriv (lemma44ActualZtilde χ ψ) s +
        ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)) -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) (1 - s) -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans (by
    have ht := norm_sub_le
      (logDeriv (lemma44ActualZtilde χ ψ) s +
        ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ))
      (logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) (1 - s))
    linarith)

open Complex Metric Set in
theorem lemma59_ext46_inner_disk_regions {D : ℕ} {c s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hs : ‖s - c‖ < lemma44PaperAlpha D) :
    Lemma59ExtendedOmega3 D s ∧ Lemma59InExtendedOmega1 D s := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hp := lemma46_alpha_parameters hD
  have hs2 : ‖s - c‖ < 2 * lemma44PaperAlpha D := by linarith
  have hstrip := lemma59_ext46_disk_subset_local_strip hD hc hci hs2
  have hr := abs_lt.mp ((abs_re_le_norm (s - c)).trans_lt hs)
  simp only [sub_re, hc] at hr
  have hparams := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hparams.2]) (by linarith only [hparams.1])
  refine ⟨⟨by linarith, by linarith, by linarith [hstrip.2]⟩, ?_⟩
  exact lemma59_extended_disk_subset_omega1 hL100 hparams.2
    (lemma59_ext46_local_strip_regions hD hstrip).1 (mem_ball_self hR)

open Complex Set in
theorem lemma59_ext45_B_uniform_gap {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroFreeRegion D s) :
    ‖lemma45ActualB χ ψ s‖ ≤ Real.exp (-(lemma23PaperL D ^ 9)⁻¹) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  let L := lemma23PaperL D
  have hL : 3 ≤ L := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hLp : 0 < L := by linarith
  by_cases hnear : s.re < 1 / 2 + L⁻¹
  · apply (lemma59_ext45_B_bound_near χ ψ hD hψ hs hnear).trans
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
  · apply (lemma59_ext45_B_bound_far χ ψ hD hψ hs (le_of_not_gt hnear)).trans
    apply Real.exp_le_exp.mpr
    have hi : (L ^ 9)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ L))
    have h8 : 1 ≤ L ^ 8 := one_le_pow₀ (by linarith : 1 ≤ L)
    linarith

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext46_actual_A_analyticOn_inner_disk {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    {R : ℝ} (hR : R < lemma44PaperAlpha D) :
    AnalyticOnNhd ℂ (fun w => lemma45ActualA χ ψ (c + w)) (closedBall 0 R) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  intro w hw
  have hnorm : ‖w‖ < lemma44PaperAlpha D :=
    lt_of_le_of_lt (by simpa [mem_closedBall, dist_zero_right] using hw) hR
  have hs : ‖c + w - c‖ < lemma44PaperAlpha D := by simpa using hnorm
  have hr := lemma59_ext46_inner_disk_regions hD hc hci hs
  have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hF := lemma59_extended_F_ne_zero χ ψ (c + w) hL100 hψ.2 hr.2
  have hstrip := lemma59_ext46_disk_subset_local_strip hD hc hci
    (by linarith [ (lemma46_alpha_parameters hD).1] : ‖c + w - c‖ < 2 * lemma44PaperAlpha D)
  have him := (lemma59_ext46_local_strip_regions hD hstrip).2.2.2
  have hne : c + w ≠ 1 := by
    intro he
    rw [he] at him
    norm_num at him
  exact (lemma46_actual_A_analyticAt χ ψ hne hF).comp (by fun_prop)

open Complex Metric Set in
theorem lemma59_ext46_actual_model_approximation_closed {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hzero : lemma45ActualA χ ψ ρ = 0)
    {w : ℂ} (hw : ‖w‖ < lemma44PaperAlpha D) :
    ‖lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) -
      lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ ≤
        lemma46ModelErrorConstant * lemma44PaperAlpha D * lemma23PaperL D := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  let M := Real.log (lemma23PaperP D)
  let c : ℂ := (1 / 2 : ℂ) + I * (ρ.im : ℂ)
  let s := c + w
  let δ := ρ.re - 1 / 2
  have hp := lemma46_alpha_parameters hD
  change 0 < a ∧ a < 1 / 4 ∧ 2 * a < L⁻¹ ∧
    1100000 * a * L ≤ 1 ∧ (L ^ 9)⁻¹ / 4 ≤ a * L at hp
  have hL : 200 ≤ L := (lemma45_parameters_at_threshold hD).1
  have hLp : 0 < L := by linarith
  have hM : M = L ^ 9 := by simp [M, lemma23PaperP, L]
  have haM : a * M = Real.pi := by
    change lemma44PaperAlpha D * Real.log (lemma23PaperP D) = Real.pi
    unfold lemma44PaperAlpha
    field_simp [show Real.log (lemma23PaperP D) ≠ 0 by change M ≠ 0; rw [hM]; positivity]
  have hδ : 0 ≤ δ ∧ δ ≤ a ^ 2 := ⟨by dsimp [δ]; linarith, by dsimp [δ, a]; linarith⟩
  have hc : c.re = 1 / 2 := by simp [c]
  have hci : |c.im - (lemma23PaperCenter D).im| < L ^ 405 + 13 := by
    simpa [c, L] using him
  have hrho : ρ - c = (δ : ℂ) := by
    apply Complex.ext <;> simp [c, δ]
  have hrhon : ‖ρ - c‖ = δ := by rw [hrho, norm_real, Real.norm_of_nonneg hδ.1]
  have hrhoa : ‖ρ - c‖ < a := by
    rw [hrhon]
    nlinarith only [hδ.2, hp.1, hp.2.1]
  have hs : ‖s - c‖ < a := by simpa [s] using hw
  have hx : ρ ∈ ball c (2 * a) := by
    rw [mem_ball, dist_eq_norm]
    linarith only [hrhoa, hp.1]
  have hy : s ∈ ball c (2 * a) := by
    rw [mem_ball, dist_eq_norm]
    linarith only [hs, hp.1]
  have hstrip (z : ℂ) (hz : z ∈ ball c (2 * a)) : Lemma59ExtendedLocalStrip D z :=
    lemma59_ext46_disk_subset_local_strip hD hc hci (by
      simpa only [mem_ball, dist_eq_norm] using hz)
  obtain ⟨e, he, heq⟩ := lemma46_exponential_transport_on_ball
    (a := ((2 * M : ℝ) : ℂ)) (by linarith only [hp.1] : 0 < 2 * a)
    (fun z hz => (lemma59_ext46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip z hz)).1)
    (fun z hz => (lemma59_ext46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip z hz)).2)
    (fun z hz => lemma59_ext46_equation411 χ ψ hD hψ (hstrip z hz)) hx hy
  change ‖e‖ ≤ 341600 * L * ‖s - ρ‖ at he
  have hdist : ‖s - ρ‖ ≤ 3 * a := by
    have ht := norm_sub_le (s - c) (ρ - c)
    rw [sub_sub_sub_cancel_right] at ht
    linarith only [ht, hs, hrhoa, hp.1]
  have he' : ‖e‖ ≤ 1024800 * a * L := by
    have hm := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 341600 * L)
    nlinarith only [he, hm]
  let e' := e + ((2 * M * δ : ℝ) : ℂ)
  have hδM : 2 * M * δ ≤ 8 * a * L := by
    have hm := mul_le_mul_of_nonneg_left hδ.2
      (by rw [hM]; positivity : 0 ≤ 2 * M)
    have he : 2 * M * a ^ 2 = 2 * Real.pi * a := by rw [← haM]; ring
    rw [he] at hm
    have hpi := Real.pi_le_four
    nlinarith only [hm, hpi, hL, hp.1]
  have he'n : ‖e'‖ ≤ 1100000 * a * L := by
    have ht := norm_add_le e (((2 * M * δ : ℝ) : ℂ))
    rw [norm_real, Real.norm_of_nonneg (by rw [hM]; positivity)] at ht
    change ‖e'‖ ≤ _
    nlinarith only [ht, he', hδM, mul_pos hp.1 hLp]
  have he'1 : ‖e'‖ ≤ 1 := he'n.trans hp.2.2.2.1
  have hexp : ‖Complex.exp e' - 1‖ ≤ 2 * 1100000 * a * L :=
    (Complex.norm_exp_sub_one_le he'1).trans (by nlinarith only [he'n])
  let v := Complex.exp (-2 * w * (M : ℂ))
  have hv : ‖v‖ ≤ Real.exp 8 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hm : ‖-2 * w * (M : ℂ)‖ ≤ 2 * Real.pi := by
      rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (by rw [hM]; positivity)]
      norm_num
      nlinarith only [hw, haM, show 0 < M by rw [hM]; positivity]
    exact (re_le_norm _).trans (hm.trans (by linarith [Real.pi_le_four]))
  have hBs : lemma45ActualB χ ψ s = lemma45ActualB χ ψ ρ * v * Complex.exp e' := by
    have heB := (div_eq_iff
      (lemma59_ext46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip ρ hx)).2).mp heq
    have hsρ : s - ρ = w - (δ : ℂ) := by rw [← hrho]; dsimp [s]; ring
    rw [hsρ] at heB
    have harg : -((2 * M : ℝ) : ℂ) * (w - (δ : ℂ)) + e =
        -2 * w * (M : ℂ) + e' := by dsimp [e']; push_cast; ring
    rw [harg, Complex.exp_add] at heB
    dsimp [v]
    linear_combination heB
  have hregρ := lemma59_ext46_inner_disk_regions hD hc hci hrhoa
  have hregs := lemma59_ext46_inner_disk_regions hD hc hci hs
  have herrorρ := (lemma59_ext45_equation410 χ ψ hD hψ hregρ.1 hregρ.2).trans
    (lemma45_normalized_error_budget (by linarith : 3 ≤ lemma23PaperL D))
  have herrors := (lemma59_ext45_equation410 χ ψ hD hψ hregs.1 hregs.2).trans
    (lemma45_normalized_error_budget (by linarith : 3 ≤ lemma23PaperL D))
  have hρ : ‖lemma45ActualB χ ψ ρ + 1‖ ≤ a * L := by
    rw [hzero, zero_sub, norm_neg, add_comm] at herrorρ
    exact herrorρ.trans hp.2.2.2.2
  have hρ2 : ‖lemma45ActualB χ ψ ρ‖ ≤ 2 := by
    have ht := norm_sub_le (lemma45ActualB χ ψ ρ + 1) (1 : ℂ)
    rw [add_sub_cancel_right, norm_one] at ht
    have haL : a * L ≤ 1 := by
      nlinarith only [hp.2.2.2.1, mul_pos hp.1 hLp]
    linarith
  have hBerr : ‖lemma45ActualB χ ψ s + v‖ ≤
      Real.exp 8 * (1 + 4 * 1100000) * a * L := by
    rw [hBs]
    have heq' : lemma45ActualB χ ψ ρ * v * Complex.exp e' + v =
        v * ((lemma45ActualB χ ψ ρ + 1) +
          lemma45ActualB χ ψ ρ * (Complex.exp e' - 1)) := by ring
    rw [heq', norm_mul]
    have ht := norm_add_le (lemma45ActualB χ ψ ρ + 1)
      (lemma45ActualB χ ψ ρ * (Complex.exp e' - 1))
    rw [norm_mul] at ht
    have hm := mul_le_mul hρ2 hexp (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hi : ‖(lemma45ActualB χ ψ ρ + 1) +
        lemma45ActualB χ ψ ρ * (Complex.exp e' - 1)‖ ≤
        (1 + 4 * 1100000) * a * L := by nlinarith only [ht, hρ, hm]
    have hb := mul_le_mul hv hi (norm_nonneg _) (Real.exp_nonneg 8)
    nlinarith only [hb]
  have hE : ‖lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)‖ ≤ a * L :=
    herrors.trans hp.2.2.2.2
  have hid : lemma45ActualA χ ψ s - (1 - v) =
      (lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)) +
      (lemma45ActualB χ ψ s + v) := by ring
  change ‖lemma45ActualA χ ψ s - (1 - v)‖ ≤ _
  rw [hid]
  have ht := norm_add_le
    (lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s))
    (lemma45ActualB χ ψ s + v)
  unfold lemma46ModelErrorConstant
  nlinarith only [ht, hE, hBerr]

open Complex Set in
theorem lemma59_ext45_actual_A_lower_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroFreeRegion D s) :
    (lemma23PaperL D ^ 9)⁻¹ / 4 ≤ ‖lemma45ActualA χ ψ s‖ := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hr := lemma59_ext45_region_subsets hD hs
  have he := (lemma59_ext45_equation410 χ ψ hD hψ hr.2.1 hr.1).trans
    (lemma45_normalized_error_budget hL)
  have hB := lemma59_ext45_B_uniform_gap χ ψ hD hψ hs
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

open Complex Metric Set in
theorem lemma59_ext46_actual_model_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hzero : lemma45ActualA χ ψ ρ = 0)
    {w : ℂ} (hw : ‖w‖ < lemma44PaperAlpha D) :
    ‖lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) -
      lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ ≤
        lemma46ModelErrorConstant * lemma44PaperAlpha D * lemma23PaperL D := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  exact lemma59_ext46_actual_model_approximation_closed χ ψ hD hψ hre hrehi.le him hzero hw

end ZhangLS.Spec
