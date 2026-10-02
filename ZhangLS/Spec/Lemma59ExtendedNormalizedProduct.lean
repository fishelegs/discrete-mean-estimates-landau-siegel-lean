import ZhangLS.Spec.Lemma59ExtendedApproximation

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Complex in
lemma lemma59_ext_good_FG_bound {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ N) (s : ℂ) (hL : 100 ≤ lemma23PaperL D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma59InExtendedOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ +
      ‖lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s‖ ≤ 2 * lemma23PaperL D ^ 79 := by
  exact lemma59_extended_FG_bound χ ψ s hL hψ.2 hs

open Complex in
lemma lemma59_ext_good_product_bound {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ N) (s : ℂ) (hL : 100 ≤ lemma23PaperL D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma59InExtendedOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s *
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s - 1‖ ≤ 4 * lemma23PaperL D ^ (-227 : ℤ) := by
  exact lemma59_extended_product_bound χ ψ s hL hψ.2 hs

open Complex in
lemma lemma59_ext_F_logDeriv_at_threshold {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hs : Lemma59InExtendedOmega2 D s) :
    ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s‖ ≤ 140800 * lemma23PaperL D := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hL : 100 ≤ lemma23PaperL D := by
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  exact lemma59_extended_F_logDeriv_bound χ ψ s hL hp.2 hψ.2 hs

open Complex Set in
def Lemma59ExtendedZeroFreeRegion (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 + lemma44PaperAlpha D ^ 2 < s.re ∧ s.re < 1 ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13

open Complex ComplexConjugate Set in
def Lemma59ExtendedLocalStrip (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| < (lemma23PaperL D)⁻¹ ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 14

open Complex Metric Set Filter in
def Lemma59ExtendedLemma46Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    1 / 2 ≤ ρ.re → ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2 →
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13 →
    lemma45ActualA χ ψ ρ = 0 →
    0 < lemma46InnerRadius D c ∧
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0

open Complex ComplexConjugate Metric Set in
def Lemma59ExtendedZeroOmega (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| < 1 / 2 ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13

open Complex ComplexConjugate Set Filter in
theorem lemma59_ext45_horizontal_F_quotient_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hre : 1 / 2 ≤ s.re)
    (hnear : s.re < 1 / 2 + (lemma23PaperL D)⁻¹)
    (him : |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) /
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
        Real.exp (281600 * lemma23PaperL D * (s.re - 1 / 2)) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  let L := lemma23PaperL D
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))
  let H : ℝ → ℝ := fun x => Real.log ‖F ((x : ℂ) + I * (s.im : ℂ))‖
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hL : 3 ≤ L := hp.1
  have hLp : 0 < L := by linarith
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2])
      (mul_pos (by norm_num) (by linarith only [hp.1]))
  have hregion (x : ℝ) (hx : x ∈ Icc (1 - s.re) s.re) :
      Lemma59InExtendedOmega2 D ((x : ℂ) + I * (s.im : ℂ)) := by
    simp only [Lemma59InExtendedOmega2, add_re, ofReal_re, mul_re, I_re, I_im,
      ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, one_mul,
      zero_add]
    refine ⟨by linarith [hx.1], ?_, by linarith⟩
    change x < 1 + L⁻¹
    linarith [hx.2]
  have hregion1 (x : ℝ) (hx : x ∈ Icc (1 - s.re) s.re) :
      Lemma59InExtendedOmega1 D ((x : ℂ) + I * (s.im : ℂ)) :=
    lemma59_extended_disk_subset_omega1 hL100 hp.2 (hregion x hx)
      (Metric.mem_ball_self hR)
  have hd (x : ℝ) (hx : x ∈ Icc (1 - s.re) s.re) :
      HasDerivAt H
        (logDeriv F ((x : ℂ) + I * (s.im : ℂ))).re x :=
    lemma45_hasDerivAt_horizontal_log_norm
      (lemma44_short_polynomial_differentiable χ ψ _)
      (lemma59_extended_F_ne_zero χ ψ _ hL100 hψ.2 (hregion1 x hx))
  have hcont : ContinuousOn H (Icc (1 - s.re) s.re) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ H (interior (Icc (1 - s.re) s.re)) :=
    fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hbound : ∀ x ∈ interior (Icc (1 - s.re) s.re),
      -140800 * L ≤ deriv H x := by
    intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    have hb := lemma59_ext_F_logDeriv_at_threshold χ ψ _ hD hψ
      (hregion x (interior_subset hx))
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
    linarith
  have ho : 1 - s.re ≤ s.re := by linarith
  have hm := (convex_Icc (1 - s.re) s.re).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hbound (1 - s.re) ⟨le_rfl, ho⟩ s.re ⟨ho, le_rfl⟩ ho
  have hsEq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
    apply Complex.ext <;> simp
  have hrEq : ((1 - s.re : ℝ) : ℂ) + I * (s.im : ℂ) = conj (1 - s) := by
    apply Complex.ext <;> simp
  have hn := lemma59_extended_F_ne_zero χ ψ _ hL100 hψ.2
    (hregion1 s.re ⟨ho, le_rfl⟩)
  have hnr := lemma59_extended_F_ne_zero χ ψ _ hL100 hψ.2
    (hregion1 (1 - s.re) ⟨le_rfl, ho⟩)
  rw [hsEq] at hn
  rw [hrEq] at hnr
  rw [lemma45_short_sum_inv_eq_conj, norm_div, norm_conj]
  have hlog : Real.log (‖F (conj (1 - s))‖ / ‖F s‖) ≤
      281600 * L * (s.re - 1 / 2) := by
    rw [Real.log_div (norm_ne_zero_iff.mpr hnr) (norm_ne_zero_iff.mpr hn)]
    dsimp only [H] at hm
    rw [hsEq, hrEq] at hm
    linarith
  rw [← Real.exp_log (div_pos (norm_pos_iff.mpr hnr) (norm_pos_iff.mpr hn))]
  exact Real.exp_le_exp.mpr hlog

open Complex ComplexConjugate in
theorem lemma59_ext45_omega1_F_inv_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 100 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    (hs : Lemma59InExtendedOmega1 D s) :
    ‖(lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s)⁻¹‖ ≤
      4 * lemma23PaperL D ^ 79 := by
  have hL100 : 100 ≤ lemma23PaperL D := hL
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s
  let G := lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s
  have hn := lemma59_extended_F_ne_zero χ ψ s hL100 hψ.2 hs
  have h41 := lemma59_extended_FG_bound χ ψ s hL100 hψ.2 hs
  have h42 := lemma59_extended_product_bound χ ψ s hL100 hψ.2 hs
  have hp : 4 * lemma23PaperL D ^ (-227 : ℤ) ≤ 1 / 2 := by
    have hpow : (9 : ℝ) ≤ lemma23PaperL D ^ 227 := by
      have h2 : (9 : ℝ) ≤ lemma23PaperL D ^ 2 := by nlinarith
      exact h2.trans (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
    rw [zpow_neg, zpow_ofNat]
    have hi := (inv_le_inv₀ (by positivity : 0 < lemma23PaperL D ^ 227)
      (by norm_num : (0 : ℝ) < 9)).mpr hpow
    norm_num at hi
    linarith
  have hprod : 1 / 2 ≤ ‖F‖ * ‖G‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (F * G)
    rw [norm_one, norm_sub_rev, norm_mul] at ht
    change ‖F * G - 1‖ ≤ _ at h42
    linarith
  have hG : ‖G‖ ≤ 2 * lemma23PaperL D ^ 79 := by
    change ‖F‖ + ‖G‖ ≤ _ at h41
    linarith [norm_nonneg F]
  change ‖F⁻¹‖ ≤ _
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  have hm := mul_le_mul_of_nonneg_left hG (norm_nonneg F)
  nlinarith

open Complex in
def Lemma59ExtendedLemma48Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    Lemma59ExtendedZeroOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      C * lemma23PaperL D ^ (-100 : ℤ)

open Complex ComplexConjugate in
theorem lemma59_ext45_equation410 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (hs1 : Lemma59InExtendedOmega1 D s) :
    ‖lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)‖ ≤
      (4 * lemma44ErrorConstant) * lemma23PaperL D ^ (-100 : ℤ) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hn := lemma59_extended_F_ne_zero χ ψ s hL100 hψ.2 hs1
  have he := lemma59_ext44_actual_approximate_functional_equation χ ψ hD hψ hs
  have hi := lemma59_ext45_omega1_F_inv_bound χ ψ s hL100 hψ hs1
  have hid : lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s) =
      (DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
        (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
          lemma44ActualZtilde χ ψ s *
            lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))) *
        (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s)⁻¹ := by
    unfold lemma45ActualA lemma45ActualB
    field_simp
    <;> ring
  rw [hid, norm_mul]
  have hm := mul_le_mul he hi (norm_nonneg _)
    (mul_nonneg lemma44_error_constant_pos.le (by positivity))
  apply hm.trans_eq
  have hpow : lemma23PaperL D ^ (-179 : ℤ) * lemma23PaperL D ^ 79 =
      lemma23PaperL D ^ (-100 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ (by linarith : lemma23PaperL D ≠ 0)]
    norm_num
  calc
    _ = (4 * lemma44ErrorConstant) *
        (lemma23PaperL D ^ (-179 : ℤ) * lemma23PaperL D ^ 79) := by ring
    _ = _ := by rw [hpow]

open Complex Set in
theorem lemma59_ext45_region_subsets {D : ℕ} {s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hs : Lemma59ExtendedZeroFreeRegion D s) :
    Lemma59InExtendedOmega1 D s ∧ Lemma59ExtendedOmega3 D s ∧
      Lemma44InExtendedGammaRegion D s ∧ 1 / 2 < s.re := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have ha := lemma44_alpha_pos_le_one hp.1
  have hre : 1 / 2 < s.re := by linarith [sq_nonneg (lemma44PaperAlpha D), hs.1]
  have hr : 0 < Real.log (lemma23PaperL D) / (100 * lemma23PaperL D) :=
    div_pos (by linarith only [hp.2])
      (mul_pos (by norm_num) (by linarith only [hp.1]))
  have hs3 : Lemma59ExtendedOmega3 D s :=
    ⟨by linarith, by linarith [hs.2.1], by linarith [hs.2.2]⟩
  exact ⟨⟨by linarith, by linarith [hs.2.1], by linarith [hs.2.2]⟩,
    hs3, lemma59_ext44_omega3_subset_extended_gamma_region hp.1 hs3, hre⟩

open Complex Metric Set in
theorem lemma59_ext46_disk_subset_local_strip {D : ℕ} {c s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hs : ‖s - c‖ < 2 * lemma44PaperAlpha D) : Lemma59ExtendedLocalStrip D s := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hp := lemma46_alpha_parameters hD
  have hr : |s.re - 1 / 2| ≤ ‖s - c‖ := by
    simpa only [sub_re, hc] using abs_re_le_norm (s - c)
  have hi := abs_im_le_norm (s - c)
  have ht := abs_add_le (s.im - c.im) (c.im - (lemma23PaperCenter D).im)
  rw [sub_add_sub_cancel] at ht
  refine ⟨hr.trans_lt (hs.trans hp.2.2.1), ?_⟩
  simp only [sub_im] at hi
  linarith [hp.2.1]

open Complex ComplexConjugate Set in
theorem lemma59_ext46_local_strip_regions {D : ℕ} {s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hs : Lemma59ExtendedLocalStrip D s) :
    Lemma59InExtendedOmega2 D s ∧ Lemma59InExtendedOmega2 D (conj (1 - s)) ∧
      Lemma59ExtendedGammaRegion D s ∧ 0 < s.im := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hi : (lemma23PaperL D)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hr := abs_lt.mp hs.1
  have hs2 : Lemma59InExtendedOmega2 D s :=
    ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hs2r : Lemma59InExtendedOmega2 D (conj (1 - s)) := by
    simp only [Lemma59InExtendedOmega2, conj_re, sub_re, one_re,
      conj_im, sub_im, one_im, zero_sub, neg_neg]
    exact ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hgamma : Lemma59ExtendedGammaRegion D s :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hext : Lemma44InExtendedGammaRegion D s :=
    ⟨by linarith [hs.1], by linarith [hs.2, pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405]⟩
  exact ⟨hs2, hs2r, hgamma,
    (lemma44_extended_gamma_region_height hp.1 hext).2.2.1⟩

end ZhangLS.Spec
