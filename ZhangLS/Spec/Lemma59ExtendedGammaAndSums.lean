import ZhangLS.Spec.Lemma59ZeroRemovedShift
import ZhangLS.Spec.Lemma44ApproximateFunctionalEquation
import ZhangLS.Spec.Lemma59UniformPolynomialInputs
import ZhangLS.Spec.Lemma48InverseFactor
import ZhangLS.Spec.Lemma59FiniteZeroProducts
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Finset.Sort

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma59_extended_height_margin {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma23PaperL D ^ 20 + 20 ≤ lemma23PaperL D ^ 405 := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hp20 : 1 ≤ lemma23PaperL D ^ 20 := one_le_pow₀ hL1
  have hp3 : (3 : ℝ) ^ 3 ≤ lemma23PaperL D ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have hpow : lemma23PaperL D ^ 3 ≤ lemma23PaperL D ^ 385 := pow_le_pow_right₀ hL1 (by norm_num)
  norm_num at hp3
  have hm := mul_le_mul_of_nonneg_left (hp3.trans hpow) (by positivity : 0 ≤ lemma23PaperL D ^ 20)
  have he : lemma23PaperL D ^ 20 * lemma23PaperL D ^ 385 = lemma23PaperL D ^ 405 := by rw [← pow_add]
  rw [he] at hm
  nlinarith only [hm,hp20]

open Complex in
def Lemma59ExtendedGammaRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| ≤ 100 ∧
    |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20

open MeasureTheory Complex in
def Lemma59ExtendedOmega3 (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 - lemma44PaperAlpha D < s.re ∧ s.re < 1 + lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 19

open Complex in
theorem lemma59_ext44_gamma_region_height {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma59ExtendedGammaRegion D s) :
    24 ≤ |s.im| ∧ |s.re| + 2 ≤ |s.im| / 4 ∧
      Real.log (3 * |s.im|) ≤ 550 * lemma23PaperL D := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  let L := lemma23PaperL D
  have hL3 : 3 ≤ L := hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hpow : L ^ 405 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
  have hpow3 : 3 ≤ L ^ 519 := (show L ≤ L ^ 519 from le_self_pow₀ hL1 (by norm_num))
    |>.trans' hL3
  have hpow729 : 729 ≤ L ^ 519 := by
    have h₆ : (3 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL3 6
    have h₆' : L ^ 6 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
    norm_num at h₆
    exact h₆.trans h₆'
  have him : |s.im - 2 * Real.pi * L ^ 519| ≤ L ^ 405 + 20 := hs.2
  have himlo : L ^ 519 ≤ s.im := by
    have h := (abs_le.mp him).1
    have hpi := Real.one_le_pi_div_two
    nlinarith
  have himhi : s.im ≤ 10 * L ^ 519 := by
    have h := (abs_le.mp him).2
    nlinarith [Real.pi_le_four]
  have hspos : 0 ≤ s.im := by linarith
  rw [abs_of_nonneg hspos]
  have hre : |s.re| ≤ 101 := by
    have h := abs_add_le (s.re - 1 / 2) (1 / 2 : ℝ)
    norm_num at h
    have hreal := hs.1
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  have htpos : 0 < 3 * s.im := by linarith
  calc
    Real.log (3 * s.im) ≤ Real.log (30 * L ^ 519) :=
      Real.log_le_log htpos (by linarith)
    _ = Real.log 30 + 519 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    _ ≤ 550 * L := by
      have hlogL := Real.log_le_self hLpos.le
      have hlog30 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 30)
      nlinarith

open Complex ComplexConjugate in
theorem lemma59_ext44_middle_reflected_displacement {D : ℕ} {s : ℂ} {v : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma59ExtendedOmega3 D s)
    (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v‖ ≤
      4 * lemma23PaperL D ^ 405 := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have ha := lemma44_alpha_pos_le_one hL
  have hre : |(lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).re| ≤ 2 := by
    have heq : (lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).re =
        1 / 2 - (1 + lemma44PaperAlpha D - s.re) := by
      simp [lemma44MiddleReflectedArgument, lemma23PaperCenter]
    rw [heq]
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2.1]
  have hp : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  have him : |(lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).im| ≤
      2 * lemma23PaperL D ^ 405 + 3 := by
    have htri := abs_add_le ((lemma23PaperCenter D).im - s.im) (-v)
    simp only [abs_neg, abs_sub_comm] at htri
    have heq : (lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v).im =
        (lemma23PaperCenter D).im - s.im - v := by
      simp [lemma44MiddleReflectedArgument]
      ring
    rw [heq]
    have htri' : |(lemma23PaperCenter D).im - s.im - v| ≤
        |s.im - (lemma23PaperCenter D).im| + |v| := by
      simpa only [sub_eq_add_neg] using htri
    exact htri'.trans (by linarith [hs.2.2])
  have hpow : 3 ≤ lemma23PaperL D ^ 405 :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

open MeasureTheory Complex in
theorem lemma59_ext44_omega3_displacement {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405 := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have ha := lemma44_alpha_pos_le_one hL
  have hre : |(lemma23PaperCenter D - s).re| ≤ 2 := by
    change |1 / 2 - s.re| ≤ 2
    have hreal := hs.1
    have hreal' := hs.2.1
    apply abs_le.mpr
    constructor <;> linarith [ha.2]
  have him : |(lemma23PaperCenter D - s).im| ≤ lemma23PaperL D ^ 405 + 19 := by
    simpa [abs_sub_comm] using hs.2.2.le
  have hpow : 3 ≤ lemma23PaperL D ^ 405 :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

open Complex MeasureTheory in
theorem lemma59_ext44_omega3_re_pos {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) : 0 < s.re := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have h3 : (3 : ℝ) ^ 3 ≤ lemma23PaperL D ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have h39 : lemma23PaperL D ^ 3 ≤ lemma23PaperL D ^ 9 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have ha : lemma44PaperAlpha D ≤ 1 / 4 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    apply (div_le_iff₀ (pow_pos hL0 9)).mpr
    norm_num at h3
    nlinarith only [h3, h39, Real.pi_le_four]
  linarith only [hs.1, ha]

open Complex Set in
theorem lemma59_ext44_omega3_subset_extended_gamma_region {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma59ExtendedOmega3 D s) :
    Lemma44InExtendedGammaRegion D s := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have ha := lemma44_alpha_pos_le_one hL
  refine ⟨?_, ?_⟩
  · apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2.1]
  · have hp : 0 ≤ lemma23PaperL D ^ 405 := by positivity
    linarith [hs.2.2]

open Complex MeasureTheory Set in
theorem lemma59_ext44_right_mellin_gaussian_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (v : ℝ) :
    ‖lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I‖ ≤
      (lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * lemma23PaperL D ^ 9)) *
        Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let w : ℂ := 1 + (v : ℂ) * I
  have hL0 : 0 < lemma23PaperL D := by linarith
  have ha : lemma44PaperAlpha D ≤ 1 / 4 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    apply (div_le_iff₀ (pow_pos hL0 9)).mpr
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
    have h39 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show 3 ≤ 9 by norm_num)
    norm_num at h3
    nlinarith only [h3, h39, Real.pi_le_four]
  have hz : 5 / 4 ≤ (s + w).re := by simp [w]; linarith only [hs.1, ha]
  have hp := lemma44_product_series_norm_le_divisor_mass χ ψ hz
  rw [norm_mul] at hp
  have hmass := lemma44_divisor_series_mass_nonneg
  have hn : 1 ≤ ‖w‖ := by simpa [w] using Complex.abs_re_le_norm w
  have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hscale : ‖exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ =
      Real.exp ((9 / 5 : ℝ) * lemma23PaperL D ^ 9) := by
    rw [norm_exp, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero,
      lemma44_paper_gaussian_scale_log]
    simp [w]
  have homega : ‖lemma57OmegaOne D w‖ ≤
      Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2) := by
    change ‖lemma57OmegaOne D (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
    rw [lemma44_Omega_norm_vertical, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 < lemma23PaperL D := by linarith
    have hp30 : 1 ≤ lemma23PaperL D ^ 30 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    field_simp
    nlinarith only [hp30]
  unfold lemma44ProductMellinIntegrand
  change ‖(DirichletCharacter.LFunction ψ (s + w) *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w)) *
    exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) * lemma57OmegaOne D w / w * I‖ ≤ _
  simp only [norm_mul, norm_inv, norm_I, mul_one, div_eq_mul_inv]
  rw [hscale]
  calc
    _ ≤ lemma44DivisorSeriesMass * Real.exp ((9 / 5 : ℝ) * lemma23PaperL D ^ 9) *
        (Real.exp 1 * Real.exp (-(1 / (4 * lemma23PaperL D ^ 30)) * v ^ 2)) * 1 := by
      exact mul_le_mul (mul_le_mul
        (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)) homega
        (norm_nonneg _) (by positivity)) hinv (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

open Complex Set in
theorem lemma59_ext44_truncated_shift_in_extended_gamma_region {D : ℕ} {s w : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma59ExtendedOmega3 D s)
    (hwre : |w.re| ≤ 15) (hwim : |w.im| ≤ lemma23PaperL D ^ 20) :
    Lemma44InExtendedGammaRegion D (s + w) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have ha := lemma44_alpha_pos_le_one hL
  have hre : |s.re - 1 / 2| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2.1]
  have hp : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  constructor
  · change |s.re + w.re - 1 / 2| ≤ 100
    have ht := abs_add_le (s.re - 1 / 2) w.re
    rw [sub_add_eq_add_sub] at ht
    linarith
  · change |s.im + w.im - (lemma23PaperCenter D).im| ≤ _
    have ht := abs_add_le (s.im - (lemma23PaperCenter D).im) w.im
    rw [sub_add_eq_add_sub] at ht
    linarith [hs.2.2]

open Complex Set in
theorem lemma59_ext44ActualZtilde_norm_on_omega3 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44ActualZtilde χ ψ s‖ ≤
      Real.exp 1 * Real.exp ((1 - 2 * s.re) * Real.log (lemma23PaperP D)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hregion := lemma59_ext44_omega3_subset_extended_gamma_region hL hs
  by_cases hre : 1 / 2 ≤ s.re
  · have hb := lemma44ActualZtilde_norm_le_right χ ψ hD hψ hregion hre
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg
      ((1 - 2 * s.re) * Real.log (lemma23PaperP D)))
    simpa only [one_mul] using hm
  · have hb := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hregion (le_of_not_ge hre)
    have hsmall : 3 * lemma23PaperL D * (1 / 2 - s.re) ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left (show 1 / 2 - s.re ≤ lemma44PaperAlpha D by
        linarith [hs.1]) (by linarith : 0 ≤ 3 * lemma23PaperL D)
      exact hm.trans (lemma44_alpha_horizontal_loss hL)
    apply hb.trans
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hsmall])

open Complex in
theorem lemma59_ext44_equation46 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedGammaRegion D s) :
    ‖logDeriv (lemma44ActualZtilde χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)‖ ≤ 60000 * lemma23PaperL D := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have hheight := lemma59_ext44_gamma_region_height hL hs
  have hfactor := lemma44_productZ_logDeriv_bound ψ (lemma44CharacterTwist χ ψ)
    hψ.2.1 htwist hpne hDpne hheight.1 hheight.2.1
  change ‖logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
    Complex.log ((D * p : ℕ) : ℂ)‖ ≤ _ at hfactor
  have hπ : ‖Complex.log (Real.pi : ℂ)‖ ≤ 4 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.one_le_pi_div_two]))]
    exact (Real.log_le_self Real.pi_pos.le).trans Real.pi_le_four
  have hfactor' : ‖logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
      Complex.log ((D * p : ℕ) : ℂ)‖ ≤ 59000 * lemma23PaperL D := by
    apply hfactor.trans
    nlinarith [hheight.2.2, Real.pi_le_four]
  have hlogDp : Complex.log ((D * p : ℕ) : ℂ) =
      ((lemma23PaperL D + Real.log (p : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.natCast_log, Nat.cast_mul, Real.log_mul
      (by exact_mod_cast χ.modulus_ne_zero) (by exact_mod_cast NeZero.ne p)]
    rfl
  have hlogp : Complex.log (p : ℂ) = ((Real.log (p : ℝ) : ℝ) : ℂ) :=
    (Complex.natCast_log (n := p)).symm
  have hlogbounds := lemma44_family_log_bound hL ψ hψ
  let E : ℝ := lemma23PaperL D + 2 *
    (Real.log (p : ℝ) - Real.log (lemma23PaperP D))
  have hE : 0 ≤ E ∧ E ≤ lemma23PaperL D + 2 := by dsimp [E]; constructor <;> linarith
  have heq : logDeriv (lemma44ActualZtilde χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ) =
      (logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
        Complex.log ((D * p : ℕ) : ℂ)) - (E : ℂ) := by
    rw [hlogDp, hlogp]
    dsimp [E]
    push_cast
    ring
  rw [heq]
  have hnormE : ‖(E : ℂ)‖ ≤ lemma23PaperL D + 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE.1]
    exact hE.2
  exact (norm_sub_le _ _).trans (by linarith)

open Complex MeasureTheory in
theorem lemma59_ext44_gaussian_long_sum_on_omega3 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {B : ℝ} (hB : 0 < B) :
    ‖lemma44GaussianLongDirichletSum χ ψ s B‖ ≤
      5 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hLpos : 0 < lemma23PaperL D := by linarith
  have ha := lemma44_alpha_pos_le_one hL
  have hmax : max 0 (1 / 2 - s.re) ≤ lemma44PaperAlpha D :=
    max_le ha.1.le (by linarith [hs.1])
  have halpha : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have hexp : Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) ≤
      Real.exp (2 * Real.pi) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmax (pow_pos hLpos 9).le
    rw [halpha] at h
    linarith
  have hb := lemma44_gaussian_long_sum_L180_of_displacement χ ψ s hL hψ.2
    (lemma59_ext44_omega3_displacement hL hs) hB
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end ZhangLS.Spec
