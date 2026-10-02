import ZhangLS.Spec.Lemma57PrincipalPart
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian absorption of strip growth

Mathlib supplies analytic continuation and functional equations for the zeta
and Dirichlet L-functions, but currently no ready-made vertical-strip growth
estimate strong enough for Zhang's contour shift.  This module isolates that
missing input as a conventional exponential-type bound for the undamped
factor, away from its pole at zero.

The results below prove that the Gaussian Mellin factor absorbs every such
exponential bound both on the left vertical line and on the two horizontal
edges.  Thus the full contour-shift identity is reduced to a genuine growth
estimate about zeta and the Dirichlet L-function, not assumed directly.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Filter Set
open scoped Real Topology

/-- The part of Zhang's Mellin integrand before Gaussian damping. -/
noncomputable def lemma57UndampedMellinFactor {D : ℕ}
    (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  riemannZeta (1 + s) * dirichletLFunction χ (1 + s) / s

/-- A standard vertical-strip growth input, deliberately stated only away
from the pole.  The fixed lower norm cutoff covers the whole left line and all
horizontal edges of height at least one. -/
def Lemma57StripExponentialGrowth {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Prop :=
  ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    ∀ (σ t : ℝ), -(1 : ℝ) / 2 ≤ σ → σ ≤ 1 →
      (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ →
      ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (A * |t|)

/-- The genuine Mellin integrand is the undamped factor times the Gaussian
Mellin factor. -/
theorem lemma57MellinIntegrand_eq_undamped_mul_gaussian
    {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    lemma57MellinIntegrand χ s =
      lemma57UndampedMellinFactor χ s * lemma57GaussianMellinFactor D s := by
  simp only [lemma57MellinIntegrand, lemma57UndampedMellinFactor]
  ring

/-- Exact Gaussian norm on an arbitrary vertical line. -/
theorem lemma57GaussianMellinFactor_norm_vertical
    {D : ℕ} (hD : 1 < D) (σ t : ℝ) :
    ‖lemma57GaussianMellinFactor D ((σ : ℂ) + (t : ℂ) * I)‖ =
      Real.exp
        (4 * Real.log (D : ℝ) * σ +
          (σ ^ 2 - t ^ 2) / (4 * Real.log (D : ℝ) ^ 30)) := by
  rw [lemma57GaussianMellinFactor, norm_exp]
  congr 1
  have hL : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD)
  have hden : 4 * Real.log (D : ℝ) ^ 30 ≠ 0 := by positivity
  rw [Complex.add_re]
  have hlinear :
      (((4 * (Real.log (D : ℝ) : ℂ)) *
        ((σ : ℂ) + (t : ℂ) * I))).re =
          4 * Real.log (D : ℝ) * σ := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    norm_num
  rw [hlinear]
  congr 1
  have hsq :
      ((((σ : ℂ) + (t : ℂ) * I) ^ 2)).re = σ ^ 2 - t ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp
    ring
  have hcast :
      (4 * (Real.log (D : ℝ) : ℂ) ^ 30) =
        ((4 * Real.log (D : ℝ) ^ 30 : ℝ) : ℂ) := by
    push_cast
    ring
  have hinv :
      (((4 * Real.log (D : ℝ) ^ 30 : ℝ) : ℂ)⁻¹) =
        (((4 * Real.log (D : ℝ) ^ 30)⁻¹ : ℝ) : ℂ) := by norm_cast
  rw [hcast, div_eq_mul_inv, hinv, Complex.mul_re, hsq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  field_simp [hden]

/-- A Gaussian absorbs an arbitrary real exponential in `|t|`. -/
theorem integrable_exp_neg_mul_sq_add_mul_abs
    {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-b * t ^ 2 + A * |t|)) := by
  let K : ℝ := Real.exp (b⁻¹ * A ^ 2 / 2)
  have hb2 : 0 < b / 2 := by positivity
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(b / 2) * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb2
  have hmajor : Integrable
      (fun t : ℝ => K * Real.exp (-(b / 2) * t ^ 2)) :=
    hgauss.const_mul K
  apply hmajor.mono
  · fun_prop
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hyoung := two_mul_le_add_mul_sq
      (a := |t|) (b := A) hb
    have habssq : |t| ^ 2 = t ^ 2 := sq_abs t
    rw [habssq] at hyoung
    nlinarith

/-- Exponential strip growth plus Zhang's Gaussian damping gives honest
Bochner integrability on the shifted line `re s = -1/2`. -/
theorem lemma57LeftVerticalIntegrable_of_stripExponentialGrowth
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hgrowth : Lemma57StripExponentialGrowth χ) :
    Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2) := by
  rcases hgrowth with ⟨C, A, hC, hA, hgrowth⟩
  let L : ℝ := Real.log (D : ℝ)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hD)
  let b : ℝ := 1 / (4 * L ^ 30)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  let K : ℝ := C * Real.exp (-2 * L + b / 4)
  have hmajor : Integrable
      (fun t : ℝ => K * Real.exp (-b * t ^ 2 + A * |t|)) :=
    (integrable_exp_neg_mul_sq_add_mul_abs hb A).const_mul K
  unfold Lemma57VerticalIntegrable
  apply hmajor.mono
  · apply Continuous.aestronglyMeasurable
    have hs : ∀ t : ℝ,
        ((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro t h
      have hr := congrArg Complex.re h
      norm_num at hr
    have hm : Continuous
        (fun t : ℝ => lemma57MellinIntegrand χ
          (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ContinuousAt.comp'
        (lemma57MellinIntegrand_differentiableAt χ hD (hs t)).continuousAt
        (by fun_prop)
    exact hm.mul (continuous_const : Continuous fun _ : ℝ => (I : ℂ))
  · filter_upwards [] with t
    have hlineNorm :
        (1 : ℝ) / 2 ≤
          ‖((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
      calc
        (1 : ℝ) / 2 =
            |((((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| := by norm_num
        _ ≤ ‖((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
          Complex.abs_re_le_norm _
    have hu := hgrowth (-(1 : ℝ) / 2) t (by norm_num) (by norm_num) hlineNorm
    have hgauss := lemma57GaussianMellinFactor_norm_vertical hD
      (-(1 : ℝ) / 2) t
    rw [lemma57MellinIntegrand_eq_undamped_mul_gaussian, norm_mul, norm_mul,
      norm_I, mul_one, hgauss]
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK (Real.exp_pos _).le)]
    calc
      ‖lemma57UndampedMellinFactor χ
          (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
          Real.exp
            (4 * Real.log (D : ℝ) * (-(1 : ℝ) / 2) +
              ((-(1 : ℝ) / 2) ^ 2 - t ^ 2) /
                (4 * Real.log (D : ℝ) ^ 30)) ≤
          (C * Real.exp (A * |t|)) *
            Real.exp
              (4 * Real.log (D : ℝ) * (-(1 : ℝ) / 2) +
                ((-(1 : ℝ) / 2) ^ 2 - t ^ 2) /
                  (4 * Real.log (D : ℝ) ^ 30)) := by
        gcongr
      _ = K * Real.exp (-b * t ^ 2 + A * |t|) := by
        dsimp [K, b, L]
        simp only [mul_assoc, ← Real.exp_add]
        congr 2
        field_simp
        ring

/-- The elementary one-sided limit used for the horizontal edges: a negative
quadratic exponential absorbs every real linear exponential. -/
theorem tendsto_exp_neg_mul_sq_add_mul_atTop
    {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-b * t ^ 2 + A * t)) atTop (nhds 0) := by
  let K : ℝ := Real.exp (b⁻¹ * A ^ 2 / 2)
  have hquad : Tendsto (fun t : ℝ => -(b / 2) * t ^ 2) atTop atBot :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith)
  have hupper : Tendsto
      (fun t : ℝ => K * Real.exp (-(b / 2) * t ^ 2)) atTop (nhds 0) := by
    simpa using Tendsto.const_mul K (Real.tendsto_exp_atBot.comp hquad)
  refine squeeze_zero (fun t => by positivity) ?_ hupper
  intro t
  change Real.exp (-b * t ^ 2 + A * t) ≤
    K * Real.exp (-(b / 2) * t ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyoung := two_mul_le_add_mul_sq (a := t) (b := A) hb
  nlinarith

private theorem lemma57MellinIntegrand_norm_horizontal_le
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C A : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ (σ t : ℝ), -(1 : ℝ) / 2 ≤ σ → σ ≤ 1 →
      (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ →
      ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (A * |t|))
    {σ t : ℝ} (hσ0 : -(1 : ℝ) / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 ≤ |t|) :
    ‖lemma57MellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      C * Real.exp (4 * Real.log (D : ℝ) +
        1 / (4 * Real.log (D : ℝ) ^ 30)) *
          Real.exp (-(1 / (4 * Real.log (D : ℝ) ^ 30)) * t ^ 2 + A * |t|) := by
  have hlineNorm :
      (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
    calc
      (1 : ℝ) / 2 ≤ |t| := by linarith
      _ = |(((σ : ℂ) + (t : ℂ) * I)).im| := by simp
      _ ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := Complex.abs_im_le_norm _
  have hu := hgrowth σ t hσ0 hσ1 hlineNorm
  have hgauss := lemma57GaussianMellinFactor_norm_vertical hD σ t
  have hL : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD)
  have hsigmasq : σ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - σ)
      (by linarith : 0 ≤ 1 + σ)]
  have hexponent :
      4 * Real.log (D : ℝ) * σ +
          (σ ^ 2 - t ^ 2) / (4 * Real.log (D : ℝ) ^ 30) ≤
        4 * Real.log (D : ℝ) +
          1 / (4 * Real.log (D : ℝ) ^ 30) -
            (1 / (4 * Real.log (D : ℝ) ^ 30)) * t ^ 2 := by
    have hden : 0 < 4 * Real.log (D : ℝ) ^ 30 := by positivity
    have hlin :
        4 * Real.log (D : ℝ) * σ ≤ 4 * Real.log (D : ℝ) := by
      nlinarith
    have hq : 0 ≤ (4 * Real.log (D : ℝ) ^ 30)⁻¹ :=
      inv_nonneg.mpr hden.le
    have hsigmaScaled := mul_le_mul_of_nonneg_left hsigmasq hq
    simp only [div_eq_mul_inv, one_mul]
    nlinarith
  rw [lemma57MellinIntegrand_eq_undamped_mul_gaussian, norm_mul, hgauss]
  calc
    ‖lemma57UndampedMellinFactor χ ((σ : ℂ) + (t : ℂ) * I)‖ *
        Real.exp
          (4 * Real.log (D : ℝ) * σ +
            (σ ^ 2 - t ^ 2) / (4 * Real.log (D : ℝ) ^ 30)) ≤
      (C * Real.exp (A * |t|)) *
        Real.exp
          (4 * Real.log (D : ℝ) * σ +
            (σ ^ 2 - t ^ 2) / (4 * Real.log (D : ℝ) ^ 30)) := by
      gcongr
    _ ≤ (C * Real.exp (A * |t|)) *
        Real.exp
          (4 * Real.log (D : ℝ) +
            1 / (4 * Real.log (D : ℝ) ^ 30) -
              (1 / (4 * Real.log (D : ℝ) ^ 30)) * t ^ 2) := by
      gcongr
    _ = _ := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Exponential strip growth forces both horizontal edges of Zhang's
rectangle to vanish.  This is where the Gaussian factor does the substantive
analytic work: its negative quadratic exponent dominates the allowed linear
exponential growth. -/
theorem lemma57HorizontalDecay_of_stripExponentialGrowth
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hgrowth : Lemma57StripExponentialGrowth χ) :
    Lemma57HorizontalDecay χ := by
  rcases hgrowth with ⟨C, A, hC, hA, hgrowth⟩
  let b : ℝ := 1 / (4 * Real.log (D : ℝ) ^ 30)
  have hb : 0 < b := by
    dsimp [b]
    have hL : 0 < Real.log (D : ℝ) :=
      Real.log_pos (by exact_mod_cast hD)
    positivity
  let P : ℝ := C * Real.exp (4 * Real.log (D : ℝ) + b)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  let q : ℝ → ℝ := fun T => Real.exp (-b * T ^ 2 + A * T)
  have hq0 : Tendsto q atTop (nhds 0) := by
    simpa [q] using tendsto_exp_neg_mul_sq_add_mul_atTop hb A
  let N : ℝ :=
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (3 * P)
  have hNq0 : Tendsto (fun T => N * q T) atTop (nhds 0) := by
    simpa using Tendsto.const_mul N hq0
  unfold Lemma57HorizontalDecay
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hNq0
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hTabs : 1 ≤ |T| := by simpa [abs_of_nonneg hT0] using hT
  have htop :
      ‖∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          lemma57MellinIntegrand χ ((x : ℂ) + (T : ℂ) * I)‖ ≤
        P * q T * ((3 : ℝ) / 2) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-(1 : ℝ) / 2)) (b := 1) (C := P * q T)
      (f := fun x : ℝ =>
        lemma57MellinIntegrand χ ((x : ℂ) + (T : ℂ) * I))
      (fun x hx => by
        have hx' : x ∈ Set.uIcc (-(1 : ℝ) / 2) 1 :=
          Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num)] at hx'
        have hp := lemma57MellinIntegrand_norm_horizontal_le χ hD hC
          hgrowth (σ := x) (t := T) hx'.1 hx'.2 hTabs
        simpa [P, q, b, abs_of_nonneg hT0] using hp)
    convert hbound using 1
    norm_num
  have hbottom :
      ‖∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          lemma57MellinIntegrand χ ((x : ℂ) - (T : ℂ) * I)‖ ≤
        P * q T * ((3 : ℝ) / 2) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-(1 : ℝ) / 2)) (b := 1) (C := P * q T)
      (f := fun x : ℝ =>
        lemma57MellinIntegrand χ ((x : ℂ) - (T : ℂ) * I))
      (fun x hx => by
        have hx' : x ∈ Set.uIcc (-(1 : ℝ) / 2) 1 :=
          Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num)] at hx'
        have hp := lemma57MellinIntegrand_norm_horizontal_le χ hD hC
          hgrowth (σ := x) (t := -T) hx'.1 hx'.2
            (by simpa only [abs_neg] using hTabs)
        simpa [P, q, b, abs_of_nonneg hT0, sub_eq_add_neg] using hp)
    convert hbound using 1
    norm_num
  unfold lemma57HorizontalIntegralError
  rw [norm_mul]
  calc
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          ‖(∫ x : ℝ in (-(1 : ℝ) / 2)..1,
              lemma57MellinIntegrand χ ((x : ℂ) + (T : ℂ) * I)) -
            ∫ x : ℝ in (-(1 : ℝ) / 2)..1,
              lemma57MellinIntegrand χ ((x : ℂ) - (T : ℂ) * I)‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (‖∫ x : ℝ in (-(1 : ℝ) / 2)..1,
              lemma57MellinIntegrand χ ((x : ℂ) + (T : ℂ) * I)‖ +
            ‖∫ x : ℝ in (-(1 : ℝ) / 2)..1,
              lemma57MellinIntegrand χ ((x : ℂ) - (T : ℂ) * I)‖) := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (P * q T * ((3 : ℝ) / 2) + P * q T * ((3 : ℝ) / 2)) := by
          gcongr
    _ = N * q T := by
          dsimp [N]
          ring

/-- The full contour-shift identity follows from one conventional
vertical-strip growth theorem for the undamped zeta--Dirichlet-L factor. -/
theorem lemma57ContourShiftIdentity_of_stripExponentialGrowth
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hgrowth : Lemma57StripExponentialGrowth χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_left_integrable_horizontal_decay χ hD
    (lemma57LeftVerticalIntegrable_of_stripExponentialGrowth χ hD hgrowth)
    (lemma57HorizontalDecay_of_stripExponentialGrowth χ hD hgrowth)

end ZhangLS.Spec
