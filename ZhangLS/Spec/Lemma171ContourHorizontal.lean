import ZhangLS.Spec.Lemma171ContourGrowth
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Lemma 17.1: vanishing horizontal Gaussian integrals -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Classical Topology

noncomputable def lemma171HorizontalConstant (D : ℕ) : ℝ :=
  lemma171StripConstant D*
    Real.exp (lemma23PaperL D^(11/10:ℝ)+1/(4*lemma23PaperL D^30))*
    (1+16*lemma23PaperL D^30)^2

lemma lemma171_mellin_horizontal_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (σ t : ℝ) (hlo : -1/4 ≤ σ) (hhi : σ ≤ 1)
    (ht : 1 ≤ |t|) :
    ‖lemma171MellinIntegrand χ ((σ : ℂ)+(t : ℂ)*I)‖ ≤
      lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)) := by
  let L := lemma23PaperL D
  let b : ℝ := (16*L^30)⁻¹
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hD)
  have hb : 0 < b := by dsimp [b];positivity
  have hln : 0 ≤ L^(11/10:ℝ) := Real.rpow_nonneg hL.le _
  have hnorm : 1/4 ≤ ‖(σ : ℂ)+(t : ℂ)*I‖ := by
    have hh := Complex.abs_im_le_norm ((σ : ℂ)+(t : ℂ)*I)
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero] at hh
    linarith
  have hu := lemma171_undamped_strip_bound χ hD ((σ : ℂ)+(t : ℂ)*I)
    (by simpa using hlo) (by simpa using hhi) hnorm
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero] at hu
  have he : L^(11/10:ℝ)*σ+(σ^2-t^2)/(4*L^30) ≤
      L^(11/10:ℝ)+1/(4*L^30)-(4*b)*t^2 := by
    have hsq : σ^2 ≤ 1 := by nlinarith
    have hmul : L^(11/10:ℝ)*σ ≤ L^(11/10:ℝ) :=
      mul_le_of_le_one_right hln hhi
    have hd : 0 < 4*L^30 := by positivity
    have hfrac : (σ^2-t^2)/(4*L^30) ≤ (1-t^2)/(4*L^30) :=
      div_le_div_of_nonneg_right (by linarith) hd.le
    have heq : (1-t^2)/(4*L^30) = 1/(4*L^30)-(4*b)*t^2 := by
      dsimp [b];field_simp;ring
    rw [heq] at hfrac
    linarith
  have hk := (lemma171_strip_constant_pos χ.modulus_pos).le
  rw [lemma171_mellin_eq_undamped D χ,norm_mul,lemma171_gaussian_norm_vertical]
  calc
    _ ≤ (lemma171StripConstant D*(1+t^2)^2)*
        Real.exp (L^(11/10:ℝ)+1/(4*L^30)-(4*b)*t^2) :=
      mul_le_mul hu (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    _ = (lemma171StripConstant D*Real.exp (L^(11/10:ℝ)+1/(4*L^30)))*
        ((1+t^2)^2*Real.exp (-(4*b)*t^2)) := by
      rw [Real.exp_sub]
      simp only [neg_mul,Real.exp_neg]
      ring
    _ ≤ (lemma171StripConstant D*Real.exp (L^(11/10:ℝ)+1/(4*L^30)))*
        ((1+b⁻¹)^2*Real.exp (-(2*b)*t^2)) :=
      mul_le_mul_of_nonneg_left (lemma171_quartic_gaussian_bound hb t) (by positivity)
    _ = _ := by
      unfold lemma171HorizontalConstant
      have hexp : -(2*b)*t^2 = -t^2/(8*L^30) := by dsimp [b];field_simp;ring
      rw [hexp]
      simp only [b,inv_inv]
      dsimp [L]
      ring

lemma lemma171_horizontal_integral_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖∫x:ℝ in (-1/4)..1,lemma171MellinIntegrand χ ((x:ℂ)+(t:ℂ)*I)‖ ≤
      (5/4)*lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)) := by
  have hbound : ∀ x ∈ Set.uIoc (-1/4:ℝ) 1,
      ‖lemma171MellinIntegrand χ ((x:ℂ)+(t:ℂ)*I)‖ ≤
      lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (-1/4:ℝ)≤1)] at hx
    exact lemma171_mellin_horizontal_bound χ hD x t hx.1.le hx.2 ht
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    _ ≤ (lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)))*
        |1-(-1/4:ℝ)| := hi
    _ = _ := by norm_num;ring

lemma lemma171_gaussian_height_tendsto_zero {D : ℕ} (hD : 1 < D) :
    Tendsto (fun t:ℝ => Real.exp (-t^2/(8*lemma23PaperL D^30))) atTop (𝓝 0) := by
  have hL : 0 < lemma23PaperL D := Real.log_pos (by exact_mod_cast hD)
  have hpos : 0 < 8*lemma23PaperL D^30 := by positivity
  have hp := (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).atTop_div_const hpos
  have hn := tendsto_neg_atTop_atBot.comp hp
  simpa only [neg_div] using Real.tendsto_exp_atBot.comp hn

lemma lemma171_upper_horizontal_decay {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Tendsto (fun T:ℝ => ∫x:ℝ in (-1/4)..1,
      lemma171MellinIntegrand χ ((x:ℂ)+(T:ℂ)*I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact lemma171_horizontal_integral_bound χ hD T
      (by rw [abs_of_nonneg (by linarith : 0≤T)];exact hT)
  · simpa only [mul_zero] using
      (lemma171_gaussian_height_tendsto_zero hD).const_mul ((5/4)*lemma171HorizontalConstant D)

lemma lemma171_lower_horizontal_decay {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Tendsto (fun T:ℝ => ∫x:ℝ in (-1/4)..1,
      lemma171MellinIntegrand χ ((x:ℂ)-(T:ℂ)*I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have hh := lemma171_horizontal_integral_bound χ hD (-T)
      (by rw [abs_neg,abs_of_nonneg (by linarith : 0≤T)];exact hT)
    simpa only [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg,neg_sq] using hh
  · simpa only [mul_zero] using
      (lemma171_gaussian_height_tendsto_zero hD).const_mul ((5/4)*lemma171HorizontalConstant D)

end ZhangLS.Spec
