import ZhangLS.Spec.Lemma81ActualLFunctionMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Actual Gaussian contour mass in Lemma 8.1

The original L^400 width and L^405 height are retained. The exact full
Gaussian mass gives a uniform bound for the original finite vertical contour.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Real Topology
set_option maxHeartbeats 2000000

noncomputable def lemma81GaussianDensity (D : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt Real.pi / lemma23PaperL D^400 *
    Real.exp (-(t^2)/(4*(lemma23PaperL D^400)^2))

lemma lemma81_omega_segment_norm {D : ℕ} (hL : 0 < lemma23PaperL D) (x t : ℝ) :
    ‖lemma81Omega D (lemma81SegmentPoint D x t)‖ =
      Real.sqrt Real.pi / lemma23PaperL D^400 *
        Real.exp ((x^2-t^2)/(4*(lemma23PaperL D^400)^2)) := by
  have he : lemma81SegmentPoint D x t-lemma23PaperCenter D = (x : ℂ)+I*(t : ℂ) := by
    unfold lemma81SegmentPoint
    ring
  unfold lemma81Omega
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.sqrt_pos.mpr Real.pi_pos) (pow_pos hL 400)),Complex.norm_exp]
  congr 2
  rw [Complex.div_ofReal_re]
  congr 1
  simp only [pow_two,mul_re,add_re,add_im,mul_im,I_re,I_im,ofReal_re,ofReal_im,
    zero_mul,mul_zero,one_mul,sub_zero,add_zero,zero_add]

lemma lemma81_omega_norm_density {D : ℕ} (hL : 0 < lemma23PaperL D) (x t : ℝ) :
    ‖lemma81Omega D (lemma81SegmentPoint D x t)‖ =
      Real.exp (x^2/(4*(lemma23PaperL D^400)^2)) * lemma81GaussianDensity D t := by
  rw [lemma81_omega_segment_norm hL]
  unfold lemma81GaussianDensity
  rw [sub_div,sub_eq_add_neg,Real.exp_add,← neg_div]
  ring

lemma lemma81_gaussian_density_integrable {D : ℕ} (hL : 0 < lemma23PaperL D) :
    Integrable (lemma81GaussianDensity D) := by
  have hb : 0 < (4*(lemma23PaperL D^400)^2)⁻¹ := by positivity
  convert (integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt Real.pi/lemma23PaperL D^400) using 1
  funext t
  unfold lemma81GaussianDensity
  congr 2
  ring

lemma lemma81_gaussian_density_mass {D : ℕ} (hL : 0 < lemma23PaperL D) :
    (∫ t : ℝ, lemma81GaussianDensity D t) = 2*Real.pi := by
  let W := lemma23PaperL D^400
  have hW : 0 < W := pow_pos hL 400
  have he : (fun t : ℝ => Real.exp (-(t^2)/(4*W^2))) =
      (fun t : ℝ => Real.exp (-(4*W^2)⁻¹*t^2)) := by
    funext t
    congr 1
    ring
  change (∫ t : ℝ, (Real.sqrt Real.pi/W)*Real.exp (-(t^2)/(4*W^2))) = _
  rw [integral_const_mul,he,integral_gaussian,div_inv_eq_mul,Real.sqrt_mul Real.pi_pos.le]
  have hs : Real.sqrt (4*W^2) = 2*W := by
    rw [show 4*W^2 = (2*W)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hs]
  have hsqrt := Real.sq_sqrt Real.pi_pos.le
  field_simp
  nlinarith only [hsqrt]

/-- A uniform original contour mass bound, including J(1). -/
theorem lemma81_actual_finite_gaussian_mass {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {x : ℝ} (hx : |x| ≤ 1) :
    (∫ t in (-(lemma23PaperL D^405))..(lemma23PaperL D^405),
      ‖lemma81Omega D (lemma81SegmentPoint D x t)‖) ≤ 2*Real.pi*Real.exp 1 := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hW1 : 1 ≤ lemma23PaperL D^400 := one_le_pow₀ hL1
  have hden : 0 < 4*(lemma23PaperL D^400)^2 := by positivity
  have hx2 : x^2 ≤ 1 := by nlinarith only [(abs_le.mp hx).1,(abs_le.mp hx).2]
  have hexponent : x^2/(4*(lemma23PaperL D^400)^2) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hx2,hW1]
  have hfun : (fun t => ‖lemma81Omega D (lemma81SegmentPoint D x t)‖) =
      (fun t => Real.exp (x^2/(4*(lemma23PaperL D^400)^2))*lemma81GaussianDensity D t) := by
    funext t
    exact lemma81_omega_norm_density hLp x t
  have hi : Integrable (fun t => ‖lemma81Omega D (lemma81SegmentPoint D x t)‖) := by
    rw [hfun]
    exact (lemma81_gaussian_density_integrable hLp).const_mul _
  rw [intervalIntegral.integral_of_le (neg_le_self (pow_nonneg hLp.le 405))]
  apply (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).trans
  rw [hfun,integral_const_mul,lemma81_gaussian_density_mass hLp]
  apply (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent) (by positivity : 0 ≤ 2*Real.pi)).trans_eq
  ring

end ZhangLS.Spec
