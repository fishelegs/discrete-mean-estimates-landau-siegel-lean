import ZhangLS.Spec.Lemma171ContourGrowth
import ZhangLS.Spec.Lemma171LeftMajorant

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable def lemma171LeftEnvelope (D : ℕ) (t : ℝ) : ℝ :=
  lemma171StripConstant D *
    Real.exp (-(lemma23PaperL D^(11/10:ℝ))/4+1/(64*lemma23PaperL D^30))*
    (1+16*lemma23PaperL D^30)^2 *
    Real.exp (-(1/(8*lemma23PaperL D^30))*t^2)

lemma lemma171_left_envelope_integrable {D : ℕ} (hD : 1 < D) :
    Integrable (lemma171LeftEnvelope D) := by
  have hL : 0 < lemma23PaperL D := Real.log_pos (by exact_mod_cast hD)
  exact (integrable_exp_neg_mul_sq (by positivity : 0 < (1:ℝ)/(8*lemma23PaperL D^30))).const_mul _

lemma lemma171_left_integrand_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (t : ℝ) :
    ‖lemma171MellinIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)*I‖ ≤
      lemma171LeftEnvelope D t := by
  let L := lemma23PaperL D
  let w : ℂ := ((-1/4 : ℝ) : ℂ)+(t : ℂ)*I
  let b : ℝ := 1/(16*L^30)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hD)
  have hb : 0 < b := by dsimp [b];positivity
  have hnorm : 1/4 ≤ ‖w‖ := by
    have hh := Complex.abs_re_le_norm w
    norm_num [w] at hh ⊢
    exact hh
  have hp := lemma171_undamped_strip_bound χ hD w
    (by norm_num [w]) (by norm_num [w]) hnorm
  have him : w.im = t := by simp [w]
  rw [him] at hp
  have hc : 0 ≤ lemma171StripConstant D := (lemma171_strip_constant_pos (by omega)).le
  have he : L^(11/10:ℝ)*(-1/4)+(((-1/4:ℝ)^2)-t^2)/(4*L^30) =
      (-L^(11/10:ℝ)/4+1/(64*L^30))+(-(4*b)*t^2) := by
    dsimp [b]
    field_simp
    ring
  have hinv : b⁻¹ = 16*L^30 := by simp [b]
  have htwo : 2*b = 1/(8*L^30) := by dsimp [b];ring
  rw [norm_mul,Complex.norm_I,mul_one,lemma171_mellin_eq_undamped D χ]
  rw [norm_mul,lemma171_gaussian_norm_vertical]
  change ‖lemma171UndampedFactor χ w‖ * Real.exp (L^(11/10:ℝ)*(-1/4)+
    (((-1/4:ℝ)^2)-t^2)/(4*L^30)) ≤ _
  rw [he,Real.exp_add]
  calc
    _ ≤ (lemma171StripConstant D*(1+t^2)^2)*
        (Real.exp (-L^(11/10:ℝ)/4+1/(64*L^30))*Real.exp (-(4*b)*t^2)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (lemma171StripConstant D*Real.exp (-L^(11/10:ℝ)/4+1/(64*L^30)))*
        ((1+t^2)^2*Real.exp (-(4*b)*t^2)) := by ring
    _ ≤ (lemma171StripConstant D*Real.exp (-L^(11/10:ℝ)/4+1/(64*L^30)))*
        ((1+b⁻¹)^2*Real.exp (-(2*b)*t^2)) :=
      mul_le_mul_of_nonneg_left (lemma171_quartic_gaussian_bound hb t) (by positivity)
    _ = _ := by rw [hinv,htwo];dsimp [lemma171LeftEnvelope,L];ring

lemma lemma171_left_integrand_continuous {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Continuous (fun t : ℝ =>
      lemma171MellinIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)*I) := by
  let z : ℝ → ℂ := fun t => ((-1/4 : ℝ) : ℂ)+(t : ℂ)*I
  have hz : Continuous z := by dsimp [z];fun_prop
  have hzne (t : ℝ) : z t ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [z] at hh
  have hhalf (t : ℝ) : -1/2 < (z t).re := by norm_num [z]
  have hc : Continuous (fun t => lemma171RegularNumerator χ (z t)) := by
    apply (lemma171_regular_numerator_analyticOnNhd χ hD).continuousOn.comp_continuous hz
    exact hhalf
  have he (t : ℝ) : lemma171MellinIntegrand χ (z t) =
      lemma171RegularNumerator χ (z t)/(z t)^3 := by
    rw [lemma171_regular_numerator_eq χ (z t) (hhalf t) (hzne t)]
    field_simp [hzne t]
  change Continuous (fun t => lemma171MellinIntegrand χ (z t)*I)
  simp_rw [he]
  exact (hc.div₀ (hz.pow 3) (fun t => pow_ne_zero 3 (hzne t))).mul continuous_const

lemma lemma171_left_integrand_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Integrable (fun t : ℝ =>
      lemma171MellinIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)*I) := by
  apply (lemma171_left_envelope_integrable hD).mono'
    (lemma171_left_integrand_continuous χ hD).aestronglyMeasurable
  exact Eventually.of_forall (lemma171_left_integrand_bound χ hD)

lemma lemma171_left_vertical_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Integrable (fun t : ℝ =>
      lemma171MellinIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)) := by
  have h := (lemma171_left_integrand_integrable χ hD).mul_const (-I)
  simpa only [mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, mul_one] using h

lemma lemma171_left_vertical_norm_le_majorant {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    ‖lemma171VerticalIntegral χ (-1/4)‖ ≤ lemma171LeftMajorant D := by
  have hL : 0 < lemma23PaperL D := Real.log_pos (by exact_mod_cast hD)
  have hn : ‖(2*(Real.pi:ℂ)*I)⁻¹‖ = (2*Real.pi)⁻¹ := by
    simp [norm_inv,Real.pi_pos.le]
  have hbound : ‖∫ t : ℝ,
      lemma171MellinIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)*I‖ ≤
      ∫ t : ℝ, lemma171LeftEnvelope D t := by
    exact norm_integral_le_of_norm_le (lemma171_left_envelope_integrable hD)
      (Eventually.of_forall (lemma171_left_integrand_bound χ hD))
  unfold lemma171VerticalIntegral
  rw [norm_mul,hn]
  calc
    _ ≤ (2*Real.pi)⁻¹*(∫ t : ℝ, lemma171LeftEnvelope D t) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = lemma171LeftMajorant D := by
      unfold lemma171LeftEnvelope lemma171LeftMajorant lemma171StripConstant
      rw [integral_const_mul,integral_gaussian]
      have he : Real.pi/(1/(8*lemma23PaperL D^30)) = 8*Real.pi*lemma23PaperL D^30 := by simp only [div_eq_mul_inv,one_mul,inv_inv];ring
      rw [he]
      ring

end ZhangLS.Spec
