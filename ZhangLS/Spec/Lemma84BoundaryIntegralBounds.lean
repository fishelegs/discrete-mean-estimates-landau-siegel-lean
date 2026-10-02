import ZhangLS.Spec.Lemma84NearContourBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
set_option maxHeartbeats 1500000

/-- Integrating the Cauchy denominator avoids a spurious factor D in the
left contour. The bound is independent of the segment height. -/
lemma lemma84_left_vertical_integral_bound (f : ℝ → ℂ) {δ H M : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hM : 0 ≤ M) (u v : ℝ)
    (hf : ∀ t ∈ Ioc (-H) H, ‖f t‖ ≤ M*‖lemma84LogKernel (-δ) u v t‖) :
    ‖∫ t : ℝ in -H..H, f t‖ ≤ M*Real.exp (-δ*u)*Real.pi/δ := by
  let g : ℝ → ℝ := fun t => M*Real.exp (-δ*u)*(δ^2+(t+v)^2)⁻¹
  have hgi : Integrable g :=
    ((lemma84_inverse_quadratic_integrable hδ).comp_add_right v).const_mul _
  have hgle (t : ℝ) (ht : t ∈ Ioc (-H) H) : ‖f t‖ ≤ g t := by
    have hh := hf t ht
    simp only [lemma84_log_kernel_norm,neg_mul,show (-δ)^2=δ^2 by ring] at hh
    simpa only [g,mul_assoc,neg_mul] using hh
  have hh := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -H ≤ H)
    (Filter.Eventually.of_forall hgle) hgi.intervalIntegrable
  apply hh.trans
  rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
  have hsub : (∫ t : ℝ in Ioc (-H) H, g t) ≤ ∫ t : ℝ, g t := by
    conv_rhs => rw [← setIntegral_univ]
    apply setIntegral_mono_set hgi.integrableOn
    · filter_upwards [] with t
      dsimp [g]
      positivity
    · exact Filter.Eventually.of_forall (fun t _ => mem_univ t)
  apply hsub.trans_eq
  dsimp [g]
  rw [integral_const_mul,integral_add_right_eq_self (fun t : ℝ => (δ^2+t^2)⁻¹) v,
    lemma84_inverse_quadratic_integral hδ]
  ring

lemma lemma84_horizontal_kernel_bound (s m : ℂ) {H u b B : ℝ}
    (hH : 0 < H) (hu : 0 ≤ u) (him : |s.im| = H) (hm : ‖m‖ ≤ H/2)
    (hre : s.re ≤ b) (hscale : b*u ≤ B) :
    ‖exp (s*(u:ℂ))/(s+m)^2‖ ≤ 4*Real.exp B/H^2 := by
  have hnorm : H/2 ≤ ‖s+m‖ := by
    have hh : |s.im| ≤ |(s+m).im|+|m.im| := by
      have hh := abs_add_le (s.im+m.im) (-m.im)
      simpa only [Complex.add_im,add_neg_cancel_right,abs_neg] using hh
    have hm' := (Complex.abs_im_le_norm m).trans hm
    have hs' := Complex.abs_im_le_norm (s+m)
    rw [him] at hh
    linarith only [hh,hm',hs']
  have hsq : H^2/4 ≤ ‖s+m‖^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ H/2) hnorm 2
    nlinarith only [hh]
  have he : ‖exp (s*(u:ℂ))‖ ≤ Real.exp B := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact (mul_le_mul_of_nonneg_right hre hu).trans hscale
  rw [norm_div,norm_pow]
  have hh := div_le_div₀ (Real.exp_pos B).le he (by positivity : 0 < H^2/4) hsq
  exact hh.trans_eq (by ring)

/-- Two horizontal connector bounds, with no conductor-height loss. -/
lemma lemma84_horizontal_integrals_bound (f : ℂ → ℂ) {a b H M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hl : ∀ x ∈ Icc a b, ‖f ((x:ℂ)-I*(H:ℂ))‖ ≤ M)
    (hu : ∀ x ∈ Icc a b, ‖f ((x:ℂ)+I*(H:ℂ))‖ ≤ M) :
    ‖∫ x : ℝ in a..b, f ((x:ℂ)-I*(H:ℂ))‖ +
      ‖∫ x : ℝ in a..b, f ((x:ℂ)+I*(H:ℂ))‖ ≤ 2*M*(b-a) := by
  have hh (g : ℝ → ℂ) (hg : ∀ x ∈ Icc a b, ‖g x‖ ≤ M) :
      ‖∫ x : ℝ in a..b, g x‖ ≤ M*(b-a) := by
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (f := g) (C := M) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      exact hg x ⟨hx.1.le,hx.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hbnd
  have h := add_le_add (hh _ hl) (hh _ hu)
  exact h.trans_eq (by ring)

end ZhangLS.Spec
