import ZhangLS.Spec.Lemma45HorizontalQuotient

/-! # Horizontal norm transport through the actual logarithmic derivative

Only local differentiability and nonvanishing on the closed segment are used.
The result does not assume a global logarithm on a region containing zeros.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
set_option maxHeartbeats 2000000

lemma proposition71_horizontal_log_norm_difference {f : ℂ → ℂ} {a b t K : ℝ}
    (hab : a≤b)
    (hf : ∀x∈Icc a b, DifferentiableAt ℂ f ((x : ℂ)+I*(t : ℂ)))
    (hne : ∀x∈Icc a b, f ((x : ℂ)+I*(t : ℂ))≠0)
    (hb : ∀x∈Icc a b, ‖logDeriv f ((x : ℂ)+I*(t : ℂ))‖≤K) :
    |Real.log ‖f ((a : ℂ)+I*(t : ℂ))‖-Real.log ‖f ((b : ℂ)+I*(t : ℂ))‖|≤K*(b-a) := by
  let H : ℝ → ℝ := fun x => Real.log ‖f ((x : ℂ)+I*(t : ℂ))‖
  have hd (x : ℝ) (hx : x∈Icc a b) :
      HasDerivAt H (logDeriv f ((x : ℂ)+I*(t : ℂ))).re x :=
    lemma45_hasDerivAt_horizontal_log_norm (hf x hx) (hne x hx)
  have hn (x : ℝ) (hx : x∈Icc a b) : ‖(logDeriv f ((x : ℂ)+I*(t : ℂ))).re‖≤K := by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hb x hx)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hn (convex_Icc a b)
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩)
  have he : ‖b-a‖=b-a := by rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)]
  rw [he,Real.norm_eq_abs] at hh
  exact (abs_sub_comm _ _).le.trans hh

lemma proposition71_horizontal_norm_ratio_bound {f : ℂ → ℂ} {a b t K : ℝ}
    (hab : a≤b)
    (hf : ∀x∈Icc a b, DifferentiableAt ℂ f ((x : ℂ)+I*(t : ℂ)))
    (hne : ∀x∈Icc a b, f ((x : ℂ)+I*(t : ℂ))≠0)
    (hb : ∀x∈Icc a b, ‖logDeriv f ((x : ℂ)+I*(t : ℂ))‖≤K) :
    ‖f ((a : ℂ)+I*(t : ℂ))/f ((b : ℂ)+I*(t : ℂ))‖≤Real.exp (K*(b-a)) ∧
      ‖f ((b : ℂ)+I*(t : ℂ))/f ((a : ℂ)+I*(t : ℂ))‖≤Real.exp (K*(b-a)) := by
  have ha := hne a ⟨le_rfl,hab⟩
  have hb' := hne b ⟨hab,le_rfl⟩
  have hh := proposition71_horizontal_log_norm_difference hab hf hne hb
  have hpa : 0<‖f ((a : ℂ)+I*(t : ℂ))‖ := norm_pos_iff.mpr ha
  have hpb : 0<‖f ((b : ℂ)+I*(t : ℂ))‖ := norm_pos_iff.mpr hb'
  constructor
  · rw [norm_div,←Real.exp_log (div_pos hpa hpb)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hpa.ne' hpb.ne']
    exact (le_abs_self _).trans hh
  · rw [norm_div,←Real.exp_log (div_pos hpb hpa)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hpb.ne' hpa.ne']
    exact (le_abs_self _).trans ((abs_sub_comm _ _).le.trans hh)

end ZhangLS.Spec
