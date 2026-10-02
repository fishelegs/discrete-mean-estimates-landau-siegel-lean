import ZhangLS.Spec.Proposition71MellinPrimeBound

/-! # Complete Mellin-height tails for the Section 7 small-conductor estimate

The 1/(1+t²) tails are proved rather than extending Lemma5.6 beyond its
original closed |τ|≤D height window.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma proposition71_arctan_le_self {x : ℝ} (hx : 0≤x) : Real.arctan x≤x := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y (_ : y∈uIcc (0:ℝ) x) => (Real.hasDerivAt_arctan' y).hasDerivWithinAt)
    (fun y (_ : y∈uIcc (0:ℝ) x) => (show ‖(1+y^2)⁻¹‖≤(1:ℝ) by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg y])))
    (convex_uIcc (0:ℝ) x) left_mem_uIcc right_mem_uIcc
  simpa only [Real.arctan_zero,sub_zero,Real.norm_eq_abs,
    abs_of_nonneg (Real.arctan_nonneg.mpr hx),abs_of_nonneg hx,one_mul] using hb

lemma proposition71_positive_cauchy_tail {H : ℝ} (hH : 0<H) :
    (∫ t : ℝ in Ioi H, (1+t^2)⁻¹)≤H⁻¹ := by
  rw [integral_Ioi_inv_one_add_sq,←Real.arctan_inv_of_pos hH]
  exact proposition71_arctan_le_self (inv_nonneg.mpr hH.le)

lemma proposition71_negative_cauchy_tail {H : ℝ} (hH : 0<H) :
    (∫ t : ℝ in Iic (-H), (1+t^2)⁻¹)≤H⁻¹ := by
  rw [integral_Iic_inv_one_add_sq,Real.arctan_neg]
  have h := proposition71_positive_cauchy_tail hH
  rw [integral_Ioi_inv_one_add_sq] at h
  linarith

/-- A bounded continuous function has an absolutely integrable Cauchy-weighted norm. -/
lemma proposition71_bounded_cauchy_integrable (f : ℝ → ℂ) (hf : Continuous f)
    {B : ℝ} (_hB : 0≤B) (hbound : ∀t, ‖f t‖≤B) :
    Integrable (fun t : ℝ => ‖f t‖/(1+t^2)) := by
  apply (integrable_inv_one_add_sq.const_mul B).mono'
    (hf.norm.div (by fun_prop) (fun t => by positivity)).aestronglyMeasurable
  apply ae_of_all
  intro t
  change ‖‖f t‖/(1+t^2)‖≤B*(1+t^2)⁻¹
  rw [Real.norm_eq_abs,abs_of_nonneg
    (div_nonneg (norm_nonneg (f t)) (by positivity : 0≤1+t^2))]
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
    (hbound t) (by positivity : 0≤(1+t^2)⁻¹)

/-- The central height window and both tails are controlled separately.
The hypotheses are genuine pointwise bounds, not an averaged target. -/
theorem proposition71_cauchy_window_and_tail (f : ℝ → ℂ) (hf : Continuous f)
    {B C H : ℝ} (hB : 0≤B) (hC : 0≤C) (hH : 0<H)
    (hglobal : ∀t, ‖f t‖≤B) (hwindow : ∀t, |t|≤H → ‖f t‖≤C) :
    (∫ t : ℝ, ‖f t‖/(1+t^2))≤C*Real.pi+2*B/H := by
  let w : ℝ → ℝ := fun t => (1+t^2)⁻¹
  let v : ℝ → ℝ := fun t =>
    C*w t+B*((Iic (-H)).indicator w t+(Ioi H).indicator w t)
  have hw : Integrable w := integrable_inv_one_add_sq
  have hwl := hw.indicator (s := Iic (-H)) measurableSet_Iic
  have hwr := hw.indicator (s := Ioi H) measurableSet_Ioi
  have hv : Integrable v := (hw.const_mul C).add ((hwl.add hwr).const_mul B)
  have hu := proposition71_bounded_cauchy_integrable f hf hB hglobal
  have hpoint (t : ℝ) : ‖f t‖/(1+t^2)≤v t := by
    have hw0 : 0≤w t := by dsimp [w]; positivity
    have hgl := mul_le_mul_of_nonneg_right (hglobal t) hw0
    by_cases hleft : t≤-H
    · have hright : ¬H<t := by linarith
      dsimp [v]
      simp only [Set.indicator_apply,mem_Iic,mem_Ioi,if_pos hleft,if_neg hright,add_zero]
      rw [div_eq_mul_inv]
      change ‖f t‖*w t≤C*w t+B*w t
      nlinarith [mul_nonneg hC hw0]
    · by_cases hright : H<t
      · dsimp [v]
        simp only [Set.indicator_apply,mem_Iic,mem_Ioi,if_neg hleft,if_pos hright,zero_add]
        rw [div_eq_mul_inv]
        change ‖f t‖*w t≤C*w t+B*w t
        nlinarith [mul_nonneg hC hw0]
      · have ht : |t|≤H := abs_le.mpr ⟨by linarith,by linarith⟩
        have hwin := mul_le_mul_of_nonneg_right (hwindow t ht) hw0
        dsimp [v]
        simp only [Set.indicator_apply,mem_Iic,mem_Ioi,if_neg hleft,if_neg hright,
          add_zero,mul_zero]
        exact hwin
  have hi := integral_mono_ae hu hv (ae_of_all _ hpoint)
  have hiv : (∫t : ℝ, v t)=C*Real.pi+B*((∫t : ℝ in Iic (-H), w t)+(∫t : ℝ in Ioi H, w t)) := by
    have hadd := integral_add (hw.const_mul C) ((hwl.add hwr).const_mul B)
    simp only [Pi.add_apply] at hadd
    dsimp only [v]
    rw [hadd,integral_const_mul,integral_const_mul]
    have hadd' := integral_add hwl hwr
    simp only [Pi.add_apply] at hadd'
    rw [hadd',
      integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioi]
    rw [show (∫t : ℝ, w t)=Real.pi from integral_univ_inv_one_add_sq]
  rw [hiv] at hi
  have hl := proposition71_negative_cauchy_tail hH
  have hr := proposition71_positive_cauchy_tail hH
  have hh := mul_le_mul_of_nonneg_left (add_le_add hl hr) hB
  dsimp [w] at hi
  apply hi.trans
  simp only [div_eq_mul_inv]
  nlinarith only [hh]

end ZhangLS.Spec
