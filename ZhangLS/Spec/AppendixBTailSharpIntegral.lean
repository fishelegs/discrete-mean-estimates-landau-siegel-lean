import ZhangLS.Spec.AppendixBTailBoundaryMass

/-! Exact strict-step integral underlying the source's Gaussian unsmoothing.
The lower endpoint belongs to the complementary tail. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical

lemma appendixB_strict_step_interval (a b u : ℝ) (hab : a≤b) :
    (∫ z : ℝ in a..b, if u<z then (1 : ℝ) else 0)=max (b-max a u) 0 := by
  rw [intervalIntegral.integral_of_le hab]
  have he : (fun z : ℝ => if u<z then (1 : ℝ) else 0)=
      (Ioi u).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext z
    simp [Set.indicator,Set.mem_Ioi]
  rw [he,MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  rw [Set.inter_comm,Ioc_inter_Ioi,MeasureTheory.setIntegral_const,Real.volume_real_Ioc]
  simp

lemma appendixB_strict_step_intervalIntegrable (a b u : ℝ) :
    IntervalIntegrable (fun z : ℝ => if u<z then (1 : ℝ) else 0) volume a b := by
  have he : (fun z : ℝ => if u<z then (1 : ℝ) else 0)=
      (Ioi u).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext z
    simp [Set.indicator,Set.mem_Ioi]
  rw [he]
  have hi : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
  exact ⟨hi.1.indicator measurableSet_Ioi,hi.2.indicator measurableSet_Ioi⟩

/-- Exact source short ramp, with the strict baseline making u=a a tail point. -/
theorem appendixB_strict_step_difference_integral (a b u : ℝ) (hab : a≤b) :
    (∫ z : ℝ in a..b,
      ((if u<z then (1 : ℝ) else 0)-(if u<a then (1 : ℝ) else 0)))=
      if a≤u then max (b-u) 0 else 0 := by
  rw [intervalIntegral.integral_sub (appendixB_strict_step_intervalIntegrable a b u)
    intervalIntegrable_const,appendixB_strict_step_interval a b u hab,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  by_cases hua : u<a
  · have hau : ¬a≤u := not_le.mpr hua
    rw [if_pos hua,if_neg hau,max_eq_left hua.le,
      max_eq_left (sub_nonneg.mpr hab)]
    ring
  · have hau : a≤u := le_of_not_gt hua
    rw [if_neg hua,if_pos hau,max_eq_right hau]
    ring

lemma appendixB_scaled_log_step {L : ℝ} (hL : 0<L) (z u : ℝ) :
    appendixBStrictLogStep (L*(z-u))=if u<z then 1 else 0 := by
  unfold appendixBStrictLogStep
  simp only [mul_pos_iff_of_pos_left hL,sub_pos]

/-- The Gaussian formula is approximating this exact step formula; equality
at the sqrt(P) endpoint is present, with no half-weight convention inserted. -/
theorem appendixB_scaled_step_difference_integral {L : ℝ} (hL : 0<L)
    (a b u : ℝ) (hab : a≤b) :
    (∫ z : ℝ in a..b,
      (appendixBStrictLogStep (L*(z-u))-appendixBStrictLogStep (L*(a-u))))=
      if a≤u then max (b-u) 0 else 0 := by
  simp_rw [appendixB_scaled_log_step hL]
  exact appendixB_strict_step_difference_integral a b u hab

end ZhangLS.Spec
