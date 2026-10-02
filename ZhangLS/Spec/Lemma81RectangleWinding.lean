import ZhangLS.Spec.Lemma56PrincipalPerronResidue

/-! # Winding of an arbitrary axis-aligned rectangle

The orientation is bottom-right-top-left. The reciprocal integral is derived
from the existing verified symmetric rectangle by Cauchy on three exterior
strips, then translated to each genuine interior pole.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000

noncomputable def lemma81RectangleIntegral (f : ℂ → ℂ) (a b lo hi : ℝ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I)) -
  (∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)) +
  I * (∫ y in lo..hi, f ((b : ℂ)+(y : ℂ)*I)) -
  I * (∫ y in lo..hi, f ((a : ℂ)+(y : ℂ)*I))

lemma lemma81_rectangle_cauchy (f : ℂ → ℂ) {a b lo hi : ℝ}
    (hab : a ≤ b) (hlh : lo ≤ hi)
    (hf : DifferentiableOn ℂ f (Icc a b ×ℂ Icc lo hi)) :
    lemma81RectangleIntegral f a b lo hi = 0 := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (⟨a,lo⟩ : ℂ) (⟨b,hi⟩ : ℂ)
    (by simpa only [uIcc_of_le hab,uIcc_of_le hlh] using hf)
  simpa only [smul_eq_mul] using hh

lemma lemma81_horizontal_inverse_continuous {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun x : ℝ => ((x : ℂ)+(t : ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro x hx
  have hh := congrArg Complex.im hx
  simp only [add_im,ofReal_im,mul_im,I_im,I_re,ofReal_re,mul_one,mul_zero,add_zero,zero_add,zero_im] at hh
  exact ht hh

lemma lemma81_vertical_inverse_continuous {x : ℝ} (hx : x ≠ 0) :
    Continuous (fun t : ℝ => ((x : ℂ)+(t : ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t ht
  have hh := congrArg Complex.re ht
  simp only [add_re,ofReal_re,mul_re,I_im,I_re,ofReal_im,mul_zero,mul_one,sub_zero,add_zero,zero_re] at hh
  exact hx hh

lemma lemma81_rectangle_inverse_split_real (a b c lo hi : ℝ) (hlo : lo ≠ 0) (hhi : hi ≠ 0) :
    lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a c lo hi =
      lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b lo hi +
      lemma81RectangleIntegral (fun z : ℂ => z⁻¹) b c lo hi := by
  have hb := intervalIntegral.integral_add_adjacent_intervals
    ((lemma81_horizontal_inverse_continuous hlo).intervalIntegrable (μ := volume) a b)
    ((lemma81_horizontal_inverse_continuous hlo).intervalIntegrable b c)
  have ht := intervalIntegral.integral_add_adjacent_intervals
    ((lemma81_horizontal_inverse_continuous hhi).intervalIntegrable (μ := volume) a b)
    ((lemma81_horizontal_inverse_continuous hhi).intervalIntegrable b c)
  unfold lemma81RectangleIntegral
  rw [← hb,← ht]
  ring

lemma lemma81_rectangle_inverse_split_im (a b lo mid hi : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b lo hi =
      lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b lo mid +
      lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b mid hi := by
  have hl := intervalIntegral.integral_add_adjacent_intervals
    ((lemma81_vertical_inverse_continuous ha).intervalIntegrable (μ := volume) lo mid)
    ((lemma81_vertical_inverse_continuous ha).intervalIntegrable mid hi)
  have hr := intervalIntegral.integral_add_adjacent_intervals
    ((lemma81_vertical_inverse_continuous hb).intervalIntegrable (μ := volume) lo mid)
    ((lemma81_vertical_inverse_continuous hb).intervalIntegrable mid hi)
  unfold lemma81RectangleIntegral
  rw [← hl,← hr]
  ring

lemma lemma81_rectangle_inverse_winding_symmetric {a b T : ℝ}
    (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b (-T) T = 2*(Real.pi : ℂ)*I := by
  let B := max b 1
  have hbase := lemma56_positive_right_rectangle_inv ha (show 1 ≤ B from le_max_right _ _) hT
  have hbase' : lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a B (-T) T = 2*(Real.pi : ℂ)*I := by
    simpa only [lemma81RectangleIntegral,lemma44GeneralRectangleBoundaryIntegral,
      ofReal_neg,neg_mul,← sub_eq_add_neg] using hbase
  have hright : lemma81RectangleIntegral (fun z : ℂ => z⁻¹) b B (-T) T = 0 := by
    apply lemma81_rectangle_cauchy _ (le_max_left _ _) (by linarith)
    intro z hz
    have hne : z ≠ 0 := by
      intro he
      have hh := hz.1.1
      rw [he,zero_re] at hh
      exact (not_le_of_gt hb) hh
    exact (differentiableAt_id.inv hne).differentiableWithinAt
  rw [lemma81_rectangle_inverse_split_real a b B (-T) T (neg_ne_zero.mpr hT.ne') hT.ne',
    hright,add_zero] at hbase'
  exact hbase'

/-- The exact positive winding integral for every rectangle containing 0. -/
theorem lemma81_rectangle_inverse_winding {a b lo hi : ℝ}
    (ha : a < 0) (hb : 0 < b) (hlo : lo < 0) (hhi : 0 < hi) :
    lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b lo hi = 2*(Real.pi : ℂ)*I := by
  let T := max 1 (max (-lo) hi)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT : 0 < T := by linarith only [hT1]
  have hloT : -T ≤ lo := by
    have hh : -lo ≤ T := (le_max_left (-lo) hi).trans (le_max_right 1 _)
    linarith only [hh]
  have hhiT : hi ≤ T := (le_max_right (-lo) hi).trans (le_max_right 1 _)
  have hbase := lemma81_rectangle_inverse_winding_symmetric ha hb hT
  have hbottom : lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b (-T) lo = 0 := by
    apply lemma81_rectangle_cauchy _ (by linarith) hloT
    intro z hz
    have hne : z ≠ 0 := by
      intro he
      have hh := hz.2.2
      rw [he,zero_im] at hh
      exact (not_le_of_gt (neg_pos.mpr hlo)) (by linarith only [hh])
    exact (differentiableAt_id.inv hne).differentiableWithinAt
  have htop : lemma81RectangleIntegral (fun z : ℂ => z⁻¹) a b hi T = 0 := by
    apply lemma81_rectangle_cauchy _ (by linarith) hhiT
    intro z hz
    have hne : z ≠ 0 := by
      intro he
      have hh := hz.2.1
      rw [he,zero_im] at hh
      exact (not_le_of_gt hhi) hh
    exact (differentiableAt_id.inv hne).differentiableWithinAt
  rw [lemma81_rectangle_inverse_split_im a b (-T) lo T ha.ne hb.ne',
    lemma81_rectangle_inverse_split_im a b lo hi T ha.ne hb.ne',
    hbottom,htop,zero_add,add_zero] at hbase
  exact hbase

lemma lemma81_rectangle_reciprocal_translate (ρ : ℂ) (a b lo hi : ℝ) :
    lemma81RectangleIntegral (fun z : ℂ => (z-ρ)⁻¹) a b lo hi =
      lemma81RectangleIntegral (fun z : ℂ => z⁻¹) (a-ρ.re) (b-ρ.re) (lo-ρ.im) (hi-ρ.im) := by
  have hhorizontal (y : ℝ) :
      (∫ x in a..b, ((x : ℂ)+(y : ℂ)*I-ρ)⁻¹) =
        ∫ x in (a-ρ.re)..(b-ρ.re), ((x : ℂ)+((y-ρ.im : ℝ) : ℂ)*I)⁻¹ := by
    have he (x : ℝ) : (x : ℂ)+(y : ℂ)*I-ρ =
        ((x-ρ.re : ℝ) : ℂ)+((y-ρ.im : ℝ) : ℂ)*I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    exact intervalIntegral.integral_comp_sub_right (a := a) (b := b)
      (fun x : ℝ => ((x : ℂ)+((y-ρ.im : ℝ) : ℂ)*I)⁻¹) ρ.re
  have hvertical (x : ℝ) :
      (∫ y in lo..hi, ((x : ℂ)+(y : ℂ)*I-ρ)⁻¹) =
        ∫ y in (lo-ρ.im)..(hi-ρ.im), (((x-ρ.re : ℝ) : ℂ)+(y : ℂ)*I)⁻¹ := by
    have he (y : ℝ) : (x : ℂ)+(y : ℂ)*I-ρ =
        ((x-ρ.re : ℝ) : ℂ)+((y-ρ.im : ℝ) : ℂ)*I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    exact intervalIntegral.integral_comp_sub_right (a := lo) (b := hi)
      (fun y : ℝ => (((x-ρ.re : ℝ) : ℂ)+(y : ℂ)*I)⁻¹) ρ.im
  unfold lemma81RectangleIntegral
  rw [hhorizontal lo,hhorizontal hi,hvertical b,hvertical a]

/-- Every genuine interior pole contributes the same +2πi winding factor. -/
theorem lemma81_rectangle_simple_pole_winding {a b lo hi : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ Ioo a b ×ℂ Ioo lo hi) :
    lemma81RectangleIntegral (fun z : ℂ => (z-ρ)⁻¹) a b lo hi = 2*(Real.pi : ℂ)*I := by
  rw [lemma81_rectangle_reciprocal_translate]
  exact lemma81_rectangle_inverse_winding (sub_neg.mpr hρ.1.1) (sub_pos.mpr hρ.1.2)
    (sub_neg.mpr hρ.2.1) (sub_pos.mpr hρ.2.2)

end ZhangLS.Spec
