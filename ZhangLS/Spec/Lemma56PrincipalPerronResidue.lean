import ZhangLS.Spec.Lemma44LocalRectangle

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_positive_right_rectangle_inv {a b H : ℝ}
    (ha : a < 0) (hb : 1 ≤ b) (hH : 0 < H) :
    lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w⁻¹) a b H =
      2 * (Real.pi : ℂ) * I := by
  by_cases hh : a ≤ -1 / 2
  · exact lemma44_general_rectangle_inv hh hb hH
  have hbase := lemma44_general_rectangle_inv (a := (-1 / 2 : ℝ)) (by rfl) hb hH
  have hHalf : (-1 / 2 : ℝ) ≤ a := (lt_of_not_ge hh).le
  have hc := lemma44_local_rectangle_cauchy (fun w : ℂ => w⁻¹) hHalf hH.le
    (by
      intro w hw
      have hwre : w.re ≤ a := hw.1.2
      have hne : w ≠ 0 := by
        intro he
        simp only [he, zero_re] at hwre
        linarith only [hwre, ha]
      exact (differentiableAt_id.inv hne).differentiableWithinAt)
  have hbottom : Continuous (fun x : ℝ => ((x : ℂ) - (H : ℂ) * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith only [hi, hH]
  have htop : Continuous (fun x : ℝ => ((x : ℂ) + (H : ℂ) * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith only [hi, hH]
  have hbott := intervalIntegral.integral_add_adjacent_intervals
    (hbottom.intervalIntegrable (μ := volume) (-1 / 2) a) (hbottom.intervalIntegrable a b)
  have htopt := intervalIntegral.integral_add_adjacent_intervals
    (htop.intervalIntegrable (μ := volume) (-1 / 2) a) (htop.intervalIntegrable a b)
  unfold lemma44GeneralRectangleBoundaryIntegral at hbase hc ⊢
  rw [← hbott, ← htopt] at hbase
  linear_combination hbase - hc

theorem lemma56_positive_right_simple_pole_rectangle (N : ℂ → ℂ) {a b T : ℝ}
    (ha : a < 0) (hb : 1 ≤ b) (hT : 0 < T)
    (hN : DifferentiableOn ℂ N (lemma44ClosedRectangle a b T)) :
    lemma44GeneralRectangleBoundaryIntegral (fun w => N w / w) a b T =
      2 * (Real.pi : ℂ) * I * N 0 := by
  let S := lemma44ClosedRectangle a b T
  have hab : a ≤ b := by linarith
  have hn : S ∈ nhds (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    simp only [S, lemma44ClosedRectangle, interior_reProdIm, interior_Icc,
      mem_reProdIm, mem_Ioo, zero_re, zero_im]
    constructor <;> constructor <;> linarith
  let R := dslope N 0
  have hR : DifferentiableOn ℂ R S := (Complex.differentiableOn_dslope hn).2 hN
  have heq (w : ℂ) (hw : w ≠ 0) : N w / w = N 0 * w⁻¹ + R w := by
    dsimp [R]
    rw [dslope_of_ne _ hw, slope_def_field]
    simp only [sub_zero]
    field_simp
    ring
  have hsplit (γ : ℝ → ℂ) (hγ : Continuous γ) (hγne : ∀ t, γ t ≠ 0)
      (u v : ℝ) (hm : MapsTo γ (uIcc u v) S) :
      (∫ t : ℝ in u..v, N (γ t) / γ t) =
        N 0 * (∫ t : ℝ in u..v, (γ t)⁻¹) + (∫ t : ℝ in u..v, R (γ t)) := by
    have hq : IntervalIntegrable (fun t => N 0 * (γ t)⁻¹) volume u v :=
      ((hγ.inv₀ hγne).const_mul (N 0)).intervalIntegrable u v
    have hr : IntervalIntegrable (fun t => R (γ t)) volume u v :=
      (hR.continuousOn.comp hγ.continuousOn hm).intervalIntegrable
    calc
      _ = ∫ t : ℝ in u..v, (N 0 * (γ t)⁻¹ + R (γ t)) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact heq (γ t) (hγne t)
      _ = _ := by rw [intervalIntegral.integral_add hq hr,
        intervalIntegral.integral_const_mul]
  have hbottom := hsplit (fun x => (x : ℂ) - (T : ℂ) * I) (by fun_prop)
    (by intro x hx; have hi := congrArg Complex.im hx; simp at hi; linarith) a b
    (by
      intro x hx
      rw [uIcc_of_le hab] at hx
      change _ ∈ Icc a b ×ℂ Icc (-T) T
      simp only [mem_reProdIm, mem_Icc, sub_re, sub_im, ofReal_re, ofReal_im,
        mul_re, mul_im, I_re, I_im, mul_zero, zero_mul, mul_one, zero_add, sub_zero]
      exact ⟨hx, by constructor <;> linarith⟩)
  have htop := hsplit (fun x => (x : ℂ) + (T : ℂ) * I) (by fun_prop)
    (by intro x hx; have hi := congrArg Complex.im hx; simp at hi; linarith) a b
    (by
      intro x hx
      rw [uIcc_of_le hab] at hx
      change _ ∈ Icc a b ×ℂ Icc (-T) T
      simpa [mem_reProdIm] using And.intro hx (show -T ≤ T ∧ T ≤ T by constructor <;> linarith))
  have hright := hsplit (fun y => (b : ℂ) + (y : ℂ) * I) (by fun_prop)
    (by intro y hy; have hr := congrArg Complex.re hy; simp at hr; linarith) (-T) T
    (by
      intro y hy
      rw [uIcc_of_le (by linarith : -T ≤ T)] at hy
      change _ ∈ Icc a b ×ℂ Icc (-T) T
      simpa [mem_reProdIm] using And.intro (show a ≤ b ∧ b ≤ b by constructor; exact hab; rfl) hy)
  have hleft := hsplit (fun y => (a : ℂ) + (y : ℂ) * I) (by fun_prop)
    (by intro y hy; have hr := congrArg Complex.re hy; simp at hr; linarith) (-T) T
    (by
      intro y hy
      rw [uIcc_of_le (by linarith : -T ≤ T)] at hy
      change _ ∈ Icc a b ×ℂ Icc (-T) T
      simpa [mem_reProdIm] using And.intro (show a ≤ a ∧ a ≤ b by constructor; rfl; exact hab) hy)
  calc
    _ = N 0 * lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w⁻¹) a b T +
        lemma44GeneralRectangleBoundaryIntegral R a b T := by
      unfold lemma44GeneralRectangleBoundaryIntegral
      rw [hbottom, htop, hright, hleft]
      ring
    _ = _ := by
      rw [lemma56_positive_right_rectangle_inv ha hb hT,
        lemma44_local_rectangle_cauchy R hab hT.le hR]
      ring

end ZhangLS.Spec
