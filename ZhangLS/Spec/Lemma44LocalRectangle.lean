import ZhangLS.Spec.Lemma44FiniteProductShift

/-!
# Local finite rectangles for the reflected polynomials

The Gamma quotient need only be analytic on the finite high rectangle.
Removing its simple pole with `dslope` proves the residue locally.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma44GeneralRectangleBoundaryIntegral
    (f : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) - (T : ℂ) * I)) -
    (∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * I)) +
      I * (∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * I))

def lemma44ClosedRectangle (a b T : ℝ) : Set ℂ := Icc a b ×ℂ Icc (-T) T

theorem lemma44_local_rectangle_cauchy (f : ℂ → ℂ) {a b T : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hf : DifferentiableOn ℂ f (lemma44ClosedRectangle a b T)) :
    lemma44GeneralRectangleBoundaryIntegral f a b T = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I)
  have hs : (uIcc (((a : ℂ) - (T : ℂ) * I).re) (((b : ℂ) + (T : ℂ) * I).re) ×ℂ
      uIcc (((a : ℂ) - (T : ℂ) * I).im) (((b : ℂ) + (T : ℂ) * I).im)) =
      lemma44ClosedRectangle a b T := by
    simp [lemma44ClosedRectangle, uIcc_of_le hab, uIcc_of_le (by linarith : -T ≤ T)]
  rw [hs] at h
  simpa [lemma44GeneralRectangleBoundaryIntegral, smul_eq_mul, sub_eq_add_neg] using h hf

theorem lemma44_general_rectangle_inv {a b T : ℝ}
    (ha : a ≤ -1 / 2) (hb : 1 ≤ b) (hT : 0 < T) :
    lemma44GeneralRectangleBoundaryIntegral (fun w : ℂ => w⁻¹) a b T =
      2 * (Real.pi : ℂ) * I := by
  have hleft := lemma44_simple_pole_rectangle_left (fun _ : ℂ => (1 : ℂ))
    (differentiable_const (1 : ℂ)) ha hT
  simp only [one_div, mul_one] at hleft
  have hc := lemma44_local_rectangle_cauchy (fun w : ℂ => w⁻¹) hb hT.le
    (by
      intro w hw
      have hwre : 1 ≤ w.re := hw.1.1
      have hne : w ≠ 0 := by intro he; norm_num [he] at hwre
      exact (differentiableAt_id.inv hne).differentiableWithinAt)
  have hbottom : Continuous (fun x : ℝ => ((x : ℂ) - (T : ℂ) * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have htop : Continuous (fun x : ℝ => ((x : ℂ) + (T : ℂ) * I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hbott := intervalIntegral.integral_add_adjacent_intervals
    (hbottom.intervalIntegrable (μ := volume) a 1) (hbottom.intervalIntegrable 1 b)
  have htopt := intervalIntegral.integral_add_adjacent_intervals
    (htop.intervalIntegrable (μ := volume) a 1) (htop.intervalIntegrable 1 b)
  unfold lemma44GeneralRectangleBoundaryIntegral at hc ⊢
  unfold lemma44RectangleBoundaryIntegral at hleft
  simp only [ofReal_one] at hc hbott htopt
  rw [← hbott, ← htopt]
  linear_combination hleft + hc

theorem lemma44_local_simple_pole_rectangle (N : ℂ → ℂ) {a b T : ℝ}
    (ha : a ≤ -1 / 2) (hb : 1 ≤ b) (hT : 0 < T)
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
      rw [lemma44_general_rectangle_inv ha hb hT,
        lemma44_local_rectangle_cauchy R hab hT.le hR]
      ring

end ZhangLS.Spec
