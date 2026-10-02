import ZhangLS.Spec.Lemma112ReciprocalSeries
/-! # Actual reciprocal-tail contour at the correct product conductor -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_reciprocal_tail_rectangle_differentiable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) (z : ℝ) :
    DifferentiableOn ℂ (lemma112ActualReciprocalTailIntegrand χ ψ s z)
      (lemma44ClosedRectangle (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hψinv : lemma44CharacterTwist χ ψ⁻¹ ≠ 1 := by
    rw [← lemma44CharacterTwist_inv]
    exact inv_ne_one.mpr (lemma112_twist_family_data χ ψ hL hψ).2.2.2
  have hLi := DirichletCharacter.differentiable_LFunction hψinv
  have hN := lemma112_short_polynomial_differentiable χ ψ⁻¹
  let G : ℂ → ℂ := fun w => lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) *
      (DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ⁻¹) (1 - s - w) -
        lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w)) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) * lemma57OmegaOne D w / w
  have hG : DifferentiableOn ℂ G
      (lemma44ClosedRectangle (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20)) := by
    intro w hw
    change w.re ∈ Icc (-(lemma23PaperL D ^ 9)) (-1) ∧
      w.im ∈ Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) at hw
    have hd := lemma61_large_shift_rectangle_bounds hL (lemma112_region_subset_lemma61 hL hs)
      ⟨hw.1.1, by linarith only [hw.1.2]⟩ (abs_le.mpr hw.2)
    have hzi : 0 < (s + w).im := by linarith only [(lemma61_wide_height_data hL hd.2.1).2.1]
    have hz : DifferentiableAt ℂ (fun u : ℂ => lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + u)) w :=
      (lemma23DirichletZ_differentiableAt_of_im_ne_zero _ hzi.ne').comp w (by fun_prop)
    have hn : w ≠ 0 := by intro he; rw [he] at hw; norm_num at hw
    have hGat : DifferentiableAt ℂ G w := by
      dsimp [G]
      apply DifferentiableAt.div _ differentiableAt_id hn
      unfold lemma57OmegaOne
      fun_prop
    exact hGat.differentiableWithinAt
  apply hG.congr
  intro w hw
  change w.re ∈ Icc (-(lemma23PaperL D ^ 9)) (-1) ∧
    w.im ∈ Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) at hw
  have hz : 1 < (1 - s - w).re := by simp only [sub_re, one_re, hs.1]; linarith only [hw.1.2]
  have ht := lemma112_actual_reciprocal_series_split χ ψ⁻¹ hz
  have he : (∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n) =
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ⁻¹) (1 - s - w) -
        lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w) := by
    rw [ht]
    ring
  dsimp [G, lemma112ActualReciprocalTailIntegrand]
  rw [he]

lemma lemma112_reciprocal_tail_rectangle_cauchy {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) (z : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral (lemma112ActualReciprocalTailIntegrand χ ψ s z)
      (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20) = 0 := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  exact lemma44_local_rectangle_cauchy _ (by linarith only [h9]) (by positivity)
    (lemma112_reciprocal_tail_rectangle_differentiable χ ψ hψ hL hs z)

lemma lemma112_reciprocal_tail_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s w : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ -1)
    (hwim : |w.im| ≤ lemma23PaperL D ^ 20) {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖lemma112ActualReciprocalTailIntegrand χ ψ s z w‖ ≤
      lemma61QuarterSeriesMass * Real.exp (2 + lemma23PaperL D ^ 9) *
        Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 :=
    ⟨hwre.1, by linarith only [hwre.2]⟩
  have hZ := lemma112_twist_Z_scale_cancellation χ ψ hψ hD (by linarith) hs hwide hwim z
  have hO := lemma61_large_shift_gaussian_bound (by linarith : 3 ≤ lemma23PaperL D) hwide
  have hden := lemma61_large_shift_denominator_bound hwre.2
  have htail := lemma112_reciprocal_horizontal_sum_bound χ ψ⁻¹ hD hL hs.1 hwre.2 hz
  unfold lemma112ActualReciprocalTailIntegrand
  calc
    _ = ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) *
        exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ *
        ‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
        ‖lemma57OmegaOne D w‖ * ‖w‖⁻¹ := by
      simp only [div_eq_mul_inv, norm_mul, norm_inv]
      ring
    _ ≤ (Real.exp 1 * Real.exp (-w.re * Real.log (lemma112DualScale D z))) *
        ‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
        (Real.exp 1 * Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30))) * 1 := by
      gcongr
    _ = Real.exp 2 * (‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
        Real.exp (-w.re * Real.log (lemma112DualScale D z))) *
          Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      ring
    _ ≤ Real.exp 2 * (lemma61QuarterSeriesMass * Real.exp (lemma23PaperL D ^ 9)) *
        Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

lemma lemma112_reciprocal_far_left_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s w : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (hwre : w.re = -(lemma23PaperL D ^ 9))
    (hwim : |w.im| ≤ lemma23PaperL D ^ 20) {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖lemma112ActualReciprocalTailIntegrand χ ψ s z w‖ ≤
      lemma44InverseSquareMass * Real.exp (2 - lemma23PaperL D ^ 10 / 2) *
        Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := by rw [hwre]; constructor <;> linarith only [h9]
  have hZ := lemma112_twist_Z_scale_cancellation χ ψ hψ hD (by linarith) hs hwide hwim z
  have hO := lemma61_large_shift_gaussian_bound (by linarith : 3 ≤ lemma23PaperL D) hwide
  have hden := lemma61_large_shift_denominator_bound (show w.re ≤ -1 by rw [hwre]; linarith only [h9])
  have htail := lemma112_reciprocal_far_left_sum_bound χ ψ⁻¹ hD hL hs.1 hwre hz
  unfold lemma112ActualReciprocalTailIntegrand
  calc
    _ = ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) *
        exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ *
        ‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
        ‖lemma57OmegaOne D w‖ * ‖w‖⁻¹ := by
      simp only [div_eq_mul_inv, norm_mul, norm_inv]
      ring
    _ ≤ (Real.exp 1 * Real.exp (-w.re * Real.log (lemma112DualScale D z))) *
        ‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
        (Real.exp 1 * Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30))) * 1 := by
      gcongr
    _ = Real.exp 2 * (‖∑' n : ℕ, lemma112ReciprocalTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
        Real.exp (-w.re * Real.log (lemma112DualScale D z))) *
          Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      ring
    _ ≤ Real.exp 2 * (lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10) / 2)) *
        Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
      gcongr
    _ = _ := by rw [show 2 - lemma23PaperL D ^ 10 / 2 = 2 + -(lemma23PaperL D ^ 10) / 2 by ring, Real.exp_add]; ring

end ZhangLS.Spec
