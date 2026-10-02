import ZhangLS.Spec.Lemma61ReciprocalFarLeft

/-! # Actual reciprocal tail truncation for Lemma 6.1

The original n<T^3 finite sum and its n>=T^3 tail are split exactly.
Actual Gamma conductor growth cancels with actual P4, uniformly on the
wide high rectangle. Far-left and both horizontal tail integrals, the
actual local Cauchy relation and the original-left tail error are proved.
The full Lemma61Target remains unproved: finite polynomial error-line
shift, full horizontal edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_actual_reciprocal_tail_rectangle_differentiable {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    DifferentiableOn ℂ (lemma61ActualReciprocalTailIntegrand (D := D) ψ s)
      (lemma44ClosedRectangle (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20)) := by
  have hψinv : ψ⁻¹ ≠ 1 := inv_ne_one.mpr (lemma61_family_nonprincipal ψ hψ)
  have hLi := DirichletCharacter.differentiable_LFunction hψinv
  have hN := lemma61_short_polynomial_differentiable (D := D) ψ⁻¹
  let G : ℂ → ℂ := fun w => lemma23DirichletZ ψ (s + w) *
      (DirichletCharacter.LFunction ψ⁻¹ (1 - s - w) - lemma61ShortPolynomial D ψ⁻¹ (1 - s - w)) *
        exp (w * (Real.log (lemma61PaperP4 D) : ℂ)) * lemma57OmegaOne D w / w
  have hG : DifferentiableOn ℂ G
      (lemma44ClosedRectangle (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20)) := by
    intro w hw
    change w.re ∈ Icc (-(lemma23PaperL D ^ 9)) (-1) ∧
      w.im ∈ Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) at hw
    have hd := lemma61_large_shift_rectangle_bounds hL hs ⟨hw.1.1,by linarith only [hw.1.2]⟩ (abs_le.mpr hw.2)
    have hh := lemma61_wide_height_data hL hd.2.1
    have hzi : 0 < (s + w).im := by linarith only [hh.2.1]
    have hz : DifferentiableAt ℂ (fun u : ℂ => lemma23DirichletZ ψ (s + u)) w :=
      (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ hzi.ne').comp w (by fun_prop)
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
  have hz : 1 < (1 - s - w).re := by
    simp only [sub_re,one_re]
    linarith only [(lemma61_region_real_parts hL hs).2,hw.1.2]
  have ht := lemma61_actual_reciprocal_series_split (D := D) ψ⁻¹ hz
  have he : (∑' n : ℕ, lemma61ReciprocalTailTerm D ψ⁻¹ (1 - s - w) n) =
      DirichletCharacter.LFunction ψ⁻¹ (1 - s - w) - lemma61ShortPolynomial D ψ⁻¹ (1 - s - w) := by
    rw [ht]
    ring
  dsimp [G,lemma61ActualReciprocalTailIntegrand]
  rw [he]

lemma lemma61_actual_reciprocal_tail_rectangle_cauchy {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s) :
    lemma44GeneralRectangleBoundaryIntegral (lemma61ActualReciprocalTailIntegrand (D := D) ψ s)
      (-(lemma23PaperL D ^ 9)) (-1) (lemma23PaperL D ^ 20) = 0 := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  exact lemma44_local_rectangle_cauchy _ (by linarith only [h9]) (by positivity)
    (lemma61_actual_reciprocal_tail_rectangle_differentiable ψ hψ hL hs)

end ZhangLS.Spec
