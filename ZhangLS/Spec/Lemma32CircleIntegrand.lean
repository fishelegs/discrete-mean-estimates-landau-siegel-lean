import ZhangLS.Spec.Lemma32ZetaCircle
import ZhangLS.Spec.Lemma32SmoothingCircle
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32CircleConstant : ℝ :=
  lemma32RegularProductBound (3/4)*(8*(1+16*Real.exp 1))^8*
    (8*Real.exp 1*lemma32GammaLocalBound)

noncomputable def lemma32CircleIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ :=
  lemma32AnalyticCorrection χ (1+w)*
    (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
    (lemma32SmoothingDifference (lemma23PaperL D) w*Complex.Gamma w)

lemma lemma32_circle_constant_pos : 0 < lemma32CircleConstant := by
  unfold lemma32CircleConstant
  exact mul_pos (mul_pos (lemma32_regular_product_bound_pos (3/4)) (by positivity))
    (mul_pos (by positivity) lemma32_gamma_local_bound_pos)

lemma lemma32_circle_integrand_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (w : ℂ) (hw : ‖w‖ = lemma23PaperL D^(-2024 : ℤ)) :
    ‖lemma32CircleIntegrand χ w‖ ≤ lemma32CircleConstant*lemma23PaperL D^17 := by
  let L := lemma23PaperL D
  have hl0 : 0 < L := by dsimp [L]; linarith
  have hr : 0 < L^(-2024 : ℤ) := zpow_pos hl0 _
  have h0 : w ≠ 0 := by intro hh; rw [hh,norm_zero] at hw; linarith
  have hs : ‖(1+w)-1‖ = L^(-2024 : ℤ) := by simpa only [add_sub_cancel_left] using hw
  have hc := lemma32_analytic_correction_residue_disk_bound χ hL (1+w) hs.le
  have hz := lemma32_actual_zeta_L_residue_circle_bound χ hD hL hA (1+w) hs
  have hg := lemma32_smoothing_gamma_local_bound L hL w hw.le h0
  have hk0 : 0 ≤ lemma32RegularProductBound (3/4) := (lemma32_regular_product_bound_pos (3/4)).le
  unfold lemma32CircleIntegrand
  rw [norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ lemma32RegularProductBound (3/4)*(8*(1+16*Real.exp 1)*L^2)^8*
        (8*Real.exp 1*lemma32GammaLocalBound*L) := by gcongr <;> positivity
    _ = lemma32CircleConstant*L^17 := by
      unfold lemma32CircleConstant
      rw [mul_pow,← pow_mul]
      ring

lemma lemma32_residue_circle_scale_identity (L : ℝ) (hL : 0 < L) :
    L^(-2024 : ℤ)*L^17 = L^(-2007 : ℤ) := by
  simpa only [Int.reduceAdd,zpow_ofNat] using
    (zpow_add₀ (ne_of_gt hL) (-2024 : ℤ) 17).symm

end ZhangLS.Spec
