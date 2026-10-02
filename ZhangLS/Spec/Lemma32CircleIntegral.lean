import ZhangLS.Spec.Lemma32CircleIntegrand
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_actual_normalized_circle_integral_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ) :
    ‖(2*Real.pi*Complex.I : ℂ)⁻¹ *
      circleIntegral (lemma32CircleIntegrand χ) 0 (lemma23PaperL D^(-2024 : ℤ))‖ ≤
      lemma32CircleConstant*lemma23PaperL D^(-2007 : ℤ) := by
  let L := lemma23PaperL D
  have hl0 : 0 < L := by dsimp [L]; linarith
  have hr : 0 ≤ L^(-2024 : ℤ) := (zpow_pos hl0 _).le
  have hbound : ∀ w ∈ sphere (0 : ℂ) (L^(-2024 : ℤ)),
      ‖lemma32CircleIntegrand χ w‖ ≤ lemma32CircleConstant*L^17 := by
    intro w hw
    have hn : ‖w‖ = L^(-2024 : ℤ) := by simpa [dist_eq_norm] using hw
    exact lemma32_circle_integrand_bound χ hD hL hA w hn
  have hi := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hbound
  change ‖(2*Real.pi*Complex.I : ℂ)⁻¹ * circleIntegral (lemma32CircleIntegrand χ) 0
    (L^(-2024 : ℤ))‖ ≤ _ at hi
  calc
    _ ≤ L^(-2024 : ℤ)*(lemma32CircleConstant*L^17) := hi
    _ = lemma32CircleConstant*(L^(-2024 : ℤ)*L^17) := by ring
    _ = _ := by rw [lemma32_residue_circle_scale_identity L hl0]

end ZhangLS.Spec
