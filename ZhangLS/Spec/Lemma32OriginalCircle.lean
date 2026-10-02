import ZhangLS.Spec.Lemma32CircleIntegral
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_modulus_cpow_eq_exp {D : ℕ} (hD : 0 < D) (k : ℕ) (w : ℂ) :
    (D : ℂ)^((k : ℂ)*w) = Complex.exp ((k : ℂ)*(lemma23PaperL D : ℂ)*w) := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast hD
  change ((D : ℝ) : ℂ)^((k : ℂ)*w) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hd.ne'),
    ← Complex.ofReal_log hd.le]
  congr 1
  change (Real.log (D : ℝ) : ℂ)*((k : ℂ)*w) = (k : ℂ)*(Real.log (D : ℝ) : ℂ)*w
  ring

lemma lemma32_original_smoothing_difference {D : ℕ} (hD : 0 < D) (w : ℂ) :
    (D : ℂ)^((8 : ℂ)*w)-(D : ℂ)^((4 : ℂ)*w) =
      lemma32SmoothingDifference (lemma23PaperL D) w := by
  have h8 := lemma32_modulus_cpow_eq_exp hD 8 w
  have h4 := lemma32_modulus_cpow_eq_exp hD 4 w
  norm_num only [Nat.cast_ofNat] at h8 h4
  rw [h8,h4]
  rfl

lemma lemma32_original_normalized_circle_integral_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ) :
    ‖(2*Real.pi*Complex.I : ℂ)⁻¹ * circleIntegral
      (fun w : ℂ => lemma32AnalyticCorrection χ (1+w)*
        (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
        (((D : ℂ)^((8 : ℂ)*w)-(D : ℂ)^((4 : ℂ)*w))*Complex.Gamma w))
      0 (lemma23PaperL D^(-2024 : ℤ))‖ ≤
      lemma32CircleConstant*lemma23PaperL D^(-2007 : ℤ) := by
  have he : (fun w : ℂ => lemma32AnalyticCorrection χ (1+w)*
      (riemannZeta (1+w)*dirichletLFunction χ (1+w))^8*
      (((D : ℂ)^((8 : ℂ)*w)-(D : ℂ)^((4 : ℂ)*w))*Complex.Gamma w)) =
      lemma32CircleIntegrand χ := by
    funext w
    rw [lemma32_original_smoothing_difference (by omega : 0 < D) w]
    rfl
  rw [he]
  exact lemma32_actual_normalized_circle_integral_bound χ hD hL hA

end ZhangLS.Spec
