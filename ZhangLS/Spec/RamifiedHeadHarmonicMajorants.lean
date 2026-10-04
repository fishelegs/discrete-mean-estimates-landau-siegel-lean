import ZhangLS.Spec.ShortUpsilonArithmetic
import ZhangLS.Spec.RamifiedHeadHarmonicTau

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZhangLS.Spec

open Finset
open scoped Classical

/-- The actual short-upsilon coefficient is controlled by the actual nonnegative nu. -/
theorem ramifiedHead_upsilon_norm_le_nu {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23UpsilonArithmeticFunction χ n‖ ≤ ‖lemma23NuArithmeticFunction χ n‖ :=
  shortUpsilon_norm_le_nu χ n

/-- The actual nu is bounded by the ordinary two-fold divisor function. -/
theorem ramifiedHead_nu_norm_le_tau_two {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖ ≤ (lemma34Tau 2 n : ℝ) := by
  rw [lemma34_tau2_eq_divisor_card]
  exact lemma23NuArithmeticFunction_norm_le_card_divisors χ n

/-- The one-variable majorant used in each ramified harmonic fibre. -/
noncomputable def ramifiedHeadNuWeight {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) : ℝ :=
  ‖lemma23NuArithmeticFunction χ n‖ * (lemma34Tau 4 n : ℝ) / (n : ℝ)

theorem ramifiedHead_nu_weight_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ ramifiedHeadNuWeight χ n := by
  unfold ramifiedHeadNuWeight
  positivity

theorem ramifiedHead_nu_weight_le_tau_product {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ramifiedHeadNuWeight χ n ≤
      (lemma34Tau 2 n : ℝ)*(lemma34Tau 4 n : ℝ)*(n : ℝ)⁻¹ := by
  unfold ramifiedHeadNuWeight
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (ramifiedHead_nu_norm_le_tau_two χ n) (by positivity))
    (by positivity)

/-- Mixed nu-tau-four harmonic mass has the divisor-product exponent eight. -/
theorem ramifiedHead_nu_weight_harmonic_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, ramifiedHeadNuWeight χ n) ≤ (harmonic X : ℝ)^8 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 X,
        (lemma34Tau 2 n : ℝ)*(lemma34Tau 4 n : ℝ)*(n : ℝ)⁻¹ := by
      exact sum_le_sum (fun n _ => ramifiedHead_nu_weight_le_tau_product χ n)
    _ ≤ _ := by
      simpa using lemma34_tau_product_harmonic_sum_le 2 4 X (by omega) (by omega) hX

/-- The corresponding logarithmic majorant for the actual nu coefficients. -/
theorem ramifiedHead_nu_weight_log_le {D : ℕ}
    (χ : RealPrimitiveCharacter D) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, ramifiedHeadNuWeight χ n) ≤ (1+Real.log (X : ℝ))^8 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 X,
        (lemma34Tau 2 n : ℝ)*(lemma34Tau 4 n : ℝ)*(n : ℝ)⁻¹ := by
      exact sum_le_sum (fun n _ => ramifiedHead_nu_weight_le_tau_product χ n)
    _ ≤ _ := by
      simpa using lemma34_tau_product_log_sum_le 2 4 X (by omega) (by omega) hX

end ZhangLS.Spec
