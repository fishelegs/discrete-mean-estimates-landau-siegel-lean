import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Explicit polynomial-logarithm rates

The factorial constant is deliberately retained. This avoids inventing an
unspecified small exponent or using an ineffective asymptotic threshold.
-/
set_option autoImplicit false
namespace ZhangLS.Spec

noncomputable def polynomialLogHalfConstant (k:ℕ) : ℝ := 2^k*(k.factorial:ℝ)

lemma polynomialLogHalfConstant_pos (k:ℕ) : 0<polynomialLogHalfConstant k := by
  unfold polynomialLogHalfConstant
  positivity

theorem polynomialLog_half_power {D:ℝ} (hD:1≤D) (k:ℕ) :
    (Real.log D)^k≤polynomialLogHalfConstant k*Real.sqrt D := by
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hL : 0≤Real.log D := Real.log_nonneg hD
  have hf : 0<(k.factorial:ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (Real.log D/2) (show 0≤Real.log D/2 by positivity) k)
  have he : Real.exp (Real.log D/2)=Real.sqrt D := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hDp]
    congr 1
    ring
  calc
    _=2^k*(Real.log D/2)^k := by rw [←mul_pow]; congr 1; ring
    _≤2^k*(Real.exp (Real.log D/2)*(k.factorial:ℝ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _=_ := by rw [he]; unfold polynomialLogHalfConstant; ring

/-- A concrete D^(-1/2) rate valid already for D≥1, with a fully explicit
constant depending only on the displayed natural logarithmic exponent. -/
theorem polynomialLog_div_decay {D:ℝ} (hD:1≤D) (k:ℕ) :
    (Real.log D)^k/D≤polynomialLogHalfConstant k/Real.sqrt D := by
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  apply (div_le_div_of_nonneg_right (polynomialLog_half_power hD k) hDp.le).trans_eq
  have hs : Real.sqrt D≠0 := (Real.sqrt_pos.mpr hDp).ne'
  have he := Real.sq_sqrt hDp.le
  field_simp
  rw [he]

end ZhangLS.Spec
