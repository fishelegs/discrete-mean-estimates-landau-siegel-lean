import ZhangLS.Spec.Lemma82ScaledTail
import Mathlib.NumberTheory.Harmonic.Bounds

namespace ZhangLS.Spec
open Complex Finset
open scoped Real
set_option maxHeartbeats 1200000

/-- The periodic-character tail of the actual continued L-function. -/
lemma chi_actual_truncation_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    ‖dirichletLFunction χ s - lemma82FinitePolynomial χ x s‖ ≤
      x ^ (-s.re) * (D : ℝ) * (‖s‖ / s.re + 1) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : 0 < x ^ s.re := Real.rpow_pos_of_pos hxp _
  have hh := lemma82_scaled_remainder_norm χ hD hx hs
  unfold lemma82ScaledRemainder at hh
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hxp] at hh
  rw [Real.rpow_neg hxp.le]
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hp.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] using hh'

lemma chi_finite_polynomial_harmonic_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x M : ℝ} (hx : 1 ≤ x) {s : ℂ}
    (hweight : ∀ t : ℝ, 1 ≤ t → t ≤ x → t ^ (1 - s.re) ≤ M)
    (hM : 0 ≤ M) :
    ‖lemma82FinitePolynomial χ x s‖ ≤ M * (1 + Real.log x) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖χ.evalNat n * (n : ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, M * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnp : (0 : ℝ) < n := by linarith
      have hnx : (n : ℝ) ≤ x :=
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ ⌊x⌋₊).trans
          (Nat.floor_le hxp.le)
      rw [norm_mul, norm_natCast_cpow_of_pos (by exact_mod_cast hnp), Complex.neg_re]
      calc
        _ ≤ (n : ℝ)^(-s.re) := mul_le_of_le_one_left
          (Real.rpow_nonneg hnp.le _) (χ.evalNat_norm_le_one n)
        _ = (n : ℝ)^(1-s.re) * (n : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hnp]
          congr 1
          ring
        _ ≤ M * (n : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (hweight n hn1 hnx) (by positivity)
    _ = M * (harmonic ⌊x⌋₊ : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ M * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log x hx) hM

lemma chi_rpow_strip_weight {D : ℕ} (hD : 1 < D)
    {s : ℂ} (hσ : 1 - 4 / Real.log (D : ℝ) ≤ s.re)
    {t : ℝ} (ht : 1 ≤ t) (htD : t ≤ (D : ℝ)^4) :
    t ^ (1 - s.re) ≤ Real.exp 16 := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  have hDp : (0 : ℝ) < D := by linarith
  have hL : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have htp : 0 < t := by linarith
  apply (Real.rpow_le_rpow_of_exponent_le ht (by linarith : 1-s.re ≤ 4 / Real.log (D : ℝ))).trans
  rw [Real.rpow_def_of_pos htp]
  apply Real.exp_le_exp.mpr
  have hh := Real.log_le_log htp htD
  rw [Real.log_pow] at hh
  have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ 4 / Real.log (D : ℝ) by positivity)
  have he : 4 * Real.log (D : ℝ) * (4 / Real.log (D : ℝ)) = 16 := by field_simp <;> ring
  simpa only [Nat.cast_ofNat, he] using hh'

/-- A genuine uniform logarithmic upper bound up to conductor height.
The truncation is D⁴; the saved power controls the true periodic-character tail. -/
theorem chi_actual_L_uniform_log_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 8 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hσ : 1 - 4 / Real.log (D : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 4 * (D : ℝ)) :
    ‖dirichletLFunction χ s‖ ≤ 14 * Real.exp 16 * Real.log (D : ℝ) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hDp : (0 : ℝ) < D := by linarith
  have hLp : 0 < Real.log (D : ℝ) := by linarith
  have hx : 1 ≤ (D : ℝ)^4 := one_le_pow₀ hD1
  have hxp : 0 < (D : ℝ)^4 := by positivity
  have hs2 : 1/2 ≤ s.re := by
    have hi : 4 / Real.log (D : ℝ) ≤ (1:ℝ)/2 := (div_le_iff₀ hLp).mpr (by linarith)
    linarith
  have hs : 0 < s.re := by linarith
  have hpoly := chi_finite_polynomial_harmonic_bound χ hx
    (fun t ht htx => chi_rpow_strip_weight hD hσ ht htx) (Real.exp_pos 16).le
  rw [Real.log_pow] at hpoly
  norm_num only [Nat.cast_ofNat] at hpoly
  have hpow : ((D : ℝ)^4)^(-s.re) ≤ Real.exp 16 / (D : ℝ)^4 := by
    have hh := chi_rpow_strip_weight hD hσ hx (le_refl ((D : ℝ)^4))
    have he : ((D : ℝ)^4)^(-s.re) = ((D : ℝ)^4)^(1-s.re) / (D : ℝ)^4 := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hxp]
      congr 1
      ring
    rw [he]
    exact div_le_div_of_nonneg_right hh hxp.le
  have hq : ‖s‖ / s.re + 1 ≤ 9 * (D : ℝ) := by
    have hh : ‖s‖ / s.re ≤ 8 * (D : ℝ) := by
      apply (div_le_iff₀ hs).mpr
      nlinarith
    linarith
  have herr := chi_actual_truncation_error χ hD hx hs
  have herr' : ‖dirichletLFunction χ s - lemma82FinitePolynomial χ ((D : ℝ)^4) s‖ ≤
      9 * Real.exp 16 := by
    apply herr.trans
    calc
      _ ≤ (Real.exp 16 / (D : ℝ)^4) * (D : ℝ) * (9 * (D : ℝ)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hpow hDp.le) hq
          (by positivity) (by positivity)
      _ = 9 * Real.exp 16 / (D : ℝ)^2 := by field_simp <;> ring
      _ ≤ 9 * Real.exp 16 := div_le_self (by positivity) (one_le_pow₀ hD1)
  have hn := norm_add_le
    (dirichletLFunction χ s - lemma82FinitePolynomial χ ((D : ℝ)^4) s)
    (lemma82FinitePolynomial χ ((D : ℝ)^4) s)
  rw [sub_add_cancel] at hn
  have hsum := hn.trans (add_le_add herr' hpoly)
  nlinarith [Real.exp_pos 16]

end ZhangLS.Spec
