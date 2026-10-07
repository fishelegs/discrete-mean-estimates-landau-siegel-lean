import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A prescribed-point gap for anchored bounded polynomial families

This is an explicit complex polynomial family in the coefficient class used by
THIRD153. It disproves only the inference from that class and individual
nonvanishing to a uniform positive lower bound at one prescribed point.
It is not a determinant family or a theorem about bad approximability of pi.
It does not contradict an interval-supremum lower bound.
-/

set_option autoImplicit false

open scoped Topology
open Filter

namespace NormalFamilyPointwiseGap

noncomputable def coefficient (n : ℕ) : ℝ := 4 / 9 - 1 / ((n : ℝ) + 1)

/-- An actual polynomial over `ℂ`, indexed from zero. -/
noncomputable def familyPolynomial (n : ℕ) : Polynomial ℂ :=
  Polynomial.C (-1) + Polynomial.X + Polynomial.C (coefficient n : ℂ) * Polynomial.X^2

/-- Evaluation of the actual polynomial, not a sequence of sampled numbers. -/
noncomputable def family (n : ℕ) (z : ℂ) : ℂ := (familyPolynomial n).eval z

noncomputable def target : ℂ := 3 / 4

lemma coefficient_bounds (n : ℕ) : -1 ≤ coefficient n ∧ coefficient n ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hpos).2 (by linarith)
  unfold coefficient
  constructor <;> linarith

lemma coefficient_norm_le (n : ℕ) : ‖(coefficient n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact coefficient_bounds n

theorem family_eq (n : ℕ) (z : ℂ) :
    family n z = -1 + z + (coefficient n : ℂ) * z^2 := by
  simp [family, familyPolynomial]

theorem anchored (n : ℕ) : family n 0 = -1 := by
  simp [family_eq]

theorem constant_coefficient (n : ℕ) : (familyPolynomial n).coeff 0 = -1 := by
  simp [familyPolynomial]

/-- Every nonconstant polynomial coefficient obeys the literal source bound. -/
theorem nonconstant_coefficients (n k : ℕ) (hk : k ≠ 0) :
    ‖(familyPolynomial n).coeff k‖ ≤ 1 := by
  simp only [familyPolynomial, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_C_mul_X_pow]
  by_cases h1 : k = 1
  · subst k
    norm_num
  by_cases h2 : k = 2
  · subst k
    simpa only [show (2 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 2 by decide,
      ite_false, ite_true, zero_add] using coefficient_norm_le n
  simp only [hk, Ne.symm h1, h2, ite_false, zero_add, norm_zero, zero_le_one]

/-- Each member is holomorphic on the whole complex plane. -/
theorem entire (n : ℕ) : AnalyticOnNhd ℂ (family n) Set.univ := by
  exact AnalyticOnNhd.eval_polynomial (familyPolynomial n)

/-- The family is bounded uniformly in `n` on each fixed closed disk. -/
theorem fixed_disk_bound (n : ℕ) {R : ℝ} (_hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖family n z‖ ≤ 1 + R + R^2 := by
  rw [family_eq]
  calc
    ‖-1 + z + (coefficient n : ℂ) * z^2‖
        ≤ ‖(-1 : ℂ) + z‖ + ‖(coefficient n : ℂ) * z^2‖ := norm_add_le _ _
    _ ≤ (‖(-1 : ℂ)‖ + ‖z‖) + ‖(coefficient n : ℂ) * z^2‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = 1 + ‖z‖ + ‖(coefficient n : ℂ)‖ * ‖z‖^2 := by simp [norm_pow]
    _ ≤ 1 + R + 1 * R^2 := by
      gcongr
      exact coefficient_norm_le n
    _ = 1 + R + R^2 := by ring

/-- The target is the fixed real point `3/4`, strictly inside the unit disk. -/
theorem target_inside : 0 < target.re ∧ target.re < 1 ∧ target.im = 0 ∧ ‖target‖ < 1 := by
  norm_num [target, Complex.norm_div]

/-- Exact complex value at the prescribed target. -/
theorem target_value (n : ℕ) :
    family n target = ((-9 / (16 * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [family_eq]
  unfold coefficient target
  push_cast
  field_simp
  ring

/-- The target value is nonzero for every member of the family. -/
theorem target_nonzero (n : ℕ) : family n target ≠ 0 := by
  rw [target_value]
  exact_mod_cast (show (-9 / (16 * ((n : ℝ) + 1)) : ℝ) ≠ 0 by
    apply div_ne_zero
    · norm_num
    · positivity)

theorem target_norm (n : ℕ) : ‖family n target‖ = 9 / (16 * ((n : ℝ) + 1)) := by
  rw [target_value, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have hp : (0 : ℝ) < 16 * ((n : ℝ) + 1) := by positivity
  rw [abs_of_pos hp]
  norm_num

/-- The complex target values converge to zero, despite individual nonvanishing. -/
theorem target_tendsto_zero : Tendsto (fun n : ℕ => family n target) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (-9 / 16)
  convert h using 1
  · ext n
    rw [target_value]
    push_cast
    field_simp
  · norm_num

/-- A quantitative form: every positive proposed lower bound is violated. -/
theorem arbitrarily_small (c : ℝ) (hc : 0 < c) : ∃ n : ℕ, ‖family n target‖ < c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (9 / (16 * c))
  refine ⟨n, ?_⟩
  rw [target_norm]
  have hden : (0 : ℝ) < 16 * ((n : ℝ) + 1) := by positivity
  apply (div_lt_iff₀ hden).2
  have hmul : (9 : ℝ) < (n : ℝ) * (16 * c) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * c)).1 hn
  nlinarith

/-- There is no common positive lower bound at this fixed target. -/
theorem no_uniform_positive_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ‖family n target‖ := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨n, hn⟩ := arbitrarily_small c hc
  exact (not_lt_of_ge (hbound n)) hn

end NormalFamilyPointwiseGap
