import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite Fejér kernel on the closed complex unit disk

A positive squared-norm identity proves the uniform lower bound and the
linear value at one. These are finite algebraic estimates used to detect
actual local zero power sums; no zero-exclusion hypothesis is introduced.
-/

namespace ZhangLS.Spec

open Complex Finset

noncomputable def lemma55FejerGeom (z : ℂ) (n : ℕ) : ℂ := ∑ k ∈ range n, z ^ k

lemma lemma55_fejer_geom_rec (z : ℂ) (n : ℕ) :
    lemma55FejerGeom z (n + 1) = 1 + z * lemma55FejerGeom z n := by
  unfold lemma55FejerGeom
  rw [sum_range_succ']
  simp only [pow_zero, mul_sum, pow_succ']
  ring

lemma lemma55_fejer_geom_norm_rec (z : ℂ) (n : ℕ) :
    normSq (lemma55FejerGeom z (n + 1)) =
      1 + 2 * (z * lemma55FejerGeom z n).re + normSq z * normSq (lemma55FejerGeom z n) := by
  rw [lemma55_fejer_geom_rec, normSq_add, normSq_one, normSq_mul]
  simp only [one_mul, conj_re]
  ring

lemma lemma55_fejer_positive_identity (z : ℂ) (J : ℕ) :
    ((J + 1 : ℕ) : ℝ) + 2 * ∑ n ∈ range (J + 1), (z * lemma55FejerGeom z n).re =
      normSq (lemma55FejerGeom z (J + 1)) +
        (1 - normSq z) * ∑ n ∈ range (J + 1), normSq (lemma55FejerGeom z n) := by
  induction J with
  | zero => simp [lemma55FejerGeom]
  | succ J ih =>
    conv_lhs => rw [sum_range_succ]
    conv_rhs => rw [sum_range_succ]
    rw [lemma55_fejer_geom_norm_rec]
    push_cast
    have h := ih
    push_cast at h
    nlinarith only [h]

lemma lemma55_fejer_nested_lower_bound {z : ℂ} (hz : ‖z‖ ≤ 1) (J : ℕ) :
    -((J + 1 : ℕ) : ℝ) / 2 ≤ ∑ n ∈ range (J + 1), (z * lemma55FejerGeom z n).re := by
  have hsq : normSq z ≤ 1 := by
    rw [normSq_eq_norm_sq]
    nlinarith only [hz, norm_nonneg z]
  have hn : 0 ≤ normSq (lemma55FejerGeom z (J + 1)) +
      (1 - normSq z) * ∑ n ∈ range (J + 1), normSq (lemma55FejerGeom z n) := by
    exact add_nonneg (normSq_nonneg _) (mul_nonneg (by linarith only [hsq])
      (sum_nonneg (fun n _ => normSq_nonneg _)))
  rw [← lemma55_fejer_positive_identity] at hn
  linarith only [hn]


lemma lemma55_fejer_nested_eq_weighted (z : ℂ) (J : ℕ) :
    (∑ n ∈ range (J + 1), z * lemma55FejerGeom z n) =
      ∑ j ∈ range J, ((J - j : ℕ) : ℂ) * z ^ (j + 1) := by
  induction J with
  | zero => simp [lemma55FejerGeom]
  | succ J ih =>
    conv_lhs => rw [sum_range_succ, ih]
    conv_rhs => rw [sum_range_succ]
    have hc : (∑ j ∈ range J, ((J + 1 - j : ℕ) : ℂ) * z ^ (j + 1)) =
        (∑ j ∈ range J, ((J - j : ℕ) : ℂ) * z ^ (j + 1)) +
          ∑ j ∈ range J, z ^ (j + 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      have hn : J + 1 - j = (J - j) + 1 := by
        have hlt := mem_range.mp hj
        omega
      rw [hn, Nat.cast_add, Nat.cast_one]
      ring
    rw [hc]
    have hg : z * lemma55FejerGeom z (J + 1) =
        (∑ j ∈ range J, z ^ (j + 1)) + z ^ (J + 1) := by
      simp only [lemma55FejerGeom, sum_range_succ, mul_add, mul_sum, pow_succ']
    rw [hg]
    simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
    ring

noncomputable def lemma55FejerKernel (z : ℂ) (J : ℕ) : ℝ :=
  (∑ n ∈ range (J + 1), (z * lemma55FejerGeom z n).re) / ((J + 1 : ℕ) : ℝ)

lemma lemma55_fejer_kernel_lower_bound {z : ℂ} (hz : ‖z‖ ≤ 1) (J : ℕ) :
    -(1 : ℝ) / 2 ≤ lemma55FejerKernel z J := by
  unfold lemma55FejerKernel
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (J + 1 : ℕ))).mpr
  have h := lemma55_fejer_nested_lower_bound hz J
  linarith only [h]

lemma lemma55_fejer_kernel_at_one (J : ℕ) : lemma55FejerKernel 1 J = (J : ℝ) / 2 := by
  have hsum : ∑ n ∈ range (J + 1), (n : ℝ) = (J : ℝ) * ((J : ℝ) + 1) / 2 := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  unfold lemma55FejerKernel
  simp only [lemma55FejerGeom, one_pow, sum_const, card_range, nsmul_eq_mul,
    mul_one, one_mul, natCast_re]
  rw [hsum]
  push_cast
  field_simp

end ZhangLS.Spec

