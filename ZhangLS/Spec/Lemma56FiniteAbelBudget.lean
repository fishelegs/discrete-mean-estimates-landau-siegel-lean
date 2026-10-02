import ZhangLS.Spec.Lemma56PrimeLogWindow
import Mathlib.Algebra.BigOperators.Module

/-! # Actual finite Abel conversion for original Lemma 5.6

Actual prime-mass normalization and the faithful principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_finite_abel_positive_budget {m n : ℕ} (hmn : m < n)
    (w : ℕ → ℝ) (c : ℕ → ℂ) {A : ℝ}
    (hmono : MonotoneOn w (Set.Icc m (n - 1))) (hw : 0 ≤ w m)
    (hc : ∀ k : ℕ, m ≤ k → k ≤ n → ‖∑ j ∈ range k, c j‖ ≤ A) :
    ‖∑ j ∈ Ico m n, w j • c j‖ ≤ 2 * A * w (n - 1) := by
  have hm : m ≤ n - 1 := Nat.le_sub_one_of_lt hmn
  have htop : 0 ≤ w (n - 1) := hw.trans
    (hmono ⟨le_rfl, hm⟩ ⟨hm, le_rfl⟩ hm)
  have hd : ∀ j ∈ Ico m (n - 1), 0 ≤ w (j + 1) - w j := by
    intro j hj
    have hh := mem_Ico.mp hj
    apply sub_nonneg.mpr
    exact hmono ⟨hh.1, hh.2.le⟩ ⟨by omega, by omega⟩ (by omega)
  have hmid : ‖∑ j ∈ Ico m (n - 1),
      (w (j + 1) - w j) • (∑ k ∈ range (j + 1), c k)‖ ≤
        A * (w (n - 1) - w m) := by
    calc
      _ ≤ ∑ j ∈ Ico m (n - 1),
          ‖(w (j + 1) - w j) • (∑ k ∈ range (j + 1), c k)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Ico m (n - 1), (w (j + 1) - w j) * A := by
        apply sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd j hj)]
        apply mul_le_mul_of_nonneg_left _ (hd j hj)
        have hh := mem_Ico.mp hj
        exact hc (j + 1) (by omega) (by omega)
      _ = A * (w (n - 1) - w m) := by
        rw [← sum_mul, sum_Ico_sub w hm]
        ring
  have hfirst : ‖w (n - 1) • (∑ j ∈ range n, c j)‖ ≤ w (n - 1) * A := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htop]
    exact mul_le_mul_of_nonneg_left (hc n hmn.le le_rfl) htop
  have hsecond : ‖w m • (∑ j ∈ range m, c j)‖ ≤ w m * A := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (hc m le_rfl hmn.le) hw
  rw [sum_Ico_by_parts w c hmn]
  have h1 := norm_sub_le (w (n - 1) • (∑ j ∈ range n, c j))
    (w m • (∑ j ∈ range m, c j))
  have h2 := norm_sub_le
    (w (n - 1) • (∑ j ∈ range n, c j) - w m • (∑ j ∈ range m, c j))
    (∑ j ∈ Ico m (n - 1), (w (j + 1) - w j) • (∑ k ∈ range (j + 1), c k))
  nlinarith only [h1, h2, hfirst, hsecond, hmid]

lemma lemma56_prime_weight_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hlogx : 1 ≤ Real.log x) : x / Real.log x ≤ y / Real.log y := by
  have hy : 0 < y := hx.trans_le hxy
  have hlogy : 1 ≤ Real.log y := hlogx.trans (Real.log_le_log hx hxy)
  have hratio : 0 < y / x := div_pos hy hx
  have he := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hy.ne' hx.ne'] at he
  have hh := mul_le_mul_of_nonneg_left he hx.le
  have heq : x * (y / x - 1) = y - x := by field_simp
  rw [heq] at hh
  have hp := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hlogx)
  apply (div_le_div_iff₀ (by linarith only [hlogx] : 0 < Real.log x)
    (by linarith only [hlogy] : 0 < Real.log y)).mpr
  nlinarith only [hh, hp]

end ZhangLS.Spec
