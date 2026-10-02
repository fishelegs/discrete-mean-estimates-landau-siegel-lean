import ZhangLS.Spec.Lemma153ActualNorm

/-! Reusable cubic growth estimates. The hypotheses here explicitly require
an independently proved bound for the actual local coefficients. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma162_cubic_half_majorant_summable :
    Summable (fun n : ℕ => ((n:ℝ)+2)^3*(1/2:ℝ)^n) := by
  have hg := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3
    (by norm_num : ‖(1/2:ℝ)‖ < 1)
  convert h3.add ((h2.mul_left 6).add ((h1.mul_left 12).add (hg.mul_left 8))) using 1
  funext n
  ring

noncomputable def lemma162CubicNormConstant : ℝ :=
  ∑' n : ℕ, ((n:ℝ)+2)^3*(1/2:ℝ)^n

lemma lemma162_cubic_norm_constant_nonneg : 0 ≤ lemma162CubicNormConstant :=
  tsum_nonneg (fun _ => by positivity)

/-- Cubic coefficient growth gives a local absolute sum at most 1+C'|z|. -/
lemma lemma162_cubic_local_norm_series (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hzero : a 0 = 1)
    (ha : ∀ n : ℕ, ‖a (n+1)‖ ≤ C*((n:ℝ)+2)^3)
    (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    Summable (fun n : ℕ => ‖a n*z^n‖) ∧
      (∑' n : ℕ, ‖a n*z^n‖) ≤ 1+(C*lemma162CubicNormConstant)*‖z‖ := by
  have hm := lemma162_cubic_half_majorant_summable.mul_left (C*‖z‖)
  have hb (n : ℕ) : ‖a (n+1)*z^(n+1)‖ ≤
      (C*‖z‖)*(((n:ℝ)+2)^3*(1/2:ℝ)^n) := by
    rw [norm_mul,norm_pow,pow_succ ‖z‖]
    have hp := pow_le_pow_left₀ (norm_nonneg z) hz n
    calc
      _ ≤ (C*((n:ℝ)+2)^3)*((1/2:ℝ)^n*‖z‖) := by
        exact mul_le_mul (ha n)
          (mul_le_mul_of_nonneg_right hp (norm_nonneg z))
          (by positivity) (by positivity)
      _ = _ := by ring
  have ht : Summable (fun n : ℕ => ‖a (n+1)*z^(n+1)‖) :=
    hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hs : Summable (fun n : ℕ => ‖a n*z^n‖) :=
    (summable_nat_add_iff 1).mp ht
  refine ⟨hs,?_⟩
  have hsum := ht.tsum_le_tsum hb hm
  rw [tsum_mul_left] at hsum
  rw [hs.tsum_eq_zero_add]
  simp only [hzero,pow_zero,mul_one,norm_one]
  dsimp [lemma162CubicNormConstant] at *
  nlinarith only [hsum]

/-- The same estimate with a possibly non-unit constant term, useful for the
isolated 2-adic series before division by its global normalizer. -/
lemma lemma162_cubic_local_norm_series_general (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n : ℕ, ‖a (n+1)‖ ≤ C*((n:ℝ)+2)^3)
    (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    Summable (fun n : ℕ => ‖a n*z^n‖) ∧
      (∑' n : ℕ, ‖a n*z^n‖) ≤ ‖a 0‖+(C*lemma162CubicNormConstant)*‖z‖ := by
  have hm := lemma162_cubic_half_majorant_summable.mul_left (C*‖z‖)
  have hb (n : ℕ) : ‖a (n+1)*z^(n+1)‖ ≤
      (C*‖z‖)*(((n:ℝ)+2)^3*(1/2:ℝ)^n) := by
    rw [norm_mul,norm_pow,pow_succ ‖z‖]
    have hp := pow_le_pow_left₀ (norm_nonneg z) hz n
    calc
      _ ≤ (C*((n:ℝ)+2)^3)*((1/2:ℝ)^n*‖z‖) := by
        exact mul_le_mul (ha n)
          (mul_le_mul_of_nonneg_right hp (norm_nonneg z))
          (by positivity) (by positivity)
      _ = _ := by ring
  have ht : Summable (fun n : ℕ => ‖a (n+1)*z^(n+1)‖) :=
    hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hs : Summable (fun n : ℕ => ‖a n*z^n‖) :=
    (summable_nat_add_iff 1).mp ht
  refine ⟨hs,?_⟩
  have hsum := ht.tsum_le_tsum hb hm
  rw [tsum_mul_left] at hsum
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero,mul_one]
  dsimp [lemma162CubicNormConstant] at *
  nlinarith only [hsum]

end ZhangLS.Spec
