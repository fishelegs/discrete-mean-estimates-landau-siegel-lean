import ZhangLS.Spec.Lemma83FinitePrimeBounds
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
Generic finite-prefix estimates for the actual Lemma 15.1 coefficients.
The elementary zeta-series estimate reuses the published Lemma 8.3 bound.
Its import closure does not select a version of any Appendix B module.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZhangLS.Spec

open Finset Set MeasureTheory
open scoped BigOperators

/-- The elementary integral-test estimate, including the zero term (which vanishes). -/
theorem actual151_real_zeta_series_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have h := lemma83_rpow_tsum_le (σ - 1) (by linarith)
  simpa only [show (1 : ℝ) + (σ - 1) = σ by ring, one_div] using h

/-- Denominator form of the elementary zeta-series estimate. -/
theorem actual151_real_zeta_div_series_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ σ) ≤ 1 + 1 / (σ - 1) := by
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    using actual151_real_zeta_series_le hσ

/-- A sharp real-axis upper bound for the norm of the actual Riemann zeta function. -/
theorem actual151_norm_riemannZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hnorm (n : ℕ) : ‖(1 : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ =
      (n : ℝ) ^ (-σ) := by
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hσ0),
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), one_div]
  have hs : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ (σ : ℂ)‖) := by
    simp_rw [hnorm]
    exact Real.summable_nat_rpow.mpr (by linarith)
  calc
    ‖riemannZeta (σ : ℂ)‖ = ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ := by
      rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ)]
    _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := tsum_congr hnorm
    _ ≤ 1 + 1 / (σ - 1) := actual151_real_zeta_series_le hσ

/-- The usual Rankin exponent lies strictly to the right of the line of convergence. -/
theorem actual151_rankin_sigma_gt_one {T : ℝ} (hT : 1 < T) :
    1 < 1 + 1 / Real.log T := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hinv : 0 < 1 / Real.log T := one_div_pos.mpr hlog
  linarith

/-- The pointwise Rankin inequality on `0 < x ≤ T`. -/
theorem actual151_rankin_term_le {T x a : ℝ} (hT : 1 < T)
    (hx : 0 < x) (hxT : x ≤ T) (ha : 0 ≤ a) :
    a / x ≤ Real.exp 1 * (a / x ^ (1 + 1 / Real.log T)) := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hpow : x ^ (1 / Real.log T) ≤ Real.exp 1 := by
    calc
      x ^ (1 / Real.log T) ≤ T ^ (1 / Real.log T) :=
        Real.rpow_le_rpow hx.le hxT (by positivity)
      _ = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hT0]
        congr 1
        field_simp [hlog.ne']
  have hxpow : x ^ (1 / Real.log T) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  calc
    a / x = x ^ (1 / Real.log T) * (a / x ^ (1 + 1 / Real.log T)) := by
      rw [Real.rpow_add hx, Real.rpow_one]
      field_simp [hx.ne', hxpow]
    _ ≤ Real.exp 1 * (a / x ^ (1 + 1 / Real.log T)) :=
      mul_le_mul_of_nonneg_right hpow
        (div_nonneg ha (Real.rpow_nonneg hx.le _))

/-- Rankin's bound for any finite positive support contained in `[1,T]`.
Only the ordinary summability of the absolute Dirichlet series is assumed. -/
theorem actual151_finite_prefix_rankin (a : ℕ → ℝ) {T : ℝ} (hT : 1 < T)
    (ha : ∀ n, 0 ≤ a n) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ T)
    (hsum : Summable (fun n : ℕ => a n / (n : ℝ) ^ (1 + 1 / Real.log T))) :
    (∑ n ∈ s, a n / (n : ℝ)) ≤
      Real.exp 1 * (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) := by
  calc
    (∑ n ∈ s, a n / (n : ℝ)) ≤
        ∑ n ∈ s, Real.exp 1 * (a n / (n : ℝ) ^ (1 + 1 / Real.log T)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact actual151_rankin_term_le hT (Nat.cast_pos.mpr (hs n hn).1)
        (hs n hn).2 (ha n)
    _ = Real.exp 1 * ∑ n ∈ s, a n / (n : ℝ) ^ (1 + 1 / Real.log T) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      exact hsum.sum_le_tsum s
        (fun n _ => div_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- The floor-cutoff form of the finite-prefix Rankin estimate. -/
theorem actual151_Icc_prefix_rankin (a : ℕ → ℝ) {T : ℝ} (hT : 1 < T)
    (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable (fun n : ℕ => a n / (n : ℝ) ^ (1 + 1 / Real.log T))) :
    (∑ n ∈ Finset.Icc 1 ⌊T⌋₊, a n / (n : ℝ)) ≤
      Real.exp 1 * (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) := by
  apply actual151_finite_prefix_rankin a hT ha _ _ hsum
  intro n hn
  obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
  exact ⟨hn1, (Nat.cast_le.mpr hnT).trans (Nat.floor_le (by linarith))⟩

/-- The strict-cutoff form, useful when the original coefficient vanishes at `T`. -/
theorem actual151_strict_prefix_rankin (a : ℕ → ℝ) {T : ℝ} (hT : 1 < T)
    (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable (fun n : ℕ => a n / (n : ℝ) ^ (1 + 1 / Real.log T))) :
    (∑ n ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun n : ℕ => (n : ℝ) < T), a n / (n : ℝ)) ≤
      Real.exp 1 * (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) := by
  apply actual151_finite_prefix_rankin a hT ha _ _ hsum
  intro n hn
  obtain ⟨hnI, hnT⟩ := Finset.mem_filter.mp hn
  exact ⟨(Finset.mem_Icc.mp hnI).1, hnT.le⟩

/-- The zero term causes no mismatch between `LSeries.term` and the real absolute series. -/
theorem actual151_norm_lseries_term_real (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ‖LSeries.term a (σ : ℂ) n‖ = ‖a n‖ / (n : ℝ) ^ σ := by
  rw [LSeries.norm_term_eq, Complex.ofReal_re]
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hσ.ne']
  · simp [hn]

/-- Transport absolute convergence into the real-series formulation used by Rankin's bound. -/
theorem actual151_abs_real_series_summable (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsum : LSeriesSummable a (σ : ℂ)) :
    Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ σ) := by
  simpa only [actual151_norm_lseries_term_real a hσ] using hsum.norm

/-- A fourth-power zeta majorant gives a fourth power of `log T` for the weighted prefix. -/
theorem actual151_finite_prefix_log_fourth_of_zeta (a : ℕ → ℝ) {T C : ℝ}
    (hT : 1 < T) (hlog : 1 ≤ Real.log T) (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ T)
    (hsum : Summable (fun n : ℕ => a n / (n : ℝ) ^ (1 + 1 / Real.log T)))
    (heuler : (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) ≤
      C * ‖riemannZeta ((1 + 1 / Real.log T : ℝ) : ℂ)‖ ^ 4) :
    (∑ n ∈ s, a n / (n : ℝ)) ≤
      16 * Real.exp 1 * C * (Real.log T) ^ 4 := by
  have hz : ‖riemannZeta ((1 + 1 / Real.log T : ℝ) : ℂ)‖ ≤ 2 * Real.log T := by
    calc
      ‖riemannZeta ((1 + 1 / Real.log T : ℝ) : ℂ)‖ ≤
          1 + 1 / ((1 + 1 / Real.log T) - 1) :=
        actual151_norm_riemannZeta_real_le (actual151_rankin_sigma_gt_one hT)
      _ = 1 + Real.log T := by simp
      _ ≤ 2 * Real.log T := by linarith
  calc
    (∑ n ∈ s, a n / (n : ℝ)) ≤
        Real.exp 1 * (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) :=
      actual151_finite_prefix_rankin a hT ha s hs hsum
    _ ≤ Real.exp 1 * (C * ‖riemannZeta ((1 + 1 / Real.log T : ℝ) : ℂ)‖ ^ 4) :=
      mul_le_mul_of_nonneg_left heuler (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (C * (2 * Real.log T) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 4) hC
    _ = 16 * Real.exp 1 * C * (Real.log T) ^ 4 := by ring

/-- With the paper scale `log T = L^(11/10)`, the weighted prefix is `O(L^(22/5))`.
The only analytic inputs concern the global absolutely convergent Euler series. -/
theorem actual151_finite_prefix_L_22_5_of_zeta (a : ℕ → ℝ) {T L C : ℝ}
    (hT : 1 < T) (hL : 1 ≤ L) (hlog : Real.log T = L ^ (11 / 10 : ℝ))
    (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ T)
    (hsum : Summable (fun n : ℕ => a n / (n : ℝ) ^ (1 + 1 / Real.log T)))
    (heuler : (∑' n : ℕ, a n / (n : ℝ) ^ (1 + 1 / Real.log T)) ≤
      C * ‖riemannZeta ((1 + 1 / Real.log T : ℝ) : ℂ)‖ ^ 4) :
    (∑ n ∈ s, a n / (n : ℝ)) ≤
      16 * Real.exp 1 * C * L ^ (22 / 5 : ℝ) := by
  have hlog1 : 1 ≤ Real.log T := by
    rw [hlog]
    exact Real.one_le_rpow hL (by norm_num)
  have hpow : (Real.log T) ^ (4 : ℕ) = L ^ (22 / 5 : ℝ) := by
    rw [hlog, ← Real.rpow_mul_natCast (by linarith : 0 ≤ L)]
    norm_num
  simpa only [hpow] using actual151_finite_prefix_log_fourth_of_zeta
    a hT hlog1 hC ha s hs hsum heuler

end ZhangLS.Spec
