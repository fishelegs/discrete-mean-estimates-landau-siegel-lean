import ZhangLS.Spec.Lemma82Definitions

namespace ZhangLS.Spec
open Complex Finset
open scoped Real
set_option maxHeartbeats 1000000

lemma lemma82_positive_ratio_cpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (b : ℂ) :
    ((x/y : ℝ) : ℂ)^b = (x:ℂ)^b * (y:ℂ)^(-b) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hx hy).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.exp_add,
    ← Complex.ofReal_log (div_pos hx hy).le, ← Complex.ofReal_log hx.le,
    ← Complex.ofReal_log hy.le, Real.log_div hx.ne' hy.ne', Complex.ofReal_sub]
  congr 1
  ring

lemma lemma82_original_term {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n)
    (v a b : ℂ) :
    v / (n:ℂ)^(1-a) * ((x/(n:ℝ) : ℝ) : ℂ)^b =
      (x:ℂ)^b * (v * (n:ℂ)^(-(1+b-a))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [lemma82_positive_ratio_cpow hx hnR b, Complex.ofReal_natCast,
    div_eq_mul_inv, ← Complex.cpow_neg]
  calc
    _ = (x:ℂ)^b * (v * ((n:ℂ)^(-(1-a)) * (n:ℂ)^(-b))) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hnC]
      congr 3
      ring

lemma lemma82_shifted_sum_eq_weighted {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ : ℕ) {x : ℝ} (hx : 0 < x) :
    lemma82ShiftedSum χ c j μ x =
      (x:ℂ)^(lemma82SmoothingBeta D μ) *
        lemma82WeightedPolynomial χ x (1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j) := by
  rw [← lemma82_strict_weighted_eq χ hx]
  unfold lemma82ShiftedSum lemma82StrictCutoff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  rw [lemma82_original_term hx hnp]
  ring

lemma lemma82_original_analytic_bridge {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (c : ℝ) (j : Fin 3) (μ : ℕ) {x : ℝ} (hx : 1 ≤ x)
    (hnorm : ‖1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j‖ ≤ 2) :
    ‖lemma82ShiftedSum χ c j μ x - (x:ℂ)^(lemma82SmoothingBeta D μ) *
      ((Real.log x : ℂ) * dirichletLFunction χ
        (1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j) +
        deriv (dirichletLFunction χ) (1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j))‖ ≤
      16*(D:ℝ)/x := by
  have hxp := lt_of_lt_of_le zero_lt_one hx
  rw [lemma82_shifted_sum_eq_weighted χ c j μ hxp, ← mul_sub, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxp, lemma82_smoothing_beta_re, Real.rpow_zero, one_mul]
  apply lemma82_weighted_abel_error χ hD hx _ hnorm
  simp [lemma82_smoothing_beta_re, lemma82_beta_re]

end ZhangLS.Spec
