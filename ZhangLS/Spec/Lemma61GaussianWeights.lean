import ZhangLS.Spec.Lemma61Parameters

/-! # Actual Gaussian inputs for the original Lemma 6.1

The original family, strict region, actual K/N and actual E1 are retained.
Gaussian inversion and both cutoff errors are proved for the actual weights.
The full Lemma61Target remains unproved: contour and Z-difference bounds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_gaussian_star_below_half {D : ℕ} {y : ℝ} (hy : y ≤ 1 / 2) :
    lemma61GaussianStar D y = 0 := by
  simp only [lemma61GaussianStar,if_neg (not_lt.mpr hy)]

lemma lemma61_gaussian_star_above_half {D : ℕ} {y : ℝ} (hy : 1 / 2 < y) :
    lemma61GaussianStar D y = zhangGaussianWeight D y := by
  simp only [lemma61GaussianStar,if_pos hy]

lemma lemma61_gaussian_star_nonneg {D : ℕ} (hD : 1 < D) (y : ℝ) :
    0 ≤ lemma61GaussianStar D y := by
  by_cases hy : 1 / 2 < y
  · rw [lemma61_gaussian_star_above_half hy]
    exact zhangGaussianWeight_nonneg hD (by linarith only [hy])
  · rw [lemma61_gaussian_star_below_half (le_of_not_gt hy)]

lemma lemma61_P4_pos {D : ℕ} (hD : 1 < D) : 0 < lemma61PaperP4 D := by
  have hL : 0 < lemma23PaperL D := Real.log_pos (by exact_mod_cast hD)
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  dsimp [lemma61PaperP4,lemma51PaperT0]
  positivity

lemma lemma61_complementary_scales {D : ℕ} :
    lemma61PaperP4 D * lemma56PaperT D ^ 2 = lemma23PaperP D * lemma51PaperT0 D := by
  have ht : lemma56PaperT D ≠ 0 := (Real.exp_pos _).ne'
  rw [lemma61PaperP4,zpow_neg,zpow_ofNat]
  field_simp

lemma lemma61_weighted_term_vanishes_outside {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) {n : ℕ}
    (hn : n ∉ Finset.Icc 1 ⌈2 * x⌉₊) : lemma61WeightedTerm D ψ x s n = 0 := by
  by_cases hn0 : n = 0
  · simp [lemma61WeightedTerm,hn0]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hcut : ⌈2 * x⌉₊ < n := by
    simp only [Finset.mem_Icc,not_and] at hn
    exact lt_of_not_ge (hn hn1)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hc : (⌈2 * x⌉₊ : ℝ) < n := by exact_mod_cast hcut
  have hdiv : x / n ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hnr).mpr
    linarith only [Nat.le_ceil (2 * x),hc]
  simp only [lemma61WeightedTerm,if_neg hn0,lemma61_gaussian_star_below_half hdiv,
    Complex.ofReal_zero,mul_zero]

lemma lemma61_actual_weighted_tsum_eq_finite {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) :
    (∑' n : ℕ, lemma61WeightedTerm D ψ x s n) = lemma61WeightedPolynomial D ψ x s := by
  rw [tsum_eq_sum (fun n hn => lemma61_weighted_term_vanishes_outside ψ x s hn)]
  unfold lemma61WeightedPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1
  simp only [lemma61WeightedTerm,if_neg hn0]

lemma lemma61_weighted_polynomial_continuous {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) :
    Continuous (lemma61WeightedPolynomial D ψ x) := by
  unfold lemma61WeightedPolynomial
  fun_prop

lemma lemma61_short_polynomial_continuous {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) : Continuous (lemma61ShortPolynomial D ψ) := by
  unfold lemma61ShortPolynomial
  fun_prop

lemma lemma61_error_integrand_continuous {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    Continuous (fun v : ℝ =>
      ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
  have hc := lemma61_short_polynomial_continuous (D := D) ψ
  fun_prop

lemma lemma61_error_integrand_interval_integrable {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    IntervalIntegrable (fun v : ℝ =>
      ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) :=
  (lemma61_error_integrand_continuous ψ s).intervalIntegrable _ _

lemma lemma61_E1_pos {D p : ℕ} (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (k : ℝ) : 0 < lemma61ActualE1 D ψ s k := by
  have hL : 0 ≤ lemma23PaperL D := Real.log_natCast_nonneg D
  have hab : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20 :=
    neg_le_self (pow_nonneg hL _)
  have hi : 0 ≤ (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
      ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
    apply intervalIntegral.integral_nonneg_of_forall hab
    intro v
    positivity
  unfold lemma61ActualE1
  exact add_pos_of_nonneg_of_pos (mul_nonneg (zpow_nonneg hL _) hi) (Real.exp_pos _)

lemma lemma61_gaussian_star_norm_le_one {D : ℕ} (hD : 1 < D) (y : ℝ) :
    ‖(lemma61GaussianStar D y : ℂ)‖ ≤ 1 := by
  by_cases hy : 1 / 2 < y
  · rw [lemma61_gaussian_star_above_half hy]
    have hy0 : 0 < y := by linarith
    simpa [lemma57GaussianLogWeight,Real.exp_log hy0] using
      lemma57GaussianLogWeight_norm_le_one hD (Real.log y)
  · simp [lemma61_gaussian_star_below_half (le_of_not_gt hy)]

lemma lemma61_gaussian_reciprocal_complement {D : ℕ} {y : ℝ} (hy : 0 < y) :
    zhangGaussianWeight D y + zhangGaussianWeight D (1 / y) = 1 := by
  simpa [Real.exp_log hy,Real.exp_neg,one_div] using
    zhangGaussianWeight_exp_add_neg (D := D) (Real.log y)

lemma lemma61_weighted_term_eq_LSeries_term {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) (n : ℕ) :
    lemma61WeightedTerm D ψ x s n =
      LSeries.term (fun m => ψ (m : ZMod p)) s n * (lemma61GaussianStar D (x / n) : ℂ) := by
  by_cases hn : n = 0
  · simp [lemma61WeightedTerm,hn]
  · rw [lemma61WeightedTerm,if_neg hn,lemma44_LSeries_term_eq_exp _ _ hn]

lemma lemma61_actual_weighted_terms_summable {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) :
    Summable (fun n : ℕ => LSeries.term (fun m => ψ (m : ZMod p)) s n *
      (lemma61GaussianStar D (x / n) : ℂ)) := by
  have hs : Summable (lemma61WeightedTerm D ψ x s) :=
    summable_of_ne_finset_zero (fun n hn => lemma61_weighted_term_vanishes_outside ψ x s hn)
  exact hs.congr (lemma61_weighted_term_eq_LSeries_term ψ x s)

lemma lemma61_region_real_parts {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma61InRegion D s) : 0 < s.re ∧ s.re < 1 := by
  have ha := lemma51_alpha_le_quarter hL
  have hr := abs_lt.mp hs.1
  constructor <;> linarith only [ha,hr.1,hr.2]

lemma lemma61_weighted_polynomial_differentiable {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) :
    Differentiable ℂ (lemma61WeightedPolynomial D ψ x) := by
  unfold lemma61WeightedPolynomial
  fun_prop

lemma lemma61_short_polynomial_differentiable {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) : Differentiable ℂ (lemma61ShortPolynomial D ψ) := by
  unfold lemma61ShortPolynomial
  fun_prop

lemma lemma61_omega_one_imaginary_axis (D : ℕ) (v : ℝ) :
    lemma57OmegaOne D (I * (v : ℂ)) =
      (Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) : ℂ) := by
  unfold lemma57OmegaOne
  rw [Complex.ofReal_exp]
  congr 1
  unfold lemma23PaperL
  push_cast
  rw [mul_pow,I_sq]
  ring

end ZhangLS.Spec
