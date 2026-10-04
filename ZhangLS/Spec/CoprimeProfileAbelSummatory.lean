import ZhangLS.Spec.CoprimeProfileAbelArithmetic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def mainConstant (D : ℕ) : ℝ :=
  (6 / Real.pi ^ 2) * ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

noncomputable def truncatedDensity (D N : ℕ) : ℝ :=
  density D * ∑ d ∈ Ioc 0 N, mobiusWeight D d / (d : ℝ)

lemma mobiusWeight_abs_le (D n : ℕ) : |mobiusWeight D n| ≤ (n : ℝ)⁻¹ := by
  change |if n.Coprime D then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) else 0| ≤ _
  split_ifs
  · simp only [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hm : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    simpa only [one_div] using div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)
  · simp

lemma unitCount_scaled_error {D : ℕ} (hD : 0 < D) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    |unitCount D (N / d) - ((N : ℝ) / (d : ℝ)) * density D| ≤ (D.divisors.card : ℝ) := by
  rw [unitCount_mobius hD, ← mobius_density hD]
  have he : (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℝ) * (N / d / e : ℕ)) -
      ((N : ℝ) / (d : ℝ)) * (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℝ) / (e : ℝ)) =
      ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℝ) *
        (((N / (d * e) : ℕ) : ℝ) - (N : ℝ) / ((d * e : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    rw [Nat.div_div_eq_div_mul, Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  calc
    _ ≤ ∑ e ∈ D.divisors, |(ArithmeticFunction.moebius e : ℝ) *
        (((N / (d * e) : ℕ) : ℝ) - (N : ℝ) / ((d * e : ℕ) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ D.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have hm : |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 hD
      rw [abs_mul]
      exact (mul_le_mul hm (nat_division_error N (Nat.mul_pos hd hepos))
        (abs_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by simp

/-- Exact finite arithmetic error, before replacing the finite Möbius density
by its absolutely convergent Euler value. -/
lemma finite_density_error {D : ℕ} (hD : 0 < D) (N : ℕ) :
    |summatory D (N : ℝ) - (N : ℝ) * truncatedDensity D N| ≤
      (D.divisors.card : ℝ) * (harmonic N : ℝ) := by
  have he : summatory D (N : ℝ) - (N : ℝ) * truncatedDensity D N =
      ∑ d ∈ Ioc 0 N, mobiusWeight D d *
        (unitCount D (N / d) - ((N : ℝ) / (d : ℝ)) * density D) := by
    rw [summatory_integer_mobius, truncatedDensity, ← mul_assoc, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, |mobiusWeight D d| *
        |unitCount D (N / d) - ((N : ℝ) / (d : ℝ)) * density D| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun d => mobiusWeight D d *
          (unitCount D (N / d) - ((N : ℝ) / (d : ℝ)) * density D)) (Ioc 0 N)
    _ ≤ ∑ d ∈ Ioc 0 N, (d : ℝ)⁻¹ * (D.divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      exact mul_le_mul (mobiusWeight_abs_le D d) (unitCount_scaled_error hD N hdpos)
        (abs_nonneg _) (by positivity)
    _ = _ := by
      have hi : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
      rw [← Finset.sum_mul, hi]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      ring

end ZhangLS.Spec.CoprimeProfileAbel
