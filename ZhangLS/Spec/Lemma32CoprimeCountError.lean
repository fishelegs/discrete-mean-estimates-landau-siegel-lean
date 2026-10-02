import ZhangLS.Spec.Lemma32CoprimeMobiusCount
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_real_nat_division_error (A : ℕ) {d : ℕ} (hd : 0 < d) :
    |(A/d : ℕ)-(A : ℝ)/(d : ℝ)| ≤ 1 := by
  have hl : ((A/d : ℕ) : ℝ) ≤ (A : ℝ)/(d : ℝ) := Nat.cast_div_le
  have hu : (A : ℝ) < (d : ℝ)*((A/d : ℕ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ A hd
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hh : (A : ℝ)/(d : ℝ) < ((A/d : ℕ) : ℝ)+1 :=
    (div_lt_iff₀ hdR).mpr (by nlinarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

lemma lemma32_actual_burgess_unit_count_error {D : ℕ} (hD : 0 < D) (A : ℕ) :
    |((lemma32BurgessUnitMultipliers D A).card : ℝ)-
      (A : ℝ)*(∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ))| ≤
      (D.divisors.card : ℝ) := by
  rw [lemma32_actual_burgess_unit_multiplier_count hD]
  have he : (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ)*(A/d : ℕ))-
      (A : ℝ)*(∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) =
      ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ)*
        (((A/d : ℕ) : ℝ)-(A : ℝ)/(d : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ D.divisors, |(ArithmeticFunction.moebius d : ℝ)*
        (((A/d : ℕ) : ℝ)-(A : ℝ)/(d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ D.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hD
      rw [abs_mul]
      exact (mul_le_mul hm (lemma32_real_nat_division_error A hdpos)
        (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    _ = _ := by simp

end ZhangLS.Spec
