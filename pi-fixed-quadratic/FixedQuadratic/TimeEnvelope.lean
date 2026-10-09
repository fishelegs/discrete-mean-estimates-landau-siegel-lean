import FixedQuadratic.L1Norm
import FixedQuadratic.LogClearing
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Polynomial
namespace FixedQuadratic

/-- Absolute coefficient sum in both time and center variables, weighted by
the time radius. It bounds Cauchy's coefficient estimate without introducing
any dependence on the truncation length. -/
noncomputable def timeCoefficientL1 {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (r : ℝ) : ℝ :=
  ∑ n ∈ P.support, multiCoefficientL1 (P.coeff n) * r^n

theorem timeCoefficientL1_nonneg {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ timeCoefficientL1 P r := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (multiCoefficientL1_nonneg _) (pow_nonneg hr _)

theorem timeCoefficientL1_on_superset {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (r : ℝ) (s : Finset ℕ)
    (hs : P.support ⊆ s) :
    timeCoefficientL1 P r = ∑ n ∈ s, multiCoefficientL1 (P.coeff n)*r^n := by
  classical
  apply Finset.sum_subset hs
  intro n _ hn
  rw [Polynomial.notMem_support_iff.mp hn, multiCoefficientL1_zero, zero_mul]

theorem timeCoefficientL1_zero {m : ℕ} (r : ℝ) :
    timeCoefficientL1 (0 : Polynomial (MvPolynomial (Fin m) ℂ)) r = 0 := by
  simp [timeCoefficientL1]

theorem timeCoefficientL1_add_le {m : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) :
    timeCoefficientL1 (P+Q) r ≤ timeCoefficientL1 P r + timeCoefficientL1 Q r := by
  classical
  rw [timeCoefficientL1_on_superset (P+Q) r (P.support ∪ Q.support) support_add,
    timeCoefficientL1_on_superset P r _ Finset.subset_union_left,
    timeCoefficientL1_on_superset Q r _ Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  rw [coeff_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (multiCoefficientL1_add_le _ _) (pow_nonneg hr _)

theorem timeCoefficientL1_monomial {m : ℕ} (n : ℕ) (A : MvPolynomial (Fin m) ℂ) (r : ℝ) :
    timeCoefficientL1 (Polynomial.monomial n A) r = multiCoefficientL1 A * r^n := by
  classical
  by_cases hA : A = 0
  · simp [hA, timeCoefficientL1_zero, multiCoefficientL1_zero]
  · simp [timeCoefficientL1, support_monomial, hA]

theorem timeCoefficientL1_sum_le {ι : Type*} {m : ℕ} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) :
    timeCoefficientL1 (∑ i ∈ s, P i) r ≤ ∑ i ∈ s, timeCoefficientL1 (P i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [timeCoefficientL1_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (timeCoefficientL1_add_le _ _ hr).trans (add_le_add (le_refl _) ih)

theorem timeCoefficientL1_mul_le {m : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) :
    timeCoefficientL1 (P*Q) r ≤ timeCoefficientL1 P r * timeCoefficientL1 Q r := by
  classical
  have he : P*Q = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      Polynomial.monomial (a+b) (P.coeff a*Q.coeff b) := by
    conv_lhs => rw [← sum_monomial_eq P, ← sum_monomial_eq Q, Polynomial.sum_def,
      Polynomial.sum_def]
    simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
    exact Finset.sum_comm
  rw [he]
  apply (timeCoefficientL1_sum_le _ _ hr).trans
  calc
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
        multiCoefficientL1 (P.coeff a)*multiCoefficientL1 (Q.coeff b)*r^(a+b) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (timeCoefficientL1_sum_le _ _ hr).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [timeCoefficientL1_monomial]
      exact mul_le_mul_of_nonneg_right (multiCoefficientL1_mul_le _ _) (pow_nonneg hr _)
    _ = timeCoefficientL1 P r * timeCoefficientL1 Q r := by
      simp only [timeCoefficientL1, Finset.sum_mul, Finset.mul_sum, pow_add]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

theorem timeCoefficientL1_C {m : ℕ} (A : MvPolynomial (Fin m) ℂ) (r : ℝ) :
    timeCoefficientL1 (Polynomial.C A) r = multiCoefficientL1 A := by
  simpa [Polynomial.monomial_zero_left] using timeCoefficientL1_monomial 0 A r

theorem timeCoefficientL1_one {m : ℕ} (r : ℝ) :
    timeCoefficientL1 (1 : Polynomial (MvPolynomial (Fin m) ℂ)) r = 1 := by
  simpa [multiCoefficientL1_one] using timeCoefficientL1_C (m := m) 1 r

theorem timeCoefficientL1_X {m : ℕ} (r : ℝ) :
    timeCoefficientL1 (Polynomial.X : Polynomial (MvPolynomial (Fin m) ℂ)) r = r := by
  simpa [multiCoefficientL1_one, Polynomial.monomial_one_one_eq_X] using
    timeCoefficientL1_monomial (m := m) 1 1 r

theorem timeCoefficientL1_pow_le {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    timeCoefficientL1 (P^n) r ≤ (timeCoefficientL1 P r)^n := by
  induction n with
  | zero => simp [timeCoefficientL1_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (timeCoefficientL1_mul_le _ _ hr).trans
      (mul_le_mul_of_nonneg_right ih (timeCoefficientL1_nonneg _ hr))

theorem timeCoefficientL1_prod_le {ι : Type*} {m : ℕ} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) :
    timeCoefficientL1 (∏ i ∈ s, P i) r ≤ ∏ i ∈ s, timeCoefficientL1 (P i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [timeCoefficientL1_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (timeCoefficientL1_mul_le _ _ hr).trans
      (mul_le_mul_of_nonneg_left ih (timeCoefficientL1_nonneg _ hr))

theorem time_coefficient_bound {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) {r : ℝ} (hr : 0 ≤ r) (s : ℕ) :
    multiCoefficientL1 (P.coeff s)*r^s ≤ timeCoefficientL1 P r := by
  classical
  by_cases hs : s ∈ P.support
  · exact Finset.single_le_sum (f := fun n => multiCoefficientL1 (P.coeff n)*r^n)
      (fun n _ => mul_nonneg (multiCoefficientL1_nonneg _) (pow_nonneg hr _)) hs
  · rw [notMem_support_iff.mp hs, multiCoefficientL1_zero, zero_mul]
    exact timeCoefficientL1_nonneg P hr

theorem log_coeff_norm_le_one (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.log ℂ)‖ ≤ 1 := by
  rw [PowerSeries.coeff_log]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [ite_eq_right hn, map_div₀, map_pow, map_neg, map_one, map_natCast,
      norm_div, norm_pow, norm_neg, norm_one, one_pow]
    have hc : 1 ≤ ‖(n : ℂ)‖ := by
      simpa using (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hc)).mpr hc

/-- A deliberately coarse uniform bound 2, sufficient for the separated
weight limit. It contains no log of the truncation length. -/
theorem truncatedLog_time_l1_le_two {m : ℕ} (T : ℕ) :
    timeCoefficientL1 ((truncatedLog T).map (MvPolynomial.C : ℂ →+*
      MvPolynomial (Fin m) ℂ)) (1/2) ≤ 2 := by
  classical
  have hs : ((truncatedLog T).map (MvPolynomial.C : ℂ →+*
      MvPolynomial (Fin m) ℂ)).support ⊆ Finset.range T := by
    intro n hn
    rw [Finset.mem_range]
    by_contra h
    have hc := Polynomial.mem_support_iff.mp hn
    simp [Polynomial.coeff_map, truncatedLog, PowerSeries.coeff_trunc, h] at hc
  rw [timeCoefficientL1_on_superset _ _ _ hs]
  apply (Finset.sum_le_sum (fun n hn => ?_)).trans (sum_geometric_two_le T)
  rw [Polynomial.coeff_map, truncatedLog, PowerSeries.coeff_trunc,
    ite_eq_left (Finset.mem_range.mp hn), multiCoefficientL1_C]
  simpa using mul_le_mul_of_nonneg_right (log_coeff_norm_le_one n)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n)

theorem shifted_truncatedLog_time_l1_le {m : ℕ} (T j k : ℕ) (i : Fin m) (hjk : j ≤ k) :
    timeCoefficientL1 (Polynomial.C (MvPolynomial.C (2*(j : ℂ)*Complex.I)*MvPolynomial.X i) +
      (truncatedLog T).map MvPolynomial.C) (1/2) ≤ 2*k+2 := by
  apply (timeCoefficientL1_add_le _ _ (by norm_num)).trans
  rw [timeCoefficientL1_C, MvPolynomial.C_mul_X_eq_monomial, multiCoefficientL1_monomial]
  have hn : ‖2*(j : ℂ)*Complex.I‖ = 2*j := by simp
  rw [hn]
  have ht := truncatedLog_time_l1_le_two (m := m) T
  have hc : (j : ℝ) ≤ k := by exact_mod_cast hjk
  linarith

theorem time_coefficient_half_bound {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (s : ℕ) :
    multiCoefficientL1 (P.coeff s) ≤ 2^s*timeCoefficientL1 P (1/2) := by
  have h := mul_le_mul_of_nonneg_left (time_coefficient_bound P (by norm_num : (0 : ℝ) ≤ 1/2) s)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)
  have he : (2 : ℝ)^s*(1/2)^s = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = (2^s*(1/2)^s)*multiCoefficientL1 (P.coeff s) := by rw [he, one_mul]
    _ = 2^s*(multiCoefficientL1 (P.coeff s)*(1/2)^s) := by ring
    _ ≤ _ := h

/-- Actual truncated-log entry envelope, valid for every truncation T_i,
with a fixed coarse center constant 2k+2 in place of the sharper paper C_k. -/
theorem formalEntry_truncatedLog_l1_le {m : ℕ} (T : Fin m → ℕ)
    (j k s h : ℕ) (b a : Fin m → ℕ) (hjk : j ≤ k) :
    multiCoefficientL1 (formalEntry (fun _ => 2*(j : ℂ)*Complex.I)
      (fun i => truncatedLog (T i)) s h b a) ≤
      (∏ i, ((a i).choose (b i) : ℝ)) * 2^s * (3/2)^h * (2*k+2)^(∑ i, (a i-b i)) := by
  classical
  rw [formalEntry_split]
  apply (multiCoefficientL1_mul_le _ _).trans
  rw [multiCoefficientL1_C]
  have hn : ‖∏ i, ((a i).choose (b i) : ℂ)‖ = ∏ i, ((a i).choose (b i) : ℝ) := by
    simp [norm_prod]
  rw [hn]
  have ht := time_coefficient_half_bound
    (((1+Polynomial.X)^h)*∏ i, (Polynomial.C (MvPolynomial.C
      (2*(j : ℂ)*Complex.I)*MvPolynomial.X i)+(truncatedLog (T i)).map MvPolynomial.C)^(a i-b i)) s
  have hbase : timeCoefficientL1 ((1+Polynomial.X)^h :
      Polynomial (MvPolynomial (Fin m) ℂ)) (1/2) ≤ (3/2)^h := by
    apply (timeCoefficientL1_pow_le _ (by norm_num) _).trans
    apply pow_le_pow_left₀ (timeCoefficientL1_nonneg _ (by norm_num))
    have hh := timeCoefficientL1_add_le (1 : Polynomial (MvPolynomial (Fin m) ℂ))
      Polynomial.X (by norm_num : (0 : ℝ) ≤ 1/2)
    norm_num [timeCoefficientL1_one, timeCoefficientL1_X] at hh ⊢
    exact hh
  have hprod : timeCoefficientL1 (∏ i, (Polynomial.C (MvPolynomial.C
      (2*(j : ℂ)*Complex.I)*MvPolynomial.X i)+(truncatedLog (T i)).map MvPolynomial.C)^(a i-b i))
      (1/2) ≤ (2*k+2)^(∑ i, (a i-b i)) := by
    apply (timeCoefficientL1_prod_le _ _ (by norm_num)).trans
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀
    · intro i hi; exact timeCoefficientL1_nonneg _ (by norm_num)
    · intro i hi
      apply (timeCoefficientL1_pow_le _ (by norm_num) _).trans
      exact pow_le_pow_left₀ (timeCoefficientL1_nonneg _ (by norm_num))
        (shifted_truncatedLog_time_l1_le (T i) j k i hjk) _
  have htime := (timeCoefficientL1_mul_le _ _ (by norm_num)).trans
    (mul_le_mul hbase hprod (timeCoefficientL1_nonneg _ (by norm_num)) (by positivity))
  have hentry := ht.trans (mul_le_mul_of_nonneg_left htime (by positivity))
  have hh := mul_le_mul_of_nonneg_left hentry
    (show 0 ≤ ∏ i, ((a i).choose (b i) : ℝ) by positivity)
  simpa only [mul_assoc] using hh

end FixedQuadratic
