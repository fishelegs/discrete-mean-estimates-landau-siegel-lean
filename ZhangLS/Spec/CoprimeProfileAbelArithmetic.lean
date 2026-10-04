import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-! Actual coprime totient weights; positive inclusive integer cutoffs. -/
set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open Finset
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 1000000

noncomputable def coefficient (D n : ℕ) : ℝ :=
  if n.Coprime D then (n.totient : ℝ) / (n : ℝ) else 0

noncomputable def summatory (D : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, coefficient D n

noncomputable def density (D : ℕ) : ℝ := (D.totient : ℝ) / (D : ℝ)

noncomputable def unitCount (D N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if n.Coprime D then (1 : ℝ) else 0

lemma coefficient_zero (D : ℕ) : coefficient D 0 = 0 := by simp [coefficient]

lemma coefficient_nonneg (D n : ℕ) : 0 ≤ coefficient D n := by
  unfold coefficient
  split_ifs <;> positivity

lemma coefficient_le_one (D n : ℕ) : coefficient D n ≤ 1 := by
  unfold coefficient
  split_ifs
  · by_cases hn : n = 0
    · simp [hn]
    · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
        (Nat.cast_le.mpr (Nat.totient_le n))
  · norm_num

lemma summatory_one (D : ℕ) : summatory D 1 = 1 := by
  simp [summatory, coefficient]

lemma mobius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  have hi : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then (1 : ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
    rfl
  exact_mod_cast hi

lemma coprime_indicator {D : ℕ} (hD : 0 < D) (n : ℕ) :
    (if n.Coprime D then (1 : ℝ) else 0) =
      ∑ d ∈ D.divisors, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have hg : D.gcd n ≠ 0 := (Nat.gcd_pos_of_pos_left n hD).ne'
  have he : D.divisors.filter (fun d => d ∣ n) = (D.gcd n).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hD.ne', hg]
  rw [← Finset.sum_filter, he, mobius_divisor_sum]
  simp only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]

lemma unitCount_mobius {D : ℕ} (hD : 0 < D) (N : ℕ) :
    unitCount D N =
      ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) * (N / d : ℕ) := by
  unfold unitCount
  simp_rw [coprime_indicator hD]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  ring

lemma totient_mobius (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n : ℕ => (n.totient : ℝ)) (g := fun n : ℕ => (n : ℝ))).mp
    (fun k _ => by exact_mod_cast Nat.sum_totient k) n hn
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ))] at h
  exact h.symm

lemma totient_ratio_mobius {n : ℕ} (hn : 0 < n) :
    (n.totient : ℝ) / (n : ℝ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  rw [totient_mobius n hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.mem_divisors.mp hd).1]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

lemma mobius_density {D : ℕ} (hD : 0 < D) :
    (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) = density D :=
  (totient_ratio_mobius hD).symm

lemma nat_division_error (N : ℕ) {d : ℕ} (hd : 0 < d) :
    |(N / d : ℕ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
  have hl : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hu : (N : ℝ) < (d : ℝ) * ((N / d : ℕ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hd
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hh : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (by nlinarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

lemma unitCount_error {D : ℕ} (hD : 0 < D) (N : ℕ) :
    |unitCount D N - (N : ℝ) * density D| ≤ (D.divisors.card : ℝ) := by
  rw [unitCount_mobius hD, ← mobius_density hD]
  have he : (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) * (N / d : ℕ)) -
      (N : ℝ) * (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ D.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ D.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hD
      rw [abs_mul]
      exact (mul_le_mul hm (nat_division_error N hdpos) (abs_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by simp

noncomputable def mobiusWeight (D : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime D then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) else 0,
    by simp⟩

noncomputable def unitWeight (D : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else if n.Coprime D then 1 else 0, by simp⟩

lemma unitWeight_positive (D : ℕ) {n : ℕ} (hn : 0 < n) :
    unitWeight D n = if n.Coprime D then 1 else 0 := by
  simp [unitWeight, hn.ne']

lemma totient_convolution (D n : ℕ) :
    (mobiusWeight D * unitWeight D) n = coefficient D n := by
  by_cases hn : n = 0
  · simp [hn, coefficient_zero]
  rw [ArithmeticFunction.mul_apply]
  have he : (∑ x ∈ n.divisorsAntidiagonal,
      mobiusWeight D x.1 * unitWeight D x.2) =
      if n.Coprime D then
        ∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℝ) / (x.1 : ℝ) else 0 := by
    by_cases hc : n.Coprime D
    · rw [if_pos hc]
      apply Finset.sum_congr rfl
      intro x hx
      have hxmul := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hx2 : x.2 ≠ 0 := by
        intro h0
        simp [h0] at hxmul
        exact hn hxmul.symm
      have hc12 : x.1.Coprime D ∧ x.2.Coprime D := by
        rw [← Nat.coprime_mul_iff_left, hxmul]
        exact hc
      rw [unitWeight_positive D (Nat.pos_of_ne_zero hx2)]
      change (if x.1.Coprime D then (ArithmeticFunction.moebius x.1 : ℝ) / (x.1 : ℝ) else 0) *
        (if x.2.Coprime D then 1 else 0) = _
      rw [if_pos hc12.1, if_pos hc12.2, mul_one]
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro x hx
      have hxmul := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hx2 : x.2 ≠ 0 := by
        intro h0
        simp [h0] at hxmul
        exact hn hxmul.symm
      have hc12 : ¬ (x.1.Coprime D ∧ x.2.Coprime D) := by
        rw [← Nat.coprime_mul_iff_left, hxmul]
        exact hc
      by_cases h1 : x.1.Coprime D <;> by_cases h2 : x.2.Coprime D <;>
        simp_all [mobiusWeight, unitWeight]
  rw [he, coefficient]
  split_ifs
  · rw [Nat.sum_divisorsAntidiagonal (fun a _ => (ArithmeticFunction.moebius a : ℝ) / (a : ℝ))]
    exact (totient_ratio_mobius (Nat.pos_of_ne_zero hn)).symm
  · rfl

lemma summatory_integer_mobius (D N : ℕ) :
    summatory D (N : ℝ) =
      ∑ d ∈ Ioc 0 N, mobiusWeight D d * unitCount D (N / d) := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (mobiusWeight D) (unitWeight D) N
  simp_rw [totient_convolution] at h
  have hg (M : ℕ) : (∑ m ∈ Ioc 0 M, unitWeight D m) = unitCount D M := by
    unfold unitCount
    apply Finset.sum_congr rfl
    intro m hm
    exact unitWeight_positive D (Finset.mem_Ioc.mp hm).1
  simp_rw [hg] at h
  have hi : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  simpa only [summatory, Nat.floor_natCast, hi] using h

end ZhangLS.Spec.CoprimeProfileAbel
