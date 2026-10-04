import ZhangLS.Spec.CoprimeProfileAbelSummatory
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
namespace ZhangLS.Spec.CoprimeProfileAbel
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma principal_character_nat (D n : ℕ) :
    (1 : DirichletCharacter ℂ D) (n : ZMod D) = if n.Coprime D then 1 else 0 := by
  by_cases h : n.Coprime D
  · rw [if_pos h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n D).mpr h)
  · rw [if_neg h]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using h)

lemma principal_LSeries {D : ℕ} (hD : D ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ D) (n : ZMod D)) s =
      riemannZeta s * ∏ p ∈ D.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  letI : NeZero D := ⟨hD⟩
  have hh := DirichletCharacter.LSeries_changeLevel (show 1 ∣ D from one_dvd D)
    (1 : DirichletCharacter ℂ 1) hs
  have hc (p : ℕ) : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  calc
    _ = LSeries (1 : ℕ → ℂ) s * ∏ p ∈ D.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
      simpa only [DirichletCharacter.changeLevel_one, hc, one_mul] using hh
    _ = _ := by rw [LSeries_one_eq_riemannZeta hs]

lemma mobius_square_summable (D : ℕ) :
    Summable (fun n : ℕ => mobiusWeight D n / (n : ℝ)) := by
  apply Summable.of_norm
  apply (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  calc
    _ ≤ (n : ℝ)⁻¹ / (n : ℝ) :=
      div_le_div_of_nonneg_right (mobiusWeight_abs_le D n) (Nat.cast_nonneg n)
    _ = ((n : ℝ) ^ 2)⁻¹ := by simp [div_eq_mul_inv, pow_two]

lemma coprime_mobius_LSeries_two (D : ℕ) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ D) (n : ZMod D) *
      (ArithmeticFunction.moebius n : ℂ)) 2 =
      ((∑' n : ℕ, mobiusWeight D n / (n : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp [LSeries.term, mobiusWeight]
  · rw [LSeries.term, if_neg hn, principal_character_nat]
    by_cases hc : n.Coprime D
    · rw [if_pos hc, one_mul, Complex.cpow_two]
      change (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ 2 =
        (((if n.Coprime D then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) else 0) / (n : ℝ) : ℝ) : ℂ)
      rw [if_pos hc]
      push_cast
      rw [div_div, pow_two]
    · rw [if_neg hc, zero_mul, zero_div]
      change 0 = (((if n.Coprime D then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) else 0) / (n : ℝ) : ℝ) : ℂ)
      rw [if_neg hc]
      simp

lemma mobius_square_value_equation {D : ℕ} (hD : 0 < D) :
    ((Real.pi ^ 2 / 6) * ∏ p ∈ D.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)) *
      (∑' n : ℕ, mobiusWeight D n / (n : ℝ)) = 1 := by
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ D)
    (s := 2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ D) (n : ZMod D)) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ D) (n : ZMod D) *
      (ArithmeticFunction.moebius n : ℂ)) 2 = 1 at h
  rw [principal_LSeries hD.ne' (by norm_num), coprime_mobius_LSeries_two,
    riemannZeta_two] at h
  simp only [Complex.cpow_neg, Complex.cpow_two] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_tsum] using h

lemma density_prime_product {D : ℕ} (hD : 0 < D) :
    density D = ∏ p ∈ D.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors D)
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
    Rat.cast_one, Rat.cast_inv] at h
  unfold density
  rw [h]
  field_simp

lemma density_euler_factorization {D : ℕ} (hD : 0 < D) :
    density D = (∏ p ∈ D.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)) *
      (∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) := by
  rw [density_prime_product hD, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The actual, absolutely convergent Möbius density has the requested Euler value. -/
lemma total_density_eq_main {D : ℕ} (hD : 0 < D) :
    density D * (∑' n : ℕ, mobiusWeight D n / (n : ℝ)) = mainConstant D := by
  have h := mobius_square_value_equation hD
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have ht : (∏ p ∈ D.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)) *
      (∑' n : ℕ, mobiusWeight D n / (n : ℝ)) = 6 / Real.pi ^ 2 := by
    apply (eq_div_iff hpi).mpr
    nlinarith only [h]
  rw [density_euler_factorization hD, mainConstant]
  calc
    _ = ((∏ p ∈ D.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)) *
        (∑' n : ℕ, mobiusWeight D n / (n : ℝ))) *
        (∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) := by ring
    _ = _ := by rw [ht]

end ZhangLS.Spec.CoprimeProfileAbel
