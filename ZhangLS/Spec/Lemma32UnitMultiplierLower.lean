import ZhangLS.Spec.Lemma32CoprimeDensity
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_totient_prime_count_lower (D : ℕ) :
    D ≤ D.totient*2^D.primeFactors.card := by
  have hp : (∏ p ∈ D.primeFactors, p) ≤
      2^D.primeFactors.card*(∏ p ∈ D.primeFactors, (p-1)) := by
    calc
      _ ≤ ∏ p ∈ D.primeFactors, 2*(p-1) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact Nat.zero_le _
        · intro p hp
          have := (Nat.prime_of_mem_primeFactors hp).two_le
          omega
      _ = _ := by rw [Finset.prod_mul_distrib];simp
  calc
    D = (D/(∏ p ∈ D.primeFactors, p))*(∏ p ∈ D.primeFactors, p) :=
      (Nat.div_mul_cancel (Nat.prod_primeFactors_dvd D)).symm
    _ ≤ (D/(∏ p ∈ D.primeFactors, p))*
        (2^D.primeFactors.card*(∏ p ∈ D.primeFactors, (p-1))) := Nat.mul_le_mul_left _ hp
    _ = _ := by rw [Nat.totient_eq_div_primeFactors_mul];ring

lemma lemma32_real_totient_density_lower {D : ℕ} (hD : 0 < D) :
    1/(2 : ℝ)^D.primeFactors.card ≤ (D.totient : ℝ)/(D : ℝ) := by
  have hn : (D : ℝ) ≤ (D.totient : ℝ)*(2 : ℝ)^D.primeFactors.card := by
    exact_mod_cast lemma32_totient_prime_count_lower D
  exact (div_le_div_iff₀ (by positivity) (Nat.cast_pos.mpr hD)).mpr (by simpa using hn)

lemma lemma32_actual_burgess_unit_multiplier_lower {D : ℕ} (hD : 0 < D) (A : ℕ)
    (hlarge : 2*(2 : ℝ)^D.primeFactors.card*(D.divisors.card : ℝ) ≤ (A : ℝ)) :
    (A : ℝ)/(2*(2 : ℝ)^D.primeFactors.card) ≤
      ((lemma32BurgessUnitMultipliers D A).card : ℝ) := by
  have he := (abs_le.mp (lemma32_actual_burgess_unit_density_error hD A)).1
  have hd := mul_le_mul_of_nonneg_left (lemma32_real_totient_density_lower hD)
    (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))
  have hpow : (0 : ℝ) < (2 : ℝ)^D.primeFactors.card := by positivity
  have hτ : (D.divisors.card : ℝ) ≤ (A : ℝ)/(2*(2 : ℝ)^D.primeFactors.card) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hid : (A : ℝ)/(2 : ℝ)^D.primeFactors.card =
      2*((A : ℝ)/(2*(2 : ℝ)^D.primeFactors.card)) := by
    field_simp
  simp only [mul_one_div] at hd
  rw [← mul_div_assoc] at hd
  rw [hid] at hd
  linarith

end ZhangLS.Spec
