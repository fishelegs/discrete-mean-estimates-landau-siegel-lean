import Splice.CharacterArithmetic

/-!
# Finite-prime assembly

These are finite combinatorial inequalities for the actual character and the
actual determinant prime set. Analytic estimates must be supplied by the
separately proved Mertens and harmonic-tail modules.
-/
namespace Splice

open Finset
open scoped BigOperators

variable {D : ℕ}

noncomputable def primeLogMass (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)

noncomputable def splitPrimeMass (D : ℕ) (χ : DirichletCharacter ℂ D) : ℝ :=
  ∑ p ∈ (Nat.primesLE (D ^ 32)).filter (fun p => D ^ 4 < p ∧ χ p = 1),
    Real.log p / (p : ℝ)

noncomputable def harmonicNuInterval (χ : DirichletCharacter ℂ D) (T X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc T X, nu χ n / (n : ℝ)

theorem primeWeight_nonneg (p : ℕ) : 0 ≤ Real.log p / (p : ℝ) :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem goodPrimeMass_eq_nat (D : ℕ) (χ : DirichletCharacter ℂ D) :
    goodPrimeMass D χ =
      ∑ p ∈ (Nat.primesLE (D ^ 32)).filter
        (fun p => 86713344 < p ∧ ¬ p ∣ 2 * D ∧ χ p = -1),
          Real.log p / (p : ℝ) := by
  simp only [goodPrimeMass, ← Nat.cast_pow, Nat.floor_natCast]

theorem prime_above_fourth_admissible (hD : 97 ≤ D) {p : ℕ}
    (hp : p.Prime) (hlarge : D ^ 4 < p) :
    86713344 < p ∧ ¬ p ∣ 2 * D := by
  have hDpow : D ≤ D ^ 4 := Nat.le_self_pow (by norm_num) D
  have hbase : 86713344 < D ^ 4 := by
    have hmono := Nat.pow_le_pow_left hD 4
    norm_num at hmono ⊢
    omega
  refine ⟨hbase.trans hlarge, ?_⟩
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with h2 | hDdiv
  · have hle := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) h2
    omega
  · have hle := Nat.le_of_dvd (by omega : 0 < D) hDdiv
    omega

theorem prime_above_fourth_split_or_inert (hD : 97 ≤ D)
    (χ : DirichletCharacter ℂ D) (hreal : ∀ x : ZMod D, (χ x).im = 0)
    {p : ℕ} (hp : p.Prime) (hlarge : D ^ 4 < p) : χ p = 1 ∨ χ p = -1 := by
  have hnD : ¬ p ∣ D := by
    intro hdiv
    exact (prime_above_fourth_admissible hD hp hlarge).2 (dvd_mul_of_dvd_right hdiv 2)
  have hunit : IsUnit (p : ZMod D) :=
    (ZMod.isUnit_iff_coprime p D).mpr (hp.coprime_iff_not_dvd.mpr hnD)
  have hnonzero : χ p ≠ 0 := MulChar.apply_ne_zero_iff.mpr hunit
  rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr (real_character_sq χ hreal)) p with h | h | h
  · exact (hnonzero h).elim
  · exact Or.inl h
  · exact Or.inr h

theorem prime_mass_decomposition_le (hD : 97 ≤ D)
    (χ : DirichletCharacter ℂ D) (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    primeLogMass (D ^ 32) ≤ primeLogMass (D ^ 4) + splitPrimeMass D χ +
      goodPrimeMass D χ := by
  classical
  have hpow : D ^ 4 ≤ D ^ 32 := Nat.pow_le_pow_right (by omega : 0 < D) (by norm_num)
  have hsmall : (Nat.primesLE (D ^ 32)).filter (fun p => p ≤ D ^ 4) =
      Nat.primesLE (D ^ 4) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hU, hp⟩, hT⟩
      exact ⟨hT, hp⟩
    · rintro ⟨hT, hp⟩
      exact ⟨⟨hT.trans hpow, hp⟩, hT⟩
  rw [goodPrimeMass_eq_nat]
  unfold primeLogMass splitPrimeMass
  rw [← hsmall]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE hp
  have hw := primeWeight_nonneg p
  by_cases hsmallp : p ≤ D ^ 4
  · have hnlarge : ¬ D ^ 4 < p := by omega
    simp only [hsmallp, hnlarge, false_and, ↓reduceIte, add_zero]
    split_ifs <;> linarith
  · have hlarge : D ^ 4 < p := by omega
    obtain ⟨hH, hram⟩ := prime_above_fourth_admissible hD hprime hlarge
    rcases prime_above_fourth_split_or_inert hD χ hreal hprime hlarge with hsplit | hinert
    · have hnot : ¬ χ p = -1 := by rw [hsplit]; norm_num
      simp [hsmallp, hlarge, hsplit, hnot] <;> split_ifs <;> linarith
    · have hnot : ¬ χ p = 1 := by rw [hinert]; norm_num
      simp [hsmallp, hlarge, hinert, hnot, hH, hram] <;> split_ifs <;> linarith

theorem split_prime_mass_le_half_harmonic (hD : 97 ≤ D)
    (χ : DirichletCharacter ℂ D) (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    splitPrimeMass D χ ≤
      Real.log ((D : ℝ) ^ 32) / 2 * harmonicNuInterval χ (D ^ 4) (D ^ 32) := by
  classical
  let S := (Nat.primesLE (D ^ 32)).filter (fun p => D ^ 4 < p ∧ χ p = 1)
  have hlog : 0 ≤ Real.log ((D : ℝ) ^ 32) := by
    exact Real.log_nonneg (one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega)))
  have hsub : S ⊆ Finset.Ioc (D ^ 4) (D ^ 32) := by
    intro p hp
    obtain ⟨hp, hlarge, hsplit⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨hlarge, Nat.le_of_mem_primesLE hp⟩
  calc
    splitPrimeMass D χ ≤ ∑ p ∈ S,
        (Real.log ((D : ℝ) ^ 32) / 2) * (nu χ p / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpprime, hlarge, hsplit⟩ := Finset.mem_filter.mp hp
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Nat.prime_of_mem_primesLE hpprime).pos
      have hplog : Real.log p ≤ Real.log ((D : ℝ) ^ 32) :=
        Real.log_le_log hp0 (by exact_mod_cast Nat.le_of_mem_primesLE hpprime)
      rw [nu_split_prime χ (Nat.prime_of_mem_primesLE hpprime) hsplit]
      calc
        Real.log p / (p : ℝ) ≤ Real.log ((D : ℝ) ^ 32) / (p : ℝ) :=
          div_le_div_of_nonneg_right hplog hp0.le
        _ = Real.log ((D : ℝ) ^ 32) / 2 * (2 / (p : ℝ)) := by ring
    _ = Real.log ((D : ℝ) ^ 32) / 2 * ∑ p ∈ S, nu χ p / (p : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log ((D : ℝ) ^ 32) / 2 * harmonicNuInterval χ (D ^ 4) (D ^ 32) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hlog (by norm_num))
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => div_nonneg (nu_nonneg χ hreal n) (Nat.cast_nonneg n))

/-- Finite assembly only: the analytic inputs are concrete prior estimates,
not an assumption of the desired prime-mass bound. -/
theorem prime_mass_from_mertens_and_harmonic [NeZero D] (hD : 97 ≤ D)
    (χ : DirichletCharacter ℂ D) (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hupper : primeLogMass (D ^ 4) ≤ 4 * Real.log D + 4)
    (hlower : 32 * Real.log D - 4 ≤ primeLogMass (D ^ 32))
    (htail : harmonicNuInterval χ (D ^ 4) (D ^ 32) ≤
      28 * Real.log D * LOne χ + 18 * (D : ℝ) ^ (-(3 / 2 : ℝ))) :
    goodPrimeMass D χ / (32 * Real.log D) ≥
      7 / 8 - 1 / (4 * Real.log D) - 14 * Real.log D * LOne χ -
        9 * (D : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hell : 0 < Real.log D := Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hdet := prime_mass_decomposition_le hD χ hreal
  have hsplit := split_prime_mass_le_half_harmonic hD χ hreal
  rw [Real.log_pow] at hsplit
  have htail' := mul_le_mul_of_nonneg_left htail (show 0 ≤ (32 * Real.log D) / 2 by positivity)
  have hm : 28 * Real.log D - 8 - (32 * Real.log D) / 2 *
      (28 * Real.log D * LOne χ + 18 * (D : ℝ) ^ (-(3 / 2 : ℝ))) ≤ goodPrimeMass D χ := by
    norm_num at hsplit
    linarith
  apply (le_div_iff₀ (by positivity : 0 < 32 * Real.log D)).mpr
  have hne : Real.log D ≠ 0 := ne_of_gt hell
  convert hm using 1 <;> field_simp [hne] <;> ring

end Splice

#print axioms Splice.prime_mass_decomposition_le
#print axioms Splice.split_prime_mass_le_half_harmonic
#print axioms Splice.prime_mass_from_mertens_and_harmonic
