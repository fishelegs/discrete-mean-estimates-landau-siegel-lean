import ZhangLS.Spec.RealDirichletCharacter
import Mathlib.Data.Nat.Totient

/-!
# Divisor-character sum used in Zhang's Lemma 5.7

For a real primitive Dirichlet character `χ` modulo `D`, define

  νχ(n) = ∑_{d ∣ n} χ(d).

When `n ∣ D`, every divisor `d > 1` of `n` also divides `D`, hence is not a unit
modulo `D`; a Dirichlet character vanishes on such elements.  Therefore only `d = 1`
contributes and `νχ(n) = 1`.

This replaces the legacy `nu_of_divisor_proved`, which merely assumed that all
non-unit contributions already summed to zero.
-/

namespace ZhangLS.Spec

open scoped BigOperators

namespace RealPrimitiveCharacter

variable {D : ℕ}

/-- A nontrivial divisor of the modulus is not a unit modulo the modulus, hence a
Dirichlet character vanishes on it. -/
theorem evalNat_eq_zero_of_dvd_modulus
    (χ : RealPrimitiveCharacter D) {d : ℕ}
    (hdD : d ∣ D) (hd1 : d ≠ 1) : χ.evalNat d = 0 := by
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    have hD0 : D = 0 := Nat.eq_zero_of_zero_dvd hdD
    exact (Nat.ne_of_gt χ.modulus_pos) hD0
  have hdone : 1 < d := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hd0, hd1⟩
  unfold evalNat
  apply χ.chi.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.not_coprime_of_dvd_of_dvd hdone dvd_rfl hdD

end RealPrimitiveCharacter

/-- The genuine divisor-character convolution coefficient `ν = 1 * χ`. -/
noncomputable def divisorCharacterSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) : ℂ :=
  ∑ d ∈ Nat.divisors n, χ.evalNat d

/-- If `n` divides the modulus, then `νχ(n) = 1`.

The proof is arithmetic: every divisor other than `1` is a non-unit modulo `D`, so
its character value is zero. -/
theorem divisorCharacterSum_eq_one_of_dvd_modulus
    {D n : ℕ} (χ : RealPrimitiveCharacter D) (hnD : n ∣ D) :
    divisorCharacterSum χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    have hD0 : D = 0 := Nat.eq_zero_of_zero_dvd hnD
    exact (Nat.ne_of_gt χ.modulus_pos) hD0
  unfold divisorCharacterSum
  calc
    (∑ d ∈ Nat.divisors n, χ.evalNat d) = χ.evalNat 1 := by
      apply Finset.sum_eq_single 1
      · intro d hddiv hdne
        apply χ.evalNat_eq_zero_of_dvd_modulus
        · exact dvd_trans (Nat.mem_divisors.mp hddiv).1 hnD
        · exact hdne
      · intro hnot
        exact (hnot (Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩)).elim
    _ = 1 := χ.evalNat_one

/-- Real-valued form of the same coefficient, convenient for the inequalities in
Lemma 5.7. -/
noncomputable def divisorCharacterSumReal {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) : ℝ :=
  (divisorCharacterSum χ n).re

@[simp] theorem divisorCharacterSumReal_eq_one_of_dvd_modulus
    {D n : ℕ} (χ : RealPrimitiveCharacter D) (hnD : n ∣ D) :
    divisorCharacterSumReal χ n = 1 := by
  simp [divisorCharacterSumReal, divisorCharacterSum_eq_one_of_dvd_modulus χ hnD]

end ZhangLS.Spec
