import ZhangLS.Spec.Lemma151Definitions
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma151_character_square {D n : ℕ} (χ : RealPrimitiveCharacter D)
    (hn : n.Coprime D) : χ.evalNat n ^ 2 = 1 := by
  unfold RealPrimitiveCharacter.evalNat
  rw [← χ.chi.pow_apply' (by decide : (2 : ℕ) ≠ 0), χ.quadratic,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime n D).mpr hn)]

/-- The extra χ disappears only after changing from χψ to ψ coefficients. -/
theorem lemma151_psi_basis_character_cancellation {D n : ℕ}
    (χ : RealPrimitiveCharacter D) (n₁ : ℕ) (hn : n.Coprime D) :
    lemma151BPsi χ (n₁*n) * χ.evalNat n = χ.evalNat n₁ * lemma151BChiPsi D (n₁*n) := by
  unfold lemma151BPsi
  have hm : χ.evalNat (n₁*n) = χ.evalNat n₁ * χ.evalNat n := by
    simp [RealPrimitiveCharacter.evalNat, Nat.cast_mul, map_mul]
  rw [hm]
  calc
    _ = χ.evalNat n₁ * lemma151BChiPsi D (n₁*n) * χ.evalNat n^2 := by ring
    _ = _ := by rw [lemma151_character_square χ hn, mul_one]

lemma lemma151_prime_dvd_Q {D q : ℕ} (hq : q.Prime) (hsmall : q < D^4) :
    q ∣ lemma151Q D := by
  unfold lemma151Q
  exact Finset.dvd_prod_of_mem (fun n => n) (by simp [hq, hsmall])

/-- The original Q removes every ramified prime; D need not be squarefree. -/
theorem lemma151_rough_coprime_modulus {D n : ℕ} (hD : 1 < D)
    (hn : n.Coprime (lemma151Q D)) : n.Coprime D := by
  apply Nat.coprime_of_dvd'
  intro q hq hqn hqD
  have hqle : q ≤ D := Nat.le_of_dvd (by omega) hqD
  have hDpow : D < D^4 := by
    have h1 : D < D*D := by nlinarith
    have h2 : D*D ≤ D^4 := by nlinarith [sq_nonneg (D*D-D)]
    exact h1.trans_le h2
  have hqQ := lemma151_prime_dvd_Q hq (hqle.trans_lt hDpow)
  exact (Nat.eq_one_of_dvd_coprimes hn hqn hqQ).symm ▸ dvd_refl 1

/-- Cancellation on the literal domain required by Lemma 15.1. -/
theorem lemma151_psi_basis_rough_cancellation {D n : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) (n₁ : ℕ)
    (hn : n.Coprime (lemma151Q D)) :
    lemma151BPsi χ (n₁*n) * χ.evalNat n = χ.evalNat n₁ * lemma151BChiPsi D (n₁*n) :=
  lemma151_psi_basis_character_cancellation χ n₁ (lemma151_rough_coprime_modulus hD hn)

end ZhangLS.Spec
