import ZhangLS.Spec.Proposition141Support
import ZhangLS.Spec.Proposition141OffDiagonal

/-! # The Section 14 small-conductor sum on the original support

This file combines actual coefficient support with conductor admissibility.
No coprimality or small common-modulus premise is left as an extra assumption
in the supported diagonal prime bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter
open scoped ComplexConjugate

/-- Uniform nonprincipal 5.6 for the exact χconjθ factor in (14.8), for
all supported d,k and all θ of conductor<D³ after both removed branches. -/
theorem proposition141_small_supported_product_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D d k : ℕ} (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ (D*k)) (B : ℝ) (a : ℕ → ℂ),
      D₀ ≤ D → NormalizedAssumptionA χ →
      Proposition141AdmissibleSequence D B a → 0 < d → 0 < k → a (d*k) ≠ 0 →
      θ ≠ 1 → θ ≠ χ.chi.changeLevel (D.dvd_mul_right k) → θ.conductor < D^3 →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖proposition141ProductPrimeSum χ θ τ‖ ≤
          C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨C,hC,N₁,hN₁,hbound⟩ := proposition141_small_actual_product_prime_bound
  obtain ⟨N₂,hN₂,hsupport⟩ := proposition141_uniform_support_modulus_bound
  refine ⟨C,hC,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D d k χ θ B a hDN hA ha hd hk han hθ hne hr τ hτ
  have hD2 : 2 ≤ D := hN₁.trans ((le_max_left N₁ N₂).trans hDN)
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (by omega)⟩
  have hc := (proposition141_mem_indices D k).mp
    (proposition141_nonzero_product_indices ha hd hk han).2
  have hP4 : 0 ≤ lemma61PaperP4 D := (lemma61_P4_pos (by omega : 1<D)).le
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast (by omega : 1≤D)
  have hmono : (D:ℝ) ≤ (D:ℝ)^2 := by nlinarith
  have hNP : ((D*k : ℕ) : ℝ) ≤ lemma23PaperP D := by
    calc
      ((D*k : ℕ) : ℝ) = (D:ℝ)*(k:ℝ) := by norm_cast
      _ ≤ (D:ℝ)*(2*lemma61PaperP4 D) := mul_le_mul_of_nonneg_left hc.2 (Nat.cast_nonneg _)
      _ ≤ 2*(D:ℝ)^2*lemma61PaperP4 D := by nlinarith
      _ ≤ lemma23PaperP D := hsupport D ((le_max_right N₁ N₂).trans hDN)
  exact hbound χ (D.dvd_mul_right k) θ ((le_max_left N₁ N₂).trans hDN)
    hA hNP hθ hne hr τ hτ

/-- The off-diagonal original prime sum, transferred through its actual
primitive inducer. The common modulus is used only for its unit bridge. -/
theorem proposition141_off_diagonal_actual_prime_sum_eq_inducer {D m : ℕ} [NeZero m]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ m)
    (hNP : ((D*m : ℕ) : ℝ) ≤ lemma23PaperP D) (τ : ℝ) :
    proposition141ProductPrimeSum χ θ τ =
      lemma56PrimeSum D (lemma44CharacterTwist χ θ⁻¹).primitiveCharacter τ := by
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp,hpP,_⟩ := (lemma56_mem_paper_primes D p).mp hp
  have hlt : D*m < p := by exact_mod_cast hNP.trans_lt hpP
  have hc : p.Coprime (D*m) := hpp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hlt) (Nat.le_of_dvd
      (Nat.mul_pos (Nat.pos_of_ne_zero χ.modulus_ne_zero) (Nat.pos_of_ne_zero (NeZero.ne m))) hd))
  rw [proposition141_off_diagonal_inducer_eval χ θ p hc]

/-- Off-diagonal version of the actual product prime bound. -/
theorem proposition141_small_actual_off_diagonal_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D m : ℕ} [NeZero m] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ m),
      D₀ ≤ D → NormalizedAssumptionA χ → ((D*m : ℕ) : ℝ) ≤ lemma23PaperP D →
      ¬D ∣ m → θ ≠ 1 → θ.conductor < D^3 →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖proposition141ProductPrimeSum χ θ τ‖ ≤
          C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_small_off_diagonal_inducer_prime_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D m _ χ θ hDN hA hNP hDm hθ hr τ hτ
  rw [proposition141_off_diagonal_actual_prime_sum_eq_inducer χ θ hNP τ]
  exact hbound χ θ hDN hA hDm hθ hr τ hτ

end ZhangLS.Spec
