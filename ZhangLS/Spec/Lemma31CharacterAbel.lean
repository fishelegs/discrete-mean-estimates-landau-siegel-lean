import ZhangLS.Spec.Lemma31WeightedTail
import ZhangLS.Spec.CharacterAbelAnalyticContinuation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
set_option maxHeartbeats 2000000

lemma lemma31_inverse_deriv (t : ℝ) (ht : 0 < t) :
    deriv (fun u : ℝ => (u : ℂ)⁻¹) t = -((t : ℂ)^2)⁻¹ := by
  simpa only [Complex.ofReal_inv,Complex.ofReal_neg,Complex.ofReal_pow] using
    ((hasDerivAt_inv (ne_of_gt ht)).ofReal_comp).deriv

lemma lemma31_eval_sum_zero_to_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, χ.evalNat n) = ∑ n ∈ Finset.Icc 1 N, χ.evalNat n := by
  letI : Fact (1 < D) := ⟨hD⟩
  have hz : χ.evalNat 0 = 0 := by simp [RealPrimitiveCharacter.evalNat,χ.chi.map_zero]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N),Finset.sum_cons,hz,zero_add]
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  simp

lemma lemma31_character_harmonic_abel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * χ.evalNat n) =
      (N : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N, χ.evalNat n) +
        ∫ t : ℝ in Set.Ioc (1 : ℝ) N,
          ((t : ℂ)^2)⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n := by
  letI : Fact (1 < D) := ⟨hD⟩
  have hz : χ.evalNat 0 = 0 := by simp [RealPrimitiveCharacter.evalNat,χ.chi.map_zero]
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) N,
      DifferentiableAt ℝ (fun u : ℝ => (u : ℂ)⁻¹) t := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    simpa only [Complex.ofReal_inv] using
      ((hasDerivAt_inv htne).ofReal_comp).differentiableAt
  have hc : ContinuousOn (fun t : ℝ => -((t : ℂ)^2)⁻¹) (Set.Icc (1 : ℝ) N) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (show t ≠ 0 by linarith [ht.1]))
  have hi : IntegrableOn (deriv (fun u : ℝ => (u : ℂ)⁻¹)) (Set.Icc (1 : ℝ) N) := by
    exact (hc.integrableOn_Icc).congr_fun
      (fun t ht => (lemma31_inverse_deriv t (by linarith [ht.1])).symm) measurableSet_Icc
  have hab := sum_mul_eq_sub_integral_mul₀' (c := χ.evalNat) hz N hd hi
  simp only [Complex.ofReal_natCast] at hab
  have hsum : (∑ n ∈ Finset.Icc 0 N, (n : ℂ)⁻¹ * χ.evalNat n) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * χ.evalNat n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N),Finset.sum_cons,hz,mul_zero,zero_add]
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    simp
  rw [hsum,lemma31_eval_sum_zero_to_one χ hD] at hab
  have hint : (∫ t : ℝ in Set.Ioc (1 : ℝ) N,
      deriv (fun u : ℝ => (u : ℂ)⁻¹) t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, χ.evalNat n) =
      -(∫ t : ℝ in Set.Ioc (1 : ℝ) N,
        ((t : ℂ)^2)⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [lemma31_inverse_deriv t (by linarith [ht.1]),
      lemma31_eval_sum_zero_to_one χ hD]
    ring
  rw [hint,sub_neg_eq_add] at hab
  exact hab

end ZhangLS.Spec
