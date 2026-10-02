import ZhangLS.Spec.Lemma32ActualRepeatedCorrelation
import ZhangLS.Spec.Lemma32FourthMomentRemainder
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_quartic_correlation_permutation {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) {H : ℕ} (v : Fin 4 → Fin H) (σ : Equiv.Perm (Fin 4)) :
    lemma32QuarticCorrelation χ (fun i => v (σ i)) = lemma32QuarticCorrelation χ v := by
  unfold lemma32QuarticCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  congr 2
  exact Fintype.prod_equiv σ _ _ (fun i => rfl)

lemma lemma32_actual_prime_repeated_quartic_permutation_bound {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (v : Fin 4 → Fin H) (σ : Equiv.Perm (Fin 4))
    (h01 : ((v (σ 0)).val : ZMod p)=((v (σ 1)).val : ZMod p))
    (h23 : ((v (σ 2)).val : ZMod p) ≠ ((v (σ 3)).val : ZMod p)) :
    |lemma32QuarticCorrelation χ v| ≤ 2 := by
  rw [← lemma32_quartic_correlation_permutation χ v σ]
  exact lemma32_actual_prime_quartic_repeated_correlation χ (fun i => v (σ i)) h01 h23

end ZhangLS.Spec
