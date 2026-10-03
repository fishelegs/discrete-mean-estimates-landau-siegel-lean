import ZhangLS.Spec.Proposition71NonprincipalDivisorBound
import ZhangLS.Spec.DivisorConductorSum

/-! Finite original support and exact divisor reindexing attach the true
nonprincipal source majorant to the already proved full RHS of (7.13). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 3500000

lemma proposition71_indices_subset_prime_floor (D : ℕ) :
    lemma81PolynomialIndices D⊆Icc 1 ⌊lemma23PaperP D⌋₊ := by
  intro n hn
  have hh := (proposition71_mem_indices D n).mp hn
  exact mem_Icc.mpr ⟨hh.1,Nat.le_floor (hh.2.le.trans (proposition71_cutoff_le_P D))⟩

/-- The literal finite d,k,r|k sum is bounded by the full actual positive
conductor sum. No mass, conductor or arithmetic factor is discarded. -/
theorem proposition71_divisor_aggregate_le_original (D : ℕ) (c : ℝ) (a : ℕ → ℂ) :
    (∑d∈lemma81PolynomialIndices D,∑k∈lemma81PolynomialIndices D,
      proposition71DivisorConductorBlock D d k c a)≤
      proposition71OriginalConductorAggregate D c a := by
  let X := ⌊lemma23PaperP D⌋₊
  let F := fun d h r : ℕ => if d*h*r∈lemma81PolynomialIndices D then
    ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
      ∑θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖proposition71OriginalSigmaSeries D c a h d θ‖ else 0
  have hF (d h r : ℕ) : 0≤F d h r := by dsimp [F]; split_ifs <;> positivity
  have hsrc (d k : ℕ) : proposition71DivisorConductorBlock D d k c a=
      ∑r∈k.divisors, if 1<r then F d (k/r) r else 0 := by
    unfold proposition71DivisorConductorBlock
    by_cases hd : d*k∈lemma81PolynomialIndices D
    · rw [if_pos hd]
      apply sum_congr rfl
      intro r hr
      have hmul := Nat.div_mul_cancel (Nat.mem_divisors.mp hr).1
      dsimp [F]
      simp only [Nat.mul_assoc,hmul,if_pos hd]
    · rw [if_neg hd]
      symm
      apply sum_eq_zero
      intro r hr
      have hmul := Nat.div_mul_cancel (Nat.mem_divisors.mp hr).1
      dsimp [F]
      simp only [Nat.mul_assoc,hmul,if_neg hd,ite_self]
  have houter : (∑d∈lemma81PolynomialIndices D,∑k∈lemma81PolynomialIndices D,
      proposition71DivisorConductorBlock D d k c a)≤
      ∑d∈Icc 1 X,∑k∈Icc 1 X,proposition71DivisorConductorBlock D d k c a := by
    apply le_trans ?_ (sum_le_sum_of_subset_of_nonneg (proposition71_indices_subset_prime_floor D)
      (fun d hd hnot => sum_nonneg (fun k hk => proposition71_divisor_conductor_block_nonneg D d k c a)))
    apply sum_le_sum
    intro d hd
    exact sum_le_sum_of_subset_of_nonneg (proposition71_indices_subset_prime_floor D)
      (fun k hk hnot => proposition71_divisor_conductor_block_nonneg D d k c a)
  apply houter.trans
  calc
    _≤∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈Icc 2 X,F d h r := by
      apply sum_le_sum
      intro d hd
      simp_rw [hsrc]
      exact divisorConductor_sum_le X (F d) (hF d)
    _=proposition71OriginalConductorAggregate D c a := by
      unfold proposition71OriginalConductorAggregate proposition71ActualConductorAggregate
        proposition71ConductorNormAggregate
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro h hh
      apply sum_congr rfl
      intro r hr
      have hdp : 0<d := (mem_Icc.mp hd).1
      have hhp : 0<h := (mem_Icc.mp hh).1
      have hrp : 0<r := by have := (mem_Icc.mp hr).1; omega
      have hprod : 0<d*h*r := Nat.mul_pos (Nat.mul_pos hdp hhp) hrp
      dsimp [F]
      simp only [proposition71_mem_indices,hprod,true_and,proposition71OriginalSigmaSeries]

/-- The printed (7.13) inequality for the actual nonprincipal prime mean,
with exactly the fixed a2 coefficient bound as outer constant. -/
theorem proposition71_original_seven_thirteen {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {B₁ B₂ : ℝ} (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (ha₂ : ∀n, ‖a₂ n‖≤B₂) :
    ‖∑p∈lemma56PaperPrimes D,(p : ℂ)^lemma52PaperBetaThree D c*
      proposition71PrimeNonprincipalMean D p c a₁ a₂‖≤
      B₂*proposition71OriginalConductorAggregate D c a₁ := by
  rw [proposition71_weighted_nonprincipal_source_exchange]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑d∈lemma81PolynomialIndices D,∑k∈lemma81PolynomialIndices D,
        B₂*proposition71DivisorConductorBlock D d k c a₁ := by
      apply sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      exact sum_le_sum (fun k hk => proposition71_nonprincipal_source_block_bound hD hL hB₁ hB₂ c a₁ a₂ ha₁ ha₂)
    _=B₂*(∑d∈lemma81PolynomialIndices D,∑k∈lemma81PolynomialIndices D,
        proposition71DivisorConductorBlock D d k c a₁) := by simp only [mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_divisor_aggregate_le_original D c a₁) hB₂

end ZhangLS.Spec
