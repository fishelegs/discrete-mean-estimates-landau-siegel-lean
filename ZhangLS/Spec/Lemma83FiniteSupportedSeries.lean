import ZhangLS.Spec.Lemma83KappaPrimePower
import ZhangLS.Spec.Lemma83ShiftedTail
/-! Finite Euler sums with arbitrary constant local coefficients.
Unlike the usual multiplicative Euler-product API, no local constant term
is required to be one and no coefficient is divided out. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 200000

noncomputable def lemma83FactoredCoefficient (S : Finset ℕ) (c : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  ∏ p ∈ S, c p (n.factorization p)

lemma lemma83_factored_coefficient_insert (S : Finset ℕ) (c : ℕ → ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) (e : ℕ) (n : Nat.factoredNumbers S) :
    lemma83FactoredCoefficient (insert p S) c (p^e*n.val) =
      c p e * lemma83FactoredCoefficient S c n.val := by
  have hn : n.val ≠ 0 := Nat.ne_zero_of_mem_factoredNumbers n.property
  have hnp : n.val.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff,Nat.support_factorization]
    exact fun h => hpS (Nat.primeFactors_subset_of_mem_factoredNumbers n.property h)
  unfold lemma83FactoredCoefficient
  rw [prod_insert hpS,Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hn,
    hp.factorization_pow]
  simp only [Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,hnp,add_zero]
  congr 1
  apply prod_congr rfl
  intro q hq
  have hqp : q ≠ p := fun h => hpS (h ▸ hq)
  simp [Finsupp.single_apply,hqp,Ne.symm hqp]

/-- Arbitrary finite local tails have an absolutely convergent smooth-number
sum equal to their finite product. The exponent-zero values can vanish. -/
lemma lemma83_finite_supported_series (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (c : ℕ → ℕ → ℂ) (hc : ∀ p ∈ S, Summable (fun e => ‖c p e‖)) :
    Summable (fun n : Nat.factoredNumbers S => ‖lemma83FactoredCoefficient S c n.val‖) ∧
      HasSum (fun n : Nat.factoredNumbers S => lemma83FactoredCoefficient S c n.val)
        (∏ p ∈ S, ∑' e : ℕ, c p e) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Nat.factoredNumbers_empty]
    simp only [lemma83FactoredCoefficient,prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (fun _ => ‖(1:ℂ)‖),
      hasSum_singleton 1 (fun _ : ℕ => (1:ℂ))⟩
  | @insert p S hpS ih =>
    have hp : p.Prime := hS p (mem_insert_self _ _)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hc' : ∀ q ∈ S, Summable (fun e => ‖c q e‖) :=
      fun q hq => hc q (mem_insert_of_mem hq)
    have ih' := ih hS' hc'
    constructor
    · rw [← (Nat.equivProdNatFactoredNumbers hp hpS).summable_iff]
      simp only [Function.comp_def,Nat.equivProdNatFactoredNumbers_apply',
        lemma83_factored_coefficient_insert S c hp hpS,norm_mul]
      exact (hc p (mem_insert_self _ _)).mul_of_nonneg ih'.1
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    · rw [prod_insert hpS,← (Nat.equivProdNatFactoredNumbers hp hpS).hasSum_iff]
      simp only [Function.comp_def,Nat.equivProdNatFactoredNumbers_apply',
        lemma83_factored_coefficient_insert S c hp hpS]
      have hpSum : HasSum (fun e : ℕ => c p e) (∑' e : ℕ, c p e) :=
        (hc p (mem_insert_self _ _)).of_norm.hasSum
      have hmul : Summable (fun v : ℕ × Nat.factoredNumbers S =>
          c p v.1 * lemma83FactoredCoefficient S c v.2.val) :=
        summable_mul_of_summable_norm
          (f := fun e : ℕ => c p e)
          (g := fun n : Nat.factoredNumbers S => lemma83FactoredCoefficient S c n.val)
          (hc p (mem_insert_self _ _)) ih'.1
      apply hpSum.mul ih'.2
      exact hmul

end ZhangLS.Spec
