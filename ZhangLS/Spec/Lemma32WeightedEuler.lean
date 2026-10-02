import ZhangLS.Spec.Lemma32SeriesConvergence
import ZhangLS.Spec.Lemma32LocalSeries
import Mathlib.NumberTheory.EulerProduct.Basic
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_weighted_term_at_one {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s 1 = 1 := by
  simp [LSeries.term,lemma32_actual_coefficient_one]

lemma lemma32_weighted_term_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ)
    (h : m.Coprime n) :
    LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s (m*n) =
      LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s m*
        LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s n := by
  by_cases hm : m = 0
  · subst m; simp
  by_cases hn : n = 0
  · subst n; simp
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,lemma32_actual_coefficient_mul χ h,
    Complex.ofReal_mul,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  exact mul_div_mul_comm _ _ _ _

lemma lemma32_actual_weighted_euler_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s (p.val^e))
      (lemma32WeightedDirichletSeries χ s) := by
  exact EulerProduct.eulerProduct_hasProd (lemma32_weighted_term_at_one χ s)
    (fun {m n} h => lemma32_weighted_term_mul χ s h)
    (lemma32_actual_weighted_norm_terms_summable χ s hs) (LSeries.term_zero _ s)

lemma lemma32_actual_weighted_euler_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, ∑' e : ℕ,
      LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s (p.val^e)) =
      lemma32WeightedDirichletSeries χ s :=
  (lemma32_actual_weighted_euler_hasProd χ s hs).tprod_eq

end ZhangLS.Spec
