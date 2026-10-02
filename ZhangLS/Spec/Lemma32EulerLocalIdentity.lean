import ZhangLS.Spec.Lemma32WeightedEuler
import ZhangLS.Spec.Lemma32AnalyticCorrection
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_prime_monomial_eq_cpow {p : ℕ} (hp : 0 < p) (s : ℂ) :
    lemma32PrimeMonomial p s = (p : ℂ)^(-s) := by
  have hr : 0 < (p : ℝ) := by exact_mod_cast hp
  unfold lemma32PrimeMonomial
  change Complex.exp (-s*(Real.log (p : ℝ) : ℂ)) = ((p : ℝ) : ℂ)^(-s)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le]
  congr 1
  ring

lemma lemma32_weighted_prime_power_term {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : 0 < p) (s : ℂ) (e : ℕ) :
    LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s (p^e) =
      (lemma32ActualCoefficient χ (p^e) : ℂ)*lemma32PrimeMonomial p s^e := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero e hp.ne'),Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p e s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s]

lemma lemma32_weighted_local_correction_identity {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (s : ℂ) :
    (1-lemma32PrimeMonomial p s)^8*
      (1-χ.chi (p : ZMod D)*lemma32PrimeMonomial p s)^8*
      (∑' e : ℕ, LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s (p^e)) =
      lemma32LocalCorrection χ p (lemma32PrimeMonomial p s) := by
  unfold lemma32LocalCorrection
  congr 1
  apply tsum_congr
  intro e
  exact lemma32_weighted_prime_power_term χ hp.pos s e

end ZhangLS.Spec
