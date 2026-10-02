import ZhangLS.Spec.Lemma32RegularFactors
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32PrimeMonomial (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s*(Real.log (p : ℝ) : ℂ))

lemma lemma32_prime_monomial_norm (p : ℕ) (s : ℂ) :
    ‖lemma32PrimeMonomial p s‖ = Real.exp (-s.re*Real.log (p : ℝ)) := by
  unfold lemma32PrimeMonomial
  rw [norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

lemma lemma32_prime_monomial_norm_square {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖lemma32PrimeMonomial p s‖^2 = (p : ℝ)^(-2*s.re) := by
  rw [lemma32_prime_monomial_norm,pow_two,← Real.exp_add,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr hp)]
  congr 1
  ring

lemma lemma32_prime_monomial_norm_lt_one {p : ℕ} (hp : 1 < p) (s : ℂ) (hs : 0 < s.re) :
    ‖lemma32PrimeMonomial p s‖ < 1 := by
  rw [lemma32_prime_monomial_norm]
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hp)
  have he : -s.re*Real.log (p : ℝ) < 0 := by
    simpa only [neg_mul] using neg_neg_of_pos (mul_pos hs hl)
  simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr he

lemma lemma32_regular_prime_errors_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1/2 < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)-1‖) := by
  have hn : Summable (fun n : ℕ => (n : ℝ)^(-2*s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hp : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-2*s.re)) := hn.subtype _
  apply (hp.mul_left 7659).of_nonneg_of_le
  · intro p
    exact norm_nonneg _
  · intro p
    have hm := lemma32_prime_monomial_norm_lt_one p.property.one_lt s (by linarith)
    have hb := lemma32_regular_local_norm_sub_one χ p.val (lemma32PrimeMonomial p.val s) hm.le
    rw [lemma32_prime_monomial_norm_square p.property.pos] at hb
    exact hb

noncomputable def lemma32RegularEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)

lemma lemma32_regular_euler_product_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1/2 < s.re) :
    Multipliable (fun p : Nat.Primes =>
      lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)) := by
  have h := multipliable_one_add_of_summable (lemma32_regular_prime_errors_summable χ s hs)
  simpa only [add_sub_cancel] using h

end ZhangLS.Spec
