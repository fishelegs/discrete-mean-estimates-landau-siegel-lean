import ZhangLS.Spec.Lemma32RepeatedRootCorrelation
import ZhangLS.Spec.Lemma32QuarticPairingClassification
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_actual_prime_repeated_correlation_norm {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) (a b c : ZMod p) (hbc : b ≠ c) :
    ‖∑ x : ZMod p, χ.chi ((x+a)^2*(x+b)*(x+c))‖ ≤ 2 :=
  lemma32_quadratic_repeated_root_correlation_norm χ.chi
    (χ.nontrivial_of_one_lt_modulus (Fact.out : p.Prime).one_lt) χ.quadratic a b c hbc

lemma lemma32_actual_prime_quartic_repeated_correlation {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (v : Fin 4 → Fin H)
    (h01 : ((v 0).val : ZMod p)=((v 1).val : ZMod p))
    (h23 : ((v 2).val : ZMod p) ≠ ((v 3).val : ZMod p)) :
    |lemma32QuarticCorrelation χ v| ≤ 2 := by
  have he : lemma32QuarticCorrelation χ v =
      (∑ x : ZMod p, χ.chi ((x+((v 0).val : ZMod p))^2*
        (x+((v 2).val : ZMod p))*(x+((v 3).val : ZMod p)))).re := by
    unfold lemma32QuarticCorrelation
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Fin.prod_univ_four,← h01]
    congr 2
    ring
  rw [he]
  exact (Complex.abs_re_le_norm _).trans
    (lemma32_actual_prime_repeated_correlation_norm χ _ _ _ h23)

end ZhangLS.Spec
