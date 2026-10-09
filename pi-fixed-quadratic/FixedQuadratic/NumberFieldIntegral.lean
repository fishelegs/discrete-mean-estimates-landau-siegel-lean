import FixedQuadratic.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

open Polynomial
open scoped NumberField
namespace FixedQuadratic

/-- Integrality is obtained from all finite places of the ambient number field,
without extending a base-field valuation to an algebraic closure. -/
theorem cleared_product_isIntegral {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (g : GaussianInt →+* K) (P : MvPolynomial (Fin m) GaussianInt)
    (a b c : Fin m → ℤ) (x y : Fin m → K) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hprim : ∀ i, Int.gcd (Int.gcd (a i) (b i) : ℤ) (c i) = 1)
    (hf : ∀ i, C (a i : K)*X^2 + C (b i : K)*X + C (c i : K) =
      C (a i : K)*((X - C (x i))*(X - C (y i)))) :
    IsIntegral ℤ ((∏ i, (a i : K)^e i) * MvPolynomial.eval₂ g x P *
      MvPolynomial.eval₂ g y P) := by
  let z := (∏ i, (a i : K)^e i) * MvPolynomial.eval₂ g x P * MvPolynomial.eval₂ g y P
  have hz : z ∈ (algebraMap (𝓞 K) K).range := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K z
    intro v
    have h := cleared_product_nonarch_le_one (v.adicAbv (K := K) (by norm_num : (1 : NNReal) < 2))
      (v.isNonarchimedean_adicAbv (K := K) (by norm_num)) g P a b c x y e he hprim hf
    change ((WithZeroMulInt.toNNReal (by norm_num : (2 : NNReal) ≠ 0)
      (v.valuation K z)) : ℝ) ≤ 1 at h
    simpa only [NNReal.coe_le_one,
      WithZeroMulInt.toNNReal_le_one_iff (by norm_num : (1 : NNReal) < 2)] using h
  obtain ⟨t, ht⟩ := hz
  change IsIntegral ℤ z
  rw [← ht]
  exact NumberField.RingOfIntegers.isIntegral_coe t

/-- A descended cleared product is Gaussian integral. The explicit descent
identity is not an integrality hypothesis; integrality is proved above.
Constructing this descent from the actual quadratic involution remains separate. -/
theorem cleared_product_gaussian_of_descent {G K : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K] {m : ℕ}
    (P : MvPolynomial (Fin m) GaussianInt)
    (a b c : Fin m → ℤ) (x y : Fin m → K) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hprim : ∀ i, Int.gcd (Int.gcd (a i) (b i) : ℤ) (c i) = 1)
    (hf : ∀ i, C (a i : K)*X^2 + C (b i : K)*X + C (c i : K) =
      C (a i : K)*((X - C (x i))*(X - C (y i))))
    (z : G) (hdesc : algebraMap G K z = (∏ i, (a i : K)^e i) *
      MvPolynomial.eval₂ (algebraMap GaussianInt K) x P *
      MvPolynomial.eval₂ (algebraMap GaussianInt K) y P) :
    (∏ i, (a i : K)^e i) * MvPolynomial.eval₂ (algebraMap GaussianInt K) x P *
      MvPolynomial.eval₂ (algebraMap GaussianInt K) y P ∈
        (algebraMap GaussianInt K).range := by
  have hint := cleared_product_isIntegral (algebraMap GaussianInt K) P a b c x y e he hprim hf
  rw [← hdesc] at hint
  have hg : IsIntegral GaussianInt (algebraMap G K z) := hint.tower_top
  have hz : IsIntegral GaussianInt z := isIntegral_algebraMap_iff.mp hg
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hz
  refine ⟨t, ?_⟩
  rw [IsScalarTower.algebraMap_apply GaussianInt G K, ht, hdesc]

end FixedQuadratic
