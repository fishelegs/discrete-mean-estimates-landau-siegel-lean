import FixedQuadratic.NumberFieldIntegral
import FixedQuadratic.Conjugation
import FixedQuadratic.Resultant
import Mathlib.RingTheory.Norm.Transitivity

open Polynomial
namespace FixedQuadratic

theorem quadratic_norm_identity {G K : Type*} [Field G] [Field K]
    [Algebra G K] [FiniteDimensional G K] [IsGalois G K]
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1) (q : K) :
    algebraMap G K (Algebra.norm G q) = q * τ q := by
  classical
  have hc : Fintype.card (K ≃ₐ[G] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegree]
  have hu : (Finset.univ : Finset (K ≃ₐ[G] K)) = {1, τ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hc, Finset.card_pair hτ.symm]
  rw [Algebra.norm_eq_prod_automorphisms, hu]
  simp [hτ.symm]

/-- A proved descent identity for the exact same-field two-embedding product. -/
theorem quadratic_cleared_product_descent {G K : Type*} [Field G] [Field K]
    [Algebra GaussianInt G] [Algebra G K] [Algebra GaussianInt K]
    [IsScalarTower GaussianInt G K] [FiniteDimensional G K] [IsGalois G K] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (P : MvPolynomial (Fin m) GaussianInt) (a : Fin m → ℤ)
    (x : Fin m → K) (e : Fin m → ℕ) :
    algebraMap G K ((∏ i, (a i : G)^e i) *
      Algebra.norm G (MvPolynomial.eval₂ (algebraMap GaussianInt K) x P)) =
      (∏ i, (a i : K)^e i) * MvPolynomial.eval₂ (algebraMap GaussianInt K) x P *
        MvPolynomial.eval₂ (algebraMap GaussianInt K) (fun i => τ (x i)) P := by
  have hfix : τ.toRingEquiv.toRingHom.comp (algebraMap GaussianInt K) =
      algebraMap GaussianInt K := by
    apply RingHom.ext
    intro z
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply GaussianInt G K]
    exact τ.commutes _
  have he := simultaneous_conjugate_evaluation P (algebraMap GaussianInt K)
    τ.toRingEquiv x hfix
  change τ (MvPolynomial.eval₂ (algebraMap GaussianInt K) x P) =
    MvPolynomial.eval₂ (algebraMap GaussianInt K) (fun i => τ (x i)) P at he
  rw [map_mul, map_prod]
  simp only [map_pow, map_intCast]
  rw [quadratic_norm_identity hdegree τ hτ, he]
  ring

/-- Exact multivariate Gaussian integrality in a degree-two Galois field over
the fraction field of Z[i]. No integrality or descent conclusion is assumed. -/
theorem quadratic_cleared_product_gaussian {G K : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (P : MvPolynomial (Fin m) GaussianInt)
    (a b c : Fin m → ℤ) (x : Fin m → K) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hprim : ∀ i, Int.gcd (Int.gcd (a i) (b i) : ℤ) (c i) = 1)
    (hf : ∀ i, C (a i : K)*X^2 + C (b i : K)*X + C (c i : K) =
      C (a i : K)*((X - C (x i))*(X - C (τ (x i))))) :
    (∏ i, (a i : K)^e i) * MvPolynomial.eval₂ (algebraMap GaussianInt K) x P *
      MvPolynomial.eval₂ (algebraMap GaussianInt K) (fun i => τ (x i)) P ∈
        (algebraMap GaussianInt K).range := by
  exact cleared_product_gaussian_of_descent P a b c x (fun i => τ (x i)) e he hprim hf
    _ (quadratic_cleared_product_descent hdegree τ hτ P a x e)

/-- Nonzero Gaussian norm yields the exact two-embedding arithmetic lower
bound. Only one simultaneous conjugate occurs, independently of m. -/
theorem quadratic_cleared_norm_one_le {G K : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (P : MvPolynomial (Fin m) GaussianInt)
    (a b c : Fin m → ℤ) (x : Fin m → K) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hprim : ∀ i, Int.gcd (Int.gcd (a i) (b i) : ℤ) (c i) = 1)
    (hf : ∀ i, C (a i : K)*X^2 + C (b i : K)*X + C (c i : K) =
      C (a i : K)*((X - C (x i))*(X - C (τ (x i)))))
    (ha : ∀ i, a i ≠ 0)
    (hx : MvPolynomial.eval₂ (algebraMap GaussianInt K) x P ≠ 0)
    (φ : K →+* ℂ) (hφ : φ.comp (algebraMap GaussianInt K) = GaussianInt.toComplex) :
    1 ≤ (∏ i, ‖φ (a i : K)‖^e i) *
      ‖φ (MvPolynomial.eval₂ (algebraMap GaussianInt K) x P)‖ *
      ‖φ (MvPolynomial.eval₂ (algebraMap GaussianInt K) (fun i => τ (x i)) P)‖ := by
  classical
  obtain ⟨z, hz⟩ := quadratic_cleared_product_gaussian hdegree τ hτ P a b c x e he hprim hf
  have hy : MvPolynomial.eval₂ (algebraMap GaussianInt K) (fun i => τ (x i)) P ≠ 0 := by
    apply simultaneous_conjugate_ne_zero P (algebraMap GaussianInt K) τ.toRingEquiv x _ hx
    apply RingHom.ext
    intro t
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply GaussianInt G K]
    exact τ.commutes _
  have hn : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    have haK : ∀ i, (a i : K) ≠ 0 := fun i => by exact_mod_cast ha i
    have hp : (∏ i, (a i : K)^e i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (haK i))
    exact (mul_ne_zero (mul_ne_zero hp hx) hy) hz.symm
  have hnorm := gaussian_norm_one_le z hn
  have hc : φ ((algebraMap GaussianInt K) z) = (z : ℂ) :=
    congrArg (fun f : GaussianInt →+* ℂ => f z) hφ
  rw [← hc, hz] at hnorm
  simpa only [map_mul, map_prod, map_pow, norm_mul, norm_prod, norm_pow] using hnorm

end FixedQuadratic
