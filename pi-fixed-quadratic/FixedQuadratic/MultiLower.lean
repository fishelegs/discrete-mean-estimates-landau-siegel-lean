import FixedQuadratic.QuadraticNorm
import FixedQuadratic.MultiEnvelope

open scoped BigOperators
open Polynomial
namespace FixedQuadratic

theorem multiCoefficientL1_pos_of_eval_ne_zero {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : MvPolynomial.eval x P ≠ 0) : 0 < multiCoefficientL1 P := by
  have hh := multi_eval_norm_le P x (fun i => P.degreeOf i) (fun _ => le_rfl)
  have hp : 0 < ‖MvPolynomial.eval x P‖ := norm_pos_iff.mpr hx
  exact pos_of_mul_pos_left (lt_of_lt_of_le hp hh) (by positivity)

theorem mapped_degreeOf_le {m : ℕ} (P : MvPolynomial (Fin m) GaussianInt)
    (e : Fin m → ℕ) (he : ∀ i, P.degreeOf i ≤ e i) :
    ∀ i, (MvPolynomial.map GaussianInt.toComplex P).degreeOf i ≤ e i := by
  intro i
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro α hα
  apply MvPolynomial.degreeOf_le_iff.mp (he i) α
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have hh := MvPolynomial.mem_support_iff.mp hα
  rw [MvPolynomial.coeff_map, hz, map_zero] at hh
  exact hh rfl

/-- The multivariate same-field norm/Mahler lower bound, with exactly one
coefficient-l1 cost and one a_i^e_i. Simultaneous conjugate nonvanishing and
Gaussian integrality are proved by the imported norm theorem. -/
theorem quadratic_multi_l1_mahler_lower {G K : Type*} [Field G] [Field K]
    [NumberField K] [Algebra GaussianInt G] [IsFractionRing GaussianInt G]
    [Algebra G K] [Algebra GaussianInt K] [IsScalarTower GaussianInt G K]
    [FiniteDimensional G K] [IsGalois G K] {m : ℕ}
    (hdegree : Module.finrank G K = 2) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1)
    (P : MvPolynomial (Fin m) GaussianInt)
    (a b c : Fin m → ℤ) (x : Fin m → K) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hprim : ∀ i, Int.gcd (Int.gcd (a i) (b i) : ℤ) (c i) = 1)
    (hf : ∀ i, C (a i : K)*X^2+C (b i : K)*X+C (c i : K) =
      C (a i : K)*((X-C (x i))*(X-C (τ (x i)))))
    (ha : ∀ i, a i ≠ 0)
    (hx : MvPolynomial.eval₂ (algebraMap GaussianInt K) x P ≠ 0)
    (φ : K →+* ℂ) (hφ : φ.comp (algebraMap GaussianInt K) = GaussianInt.toComplex) :
    (∏ i, (max 1 ‖φ (x i)‖)^e i) /
      (multiCoefficientL1 (MvPolynomial.map GaussianInt.toComplex P) *
        ∏ i, (‖φ (a i : K)‖ * max 1 ‖φ (x i)‖ * max 1 ‖φ (τ (x i))‖)^e i) ≤
      ‖φ (MvPolynomial.eval₂ (algebraMap GaussianInt K) x P)‖ := by
  classical
  let Q := MvPolynomial.map GaussianInt.toComplex P
  have hEval (v : Fin m → K) : φ (MvPolynomial.eval₂ (algebraMap GaussianInt K) v P) =
      MvPolynomial.eval (fun i => φ (v i)) Q := by
    rw [MvPolynomial.eval₂_comp_left, hφ]
    exact (MvPolynomial.eval_map _ _ _).symm
  have hxC : MvPolynomial.eval (fun i => φ (x i)) Q ≠ 0 := by
    rw [← hEval]
    exact fun hz => hx (φ.injective (by simpa using hz))
  have hB := multiCoefficientL1_pos_of_eval_ne_zero Q _ hxC
  have haC : ∀ i, 0 < ‖φ (a i : K)‖ := by
    intro i
    apply norm_pos_iff.mpr
    apply (_root_.map_ne_zero φ).mpr
    exact_mod_cast ha i
  have hR : ∀ i, 0 < max 1 ‖φ (x i)‖ := fun _ => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hS : ∀ i, 0 < max 1 ‖φ (τ (x i))‖ := fun _ => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn := quadratic_cleared_norm_one_le hdegree τ hτ P a b c x e he hprim hf ha hx φ hφ
  have hy := multi_eval_norm_le Q (fun i => φ (τ (x i))) e (mapped_degreeOf_le P e he)
  rw [← hEval] at hy
  have hh := hn.trans (mul_le_mul_of_nonneg_left hy (by positivity))
  apply (div_le_iff₀ (mul_pos hB (Finset.prod_pos
    (fun i _ => pow_pos (mul_pos (mul_pos (haC i) (hR i)) (hS i)) _)))).mpr
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ ∏ i, (max 1 ‖φ (x i)‖)^e i by positivity)
  simp only [mul_one] at hm
  convert hm using 1
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

end FixedQuadratic
