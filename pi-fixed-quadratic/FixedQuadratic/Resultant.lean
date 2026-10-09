import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

open Polynomial
namespace FixedQuadratic

/-- Exact leading-coefficient exponent for one quadratic center. The factorization
is an explicit hypothesis, not a postulated integrality conclusion. -/
theorem quadratic_resultant_identity (f P : Polynomial GaussianInt)
    (a : GaussianInt) (x y : ℂ) (d : ℕ)
    (hP : P.natDegree ≤ d)
    (hf : f.map GaussianInt.toComplex = C (a : ℂ) * ((X - C x) * (X - C y))) :
    (f.resultant P 2 d : ℂ) = (a : ℂ)^d *
      (P.map GaussianInt.toComplex).eval x * (P.map GaussianInt.toComplex).eval y := by
  rw [← resultant_map_map, hf, resultant_C_mul_left]
  have hd : (P.map GaussianInt.toComplex).natDegree ≤ d := natDegree_map_le.trans hP
  have he := resultant_mul_left (X - C x) (X - C y) (P.map GaussianInt.toComplex) d hd
  simp only [natDegree_X_sub_C] at he
  rw [he, resultant_X_sub_C_left _ _ _ hd, resultant_X_sub_C_left _ _ _ hd]
  ring

/-- In particular the exactly cleared two-root product is Gaussian integral. -/
theorem quadratic_product_gaussian (f P : Polynomial GaussianInt)
    (a : GaussianInt) (x y : ℂ) (d : ℕ) (hP : P.natDegree ≤ d)
    (hf : f.map GaussianInt.toComplex = C (a : ℂ) * ((X - C x) * (X - C y))) :
    (a : ℂ)^d * (P.map GaussianInt.toComplex).eval x *
      (P.map GaussianInt.toComplex).eval y ∈ GaussianInt.toComplex.range := by
  exact ⟨f.resultant P 2 d, quadratic_resultant_identity f P a x y d hP hf⟩

theorem gaussian_norm_one_le (z : GaussianInt) (hz : z ≠ 0) :
    1 ≤ ‖(z : ℂ)‖ := by
  have hi : (1 : ℤ) ≤ z.norm := GaussianInt.norm_pos.mpr hz
  have hr : (1 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at hr
  nlinarith [norm_nonneg (z : ℂ)]

/-- A nonzero exact norm product forces a target lower bound; the conjugate
value and coefficient cost remain visible. -/
theorem quadratic_norm_lower (f P : Polynomial GaussianInt)
    (a : GaussianInt) (x y : ℂ) (d : ℕ) (hP : P.natDegree ≤ d)
    (hf : f.map GaussianInt.toComplex = C (a : ℂ) * ((X - C x) * (X - C y)))
    (ha : a ≠ 0) (hx : (P.map GaussianInt.toComplex).eval x ≠ 0)
    (hy : (P.map GaussianInt.toComplex).eval y ≠ 0) :
    1 ≤ ‖(a : ℂ)‖^d * ‖(P.map GaussianInt.toComplex).eval x‖ *
      ‖(P.map GaussianInt.toComplex).eval y‖ := by
  have he := quadratic_resultant_identity f P a x y d hP hf
  have hn : f.resultant P 2 d ≠ 0 := by
    intro hz
    have hc : (a : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr ha
    rw [hz, GaussianInt.toComplex_zero] at he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero d hc) hx) hy) he.symm
  have h := gaussian_norm_one_le (f.resultant P 2 d) hn
  rwa [he, norm_mul, norm_mul, norm_pow] at h

end FixedQuadratic
