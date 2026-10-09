import FixedQuadratic.Resultant
import Mathlib.Algebra.Polynomial.Expand

open Polynomial
namespace FixedQuadratic

/-- Coefficientwise form of the sign substitution. -/
theorem coeff_comp_negX (P : Polynomial GaussianInt) (n : ℕ) :
    (P.comp (-X)).coeff n = (-1 : GaussianInt)^n * P.coeff n := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [add_comp, hP, hQ, mul_add]
  | monomial m a =>
    rw [monomial_comp, neg_pow]
    have he : C a * ((-1 : Polynomial GaussianInt)^m * X^m) =
        C (a * (-1 : GaussianInt)^m) * X^m := by simp; ring
    rw [he, coeff_C_mul, coeff_X_pow, coeff_monomial]
    by_cases h : m = n
    · subst m; simp only [ite_true, mul_one]; ring
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

/-- Sign-even Gaussian polynomials have no odd coefficients. -/
theorem even_coeff_odd_zero (P : Polynomial GaussianInt) (hP : P.comp (-X) = P)
    (n : ℕ) (hn : ¬ 2 ∣ n) : P.coeff n = 0 := by
  have ho : Odd n := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hn)
  have h := congrArg (fun Q : Polynomial GaussianInt => Q.coeff n) hP
  rw [coeff_comp_negX, ho.neg_one_pow, neg_one_mul] at h
  exact CharZero.neg_eq_self_iff.mp h

/-- The factor is explicitly `contract 2 P`, rather than an existential stub. -/
theorem even_factor (P : Polynomial GaussianInt) (hP : P.comp (-X) = P) :
    P = (P.contract 2).comp (X^2) := by
  rw [← expand_eq_comp_X_pow]
  apply Polynomial.ext
  intro n
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ)), coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · exact even_coeff_odd_zero P hP n hn

/-- Sign-odd Gaussian polynomials factor as X times a polynomial in X squared. -/
theorem odd_factor (P : Polynomial GaussianInt) (hP : P.comp (-X) = -P) :
    ∃ Q : Polynomial GaussianInt, P = X * Q.comp (X^2) := by
  have hzero : P.coeff 0 = 0 := by
    have h := congrArg (fun Q : Polynomial GaussianInt => Q.coeff 0) hP
    rw [coeff_comp_negX, coeff_neg, pow_zero, one_mul] at h
    exact CharZero.eq_neg_self_iff.mp h
  have hfac : X * P.divX = P := by simpa [hzero] using X_mul_divX_add P
  have heven : P.divX.comp (-X) = P.divX := by
    apply mul_left_cancel₀ (show (-X : Polynomial GaussianInt) ≠ 0 by simp)
    have h := hP
    rw [← hfac, mul_comp_neg_X, X_comp] at h
    simpa only [neg_mul] using h
  refine ⟨P.divX.contract 2, ?_⟩
  rw [← even_factor P.divX heven]
  exact hfac.symm

/-- A sign-even value at a square root of an integer is a Gaussian integer. -/
theorem even_eval_gaussian (P : Polynomial GaussianInt) (hP : P.comp (-X) = P)
    (α : ℝ) (d : ℕ) (hα : α^2 = (d : ℝ)) :
    (P.map GaussianInt.toComplex).eval (α : ℂ) ∈ GaussianInt.toComplex.range := by
  have hd : (d : ℂ) = GaussianInt.toComplex (d : GaussianInt) := by simp
  have hs : (α : ℂ)^2 = GaussianInt.toComplex (d : GaussianInt) := by
    rw [← hd]; exact_mod_cast hα
  refine ⟨(P.contract 2).eval (d : GaussianInt), ?_⟩
  conv_rhs => rw [even_factor P hP]
  rw [map_comp, eval_comp]
  simp only [Polynomial.map_pow, Polynomial.map_X, eval_pow, eval_X, hs, eval_map_apply]

/-- The odd value is alpha times a Gaussian integer. -/
theorem odd_eval_gaussian_factor (P : Polynomial GaussianInt) (hP : P.comp (-X) = -P)
    (α : ℝ) (d : ℕ) (hα : α^2 = (d : ℝ)) :
    ∃ z : GaussianInt, (P.map GaussianInt.toComplex).eval (α : ℂ) = (α : ℂ)*(z : ℂ) := by
  obtain ⟨Q,hQ⟩ := odd_factor P hP
  have hd : (d : ℂ) = GaussianInt.toComplex (d : GaussianInt) := by simp
  have hs : (α : ℂ)^2 = GaussianInt.toComplex (d : GaussianInt) := by
    rw [← hd]; exact_mod_cast hα
  refine ⟨Q.eval (d : GaussianInt), ?_⟩
  rw [hQ, Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X, map_comp, eval_comp]
  simp only [Polynomial.map_pow, Polynomial.map_X, eval_pow, eval_X, hs, eval_map_apply]

/-- Independent algebraic lemma: sign parity and nonvanishing remove all
conjugate costs at positive square roots of integers. No pi conclusion. -/
theorem parity_eval_norm_one_le (P : Polynomial GaussianInt)
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) (α : ℝ) (d : ℕ)
    (hα : α^2 = (d : ℝ)) (hα1 : 1 ≤ α)
    (hne : (P.map GaussianInt.toComplex).eval (α : ℂ) ≠ 0) :
    1 ≤ ‖(P.map GaussianInt.toComplex).eval (α : ℂ)‖ := by
  rcases hP with heven | hodd
  · obtain ⟨z,hz⟩ := even_eval_gaussian P heven α d hα
    have hzn : z ≠ 0 := by intro h; simp [h] at hz; exact hne hz.symm
    rw [← hz]
    exact gaussian_norm_one_le z hzn
  · obtain ⟨z,hz⟩ := odd_eval_gaussian_factor P hodd α d hα
    have hzn : z ≠ 0 := by intro h; simp [h] at hz; exact hne hz
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hnorm := gaussian_norm_one_le z hzn
    nlinarith

end FixedQuadratic
