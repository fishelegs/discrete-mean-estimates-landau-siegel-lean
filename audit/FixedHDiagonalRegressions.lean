import ZhangLS.Spec.FixedHDiagonal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
namespace ZhangLS.Spec.FixedHDiagonal.Regression
open ZhangLS.Spec.FixedHDiagonal MeasureTheory Complex

/-- All three cyclic indices, at both ends of the finite perturbation range. -/
example (j : Fin 3) :
    (let q : Fin 3 → ℝ := fun k => if k = 0 then 1 else if k = 1 then 2 else 3
     q j * (q (j+1)+q (j+2)) + q (j+1)*q (j+2)) = 11 := by
  simpa using cyclic_coefficient 0 j

example (j : Fin 3) :
    (let q : Fin 3 → ℝ := fun k => if k = 0 then 1-5*(1/10 : ℝ) else
      if k = 1 then 2*(1+(1/10 : ℝ)) else 3*(1-(1/10 : ℝ))
     q j * (q (j+1)+q (j+2)) + q (j+1)*q (j+2)) = 839/100 := by
  convert cyclic_coefficient (1/10) j using 1
  norm_num

/-- Zero-length endpoints retain the exact literal F/G signs. -/
example (D : ℕ) (c : ℝ) (j : Fin 3) (f f' : ℝ → ℝ) (a : ℝ) :
    (∫ x in a..a, (F D c j f f' x * G D c j f f' a x).re) =
      (∫ x in a..a, (f' x)^2) +
      Real.pi^2 * (11-26*delta D c-(delta D c)^2) * (∫ x in a..a, (f x)^2) := by
  simp

/-- The nonzero quadratic profile checks the IBP sign independently of beta algebra. -/
example : (∫ x in (0 : ℝ)..1, (1-2*x)*tail (fun y => y*(1-y)) 1 x) =
    ∫ x in (0 : ℝ)..1, (x*(1-x))^2 := by
  apply integral_deriv_tail (by fun_prop) (by fun_prop)
  · intro x
    convert (hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) using 1
    simp only [Pi.sub_apply, id_eq]
    ring
  · norm_num

/-- Concrete nonzero mass excludes a vacuous zero-profile sign regression. -/
example : (∫ x in (0 : ℝ)..1, (x*(1-x))^2) = (1 : ℝ)/30 := by
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^n) volume 0 1 :=
    (continuous_id.pow n).intervalIntegrable 0 1
  have he : (fun x : ℝ => (x*(1-x))^2) = fun x => x^2-2*x^3+x^4 := by
    funext x; ring
  rw [he, intervalIntegral.integral_add ((hp 2).sub ((hp 3).const_mul 2)) (hp 4),
    intervalIntegral.integral_sub (hp 2) ((hp 3).const_mul 2),
    intervalIntegral.integral_const_mul]
  norm_num [integral_pow]

/-- Published shifts, finite D, arbitrary compact C² f, each literal cyclic index. -/
example {D : ℕ} (hD : 2 ≤ D) (c : ℝ) (j : Fin 3) {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (ha : f a = 0) (hb : f b = 0) :
    (∫ x in a..b, (F D c j f (deriv f) x * G D c j f (deriv f) b x).re) =
      (∫ x in a..b, (deriv f x)^2) +
      Real.pi^2*(11-26*delta D c-(delta D c)^2)*(∫ x in a..b, (f x)^2) := by
  exact paper_diagonal_c2 hD c j hf hs ha hb

end ZhangLS.Spec.FixedHDiagonal.Regression
