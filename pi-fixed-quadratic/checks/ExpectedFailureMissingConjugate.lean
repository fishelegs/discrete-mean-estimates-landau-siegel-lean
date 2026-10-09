import FixedQuadratic.Resultant
open Polynomial
example (f P : Polynomial GaussianInt) (a : GaussianInt) (x y : ℂ) (d : ℕ)
    (hP : P.natDegree ≤ d)
    (hf : f.map GaussianInt.toComplex = C (a : ℂ) * ((X-C x)*(X-C y)))
    (ha : a ≠ 0) (hx : (P.map GaussianInt.toComplex).eval x ≠ 0) :
    1 ≤ ‖(a : ℂ)‖^d * ‖(P.map GaussianInt.toComplex).eval x‖ *
      ‖(P.map GaussianInt.toComplex).eval y‖ := by
  exact FixedQuadratic.quadratic_norm_lower f P a x y d hP hf ha hx
