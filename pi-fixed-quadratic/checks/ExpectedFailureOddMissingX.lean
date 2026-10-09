import FixedQuadratic.Parity
open Polynomial
example : (X : Polynomial GaussianInt) = (1 : Polynomial GaussianInt).comp (X^2) := by
  have h : (X : Polynomial GaussianInt).coeff 1 = ((1 : Polynomial GaussianInt).comp (X^2)).coeff 1 := by assumption
  norm_num at h
