import checks.Regression
example :
    (Matrix.det (!![MvPolynomial.X (0 : Fin 1), MvPolynomial.X 0 + 1;
      MvPolynomial.X 0 - 1, MvPolynomial.X 0] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℚ))).degreeOf 0 = 2 := by
  rw [FixedQuadratic.Regression.cancellation_degree]
  norm_num
