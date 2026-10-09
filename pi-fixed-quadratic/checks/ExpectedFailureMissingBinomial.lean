import checks.Regression

-- Dropping binom(2,1) loses a genuine coefficient factor in formula (3.1).
example : FixedQuadratic.formalEntry (fun _ : Fin 1 => 2*Complex.I) (fun _ => 0)
    0 0 (fun _ => 1) (fun _ => 2) =
      MvPolynomial.C (2*Complex.I)*MvPolynomial.X 0 := by
  exact FixedQuadratic.Regression.formal_entry_linear
