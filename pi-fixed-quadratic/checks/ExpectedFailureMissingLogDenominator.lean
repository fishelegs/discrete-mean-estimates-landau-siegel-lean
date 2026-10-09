import FixedQuadratic.LogClearing

open FixedQuadratic
example :
    formalEntry (fun _ : Fin 1 => 2*Complex.I) (fun _ => truncatedLog 3)
      2 0 (fun _ => 0) (fun _ => 1) ∈
    (MvPolynomial.map GaussianInt.toComplex :
      MvPolynomial (Fin 1) GaussianInt →+* MvPolynomial (Fin 1) ℂ).range := by
  exact formalEntry_truncatedLog_cleared_gaussian
    (fun _ : Fin 1 => 3) 1 2 0 (fun _ => 0) (fun _ => 1)
