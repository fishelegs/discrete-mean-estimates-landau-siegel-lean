import PiSpecializationRegression

open PiWeightedColon PiWeightedColon.Regression

example : complexHermiteCoefficientMatrix 0 piHermiteParameter (rationalSmallRowMap 3)
    (originalIndexEquiv 0 (rationalSmallColMap 3)) = piHermiteParameter + 3 := by
  exact actual_pi_matrix_entry
