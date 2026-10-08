import LogPadeRegression

open PiWeightedColon

example : logPadeRationalQ 0 * logPadeRationalP 1 -
    logPadeRationalQ 1 * logPadeRationalP 0 = 1 :=
  Regression.log_pade_first_normalized_determinant
