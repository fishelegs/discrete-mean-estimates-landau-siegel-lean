import LogPadeRegression

open PiWeightedColon

example : logPadeRationalQ 1 * logPadeRationalP 2 -
    logPadeRationalQ 2 * logPadeRationalP 1 = 1 / 6 :=
  Regression.log_pade_second_normalized_determinant
