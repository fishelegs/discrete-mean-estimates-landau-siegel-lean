import LogPadeFiniteIdentity

open Polynomial PiWeightedColon

example : logPadeP 0 * logPadeL 1 - logPadeP 1 * logPadeL 0 = C (logPadeD 0) * X ^ 2 :=
  logPade_adjacent_determinant 0
