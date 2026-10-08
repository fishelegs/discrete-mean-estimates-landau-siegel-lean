import LogPadeFiniteIdentity

example : (PiWeightedColon.logPadeP 1).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I) =
    (PiWeightedColon.logPadeRationalQ 1 : ℂ) :=
  PiWeightedColon.logPade_normalized_P_rational 1
