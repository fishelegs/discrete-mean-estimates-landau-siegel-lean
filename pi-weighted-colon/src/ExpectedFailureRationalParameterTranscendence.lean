import SpecializationRegression

open PiWeightedColon PiWeightedColon.Regression

example : Transcendental ℚ (imaginaryRealParameter 2) := by
  exact imaginaryRealParameter_two_not_transcendental
