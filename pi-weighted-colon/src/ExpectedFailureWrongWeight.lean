import EndpointColon

open PiWeightedColon

-- Must fail: d=5 is not one of the proved weights.
example : (localJ F2 5 * localK F2 5 ^ 1).colon {localQ F2} = localJ F2 5 := by
  simpa only [Submodule.pow_zero, Ideal.IsTwoSided.mul_one] using
    localJK_colon (R := F2) (d := 5) (by decide) 0
