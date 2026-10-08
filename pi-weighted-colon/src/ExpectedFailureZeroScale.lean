import EndpointColon

open PiWeightedColon

-- Must fail: the N≥1 hypothesis cannot be omitted.
example : (dataIntersection 0).colon {globalQ} = dataIntersection (0 - 1) := by
  exact intersection_colon_pred (by decide)
