import PiFamilyReversal

/- The cutoff cannot be dropped by applying the tail theorem to N = 2.
This expected failure checks the rejected precondition, not the exact N=2 gain. -/
example : ‖PiFamilyReversal.family 2 (2 * (Real.pi : ℂ) * Complex.I)‖ <
    ‖PiFamilyReversal.family 2 ((44 : ℂ)/7 * Complex.I)‖ := by
  apply PiFamilyReversal.family_reversal 2
  norm_num
