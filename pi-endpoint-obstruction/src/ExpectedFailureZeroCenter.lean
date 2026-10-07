import PiQualityFreeExample
set_option autoImplicit false

-- Omitting nonzero-center input cannot prove nonvanishing at the zero center.
example : (PiRowRank.qualityFreeMatrix 0).det ≠ 0 := by
  apply PiRowRank.qualityFreeMatrix_det_ne_zero
  norm_num
