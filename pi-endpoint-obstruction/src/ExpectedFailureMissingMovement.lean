import PiRowRank
set_option autoImplicit false

-- A downward identity assignment does not force a determinant to vanish.
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.det = 0 := by
  apply PiRowRank.det_reindexed_eq_zero_of_downward_nonidentity
    (fun _ => 0) id A (by simp)
  simp
