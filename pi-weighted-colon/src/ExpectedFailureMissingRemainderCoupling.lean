import RemainderVanish

open PiWeightedColon Polynomial

-- Must fail: the coupled condition is false for A=X, B=0 at N=0.
example : (X : Line) = 0 := by
  have h := remainder_even 0 (X : Line) 0 (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) ?_
  · exact h.1
  · norm_num [u]
