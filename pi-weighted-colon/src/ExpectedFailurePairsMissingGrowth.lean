import ApproximationPairs

example (α C η : ℝ) (hC : 0 < C) (p q a b : ℤ) (hq : 0 < q) (hb : 1 ≤ b)
    (herror : |(b : ℝ) * α - (a : ℝ)| ≤ η / (q : ℝ))
    (hcross : b * p - a * q ≠ 0) :
    ((1 - η) / C) / (q : ℝ) ^ 2 ≤ |α - (p : ℝ) / q| :=
  PiWeightedColon.one_approximant_lower_bound α C η hC p q a b hq hb herror herror hcross
