import checks.UpstreamAnalysisBridge
open FixedQuadratic FixedQuadratic.UpstreamPacketArithmetic FixedQuadratic.UpstreamAnalysis
example {m : ℕ} (F : IntermediateField ℚ ℝ) (β : Fin m → F)
    (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (j k : ℕ) (ν : ℝ) (hk : 1 ≤ k) (hj : j ≤ k) (hν : 0 ≤ ν)
    (happrox : ∀ i, |Real.pi-(β i : ℝ)| ≤
      (primitiveMinpolyHeight (β i : ℝ) : ℝ)^(-ν)) (i : Fin m) :
    ‖centerError F β j i‖ ≤ Real.exp (Real.log (2*(k : ℝ))-ν*primitiveWeights F β i) := by
  exact actual_center_error_exp F β hβ j k ν hk hj hν happrox i
