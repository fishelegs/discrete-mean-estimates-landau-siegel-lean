import checks.GeometryRegression
open FixedQuadratic.GeometryRegression
example : concreteGeometry.curveJetWeights (0 : Fin 1).succ ≤
    (1 : ℚ)*concreteGeometry.curveJetWeights 0 := by
  change (800000 : ℚ) ≤ 1 * 16
  norm_num
