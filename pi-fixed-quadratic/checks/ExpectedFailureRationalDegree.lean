import FixedQuadratic.PrimitiveHeight
open Polynomial
example : 0 < FixedQuadratic.primitiveMinpolyHeight 0 := by
  apply FixedQuadratic.primitiveMinpolyHeight_pos 0
  simp only [minpoly.zero, natDegree_X]
  norm_num
