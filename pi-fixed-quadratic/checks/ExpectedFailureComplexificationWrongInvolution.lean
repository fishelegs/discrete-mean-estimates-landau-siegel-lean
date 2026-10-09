import FixedQuadratic.Complexification
-- The identity automorphism cannot supply the simultaneous nontrivial norm pair.
example (F : IntermediateField ℚ ℝ) :
    FixedQuadratic.complexificationConjugation F (1 : F ≃ₐ[ℚ] F) ≠ 1 := by
  apply FixedQuadratic.complexificationConjugation_ne_one F 1
  simp
