import FixedQuadratic.QuadraticNorm

-- A degree-four compositum cannot use the two-embedding norm formula.
example {G K : Type*} [Field G] [Field K] [Algebra G K]
    [FiniteDimensional G K] [IsGalois G K]
    (hdegree : Module.finrank G K = 4) (τ : K ≃ₐ[G] K) (hτ : τ ≠ 1) (q : K) :
    algebraMap G K (Algebra.norm G q) = q * τ q := by
  exact FixedQuadratic.quadratic_norm_identity hdegree τ hτ q
