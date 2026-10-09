import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
namespace FixedQuadratic

/-- Only the simultaneous field automorphism is used, even if coordinates
coincide or are algebraically dependent. -/
theorem simultaneous_conjugate_evaluation {σ R K : Type*} [CommSemiring R] [Field K]
    (P : MvPolynomial σ R) (φ : R →+* K) (τ : K ≃+* K) (β : σ → K)
    (hfix : τ.toRingHom.comp φ = φ) :
    τ (P.eval₂ φ β) = P.eval₂ φ (fun i => τ (β i)) := by
  change τ.toRingHom (P.eval₂ φ β) = P.eval₂ φ (τ.toRingHom ∘ β)
  rw [MvPolynomial.eval₂_comp_left, hfix]

theorem simultaneous_conjugate_ne_zero {σ R K : Type*} [CommSemiring R] [Field K]
    (P : MvPolynomial σ R) (φ : R →+* K) (τ : K ≃+* K) (β : σ → K)
    (hfix : τ.toRingHom.comp φ = φ) (hne : P.eval₂ φ β ≠ 0) :
    P.eval₂ φ (fun i => τ (β i)) ≠ 0 := by
  rw [← simultaneous_conjugate_evaluation P φ τ β hfix]
  exact fun h => hne (τ.injective (by simpa using h))

/-- The repeated sqrt(2) example has nonzero genuine simultaneous norm and
zero fake mixed conjugate, so a Cartesian nonvanishing inference is invalid. -/
theorem cartesian_trap (x : ℝ) (hx : x^2 = 2) :
    x+x ≠ 0 ∧ x+(-x) = 0 ∧ (x+x)*((-x)+(-x)) = -8 := by
  constructor
  · nlinarith
  constructor
  · ring
  · nlinarith

end FixedQuadratic
