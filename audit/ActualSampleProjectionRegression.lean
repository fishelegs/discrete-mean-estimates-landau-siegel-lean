import ZhangLS.Spec.ActualSampleProjectionArithmetic

set_option autoImplicit false
namespace ZhangLS.Spec.ActualSampleProjection.Regression
open scoped BigOperators Classical
noncomputable section

/-- Both exact operators are self-adjoint idempotent contractions on every input vector. -/
theorem orthogonal_projection_endpoints {p : ℕ} [NeZero p] (hp : 2 ≤ p)
    (odd : Bool) (z w : Samples p) :
    project odd (project odd z) = project odd z ∧
    pairing (project odd z) w = pairing z (project odd w) ∧
    energy (project odd z) ≤ energy z :=
  ⟨project_idempotent hp odd z, project_selfadjoint hp odd z w, project_contracts hp odd z⟩

/-- The principal vector has positive raw energy but vanishes after either projection. -/
theorem principal_mode_endpoint {p : ℕ} [NeZero p] (hp : 2 ≤ p) (odd : Bool) :
    project odd (principal p) = 0 ∧
      energy (principal p) = (p : ℝ) / ((p : ℝ) - 1) := by
  refine ⟨project_principal hp odd, ?_⟩
  simpa using energy_principal hp (1 : ℂ)

theorem constant_mode_endpoint {p : ℕ} [NeZero p] (odd : Bool) (c : ℂ) :
    project odd (fun _ : ZMod p => c) = 0 := project_constant odd c

theorem zero_mode_endpoint {p : ℕ} [NeZero p] (odd : Bool) :
    project odd (0 : Samples p) = 0 := project_zero odd

/-- At the exceptional prime 2 the entire projected space is zero, for all vectors. -/
theorem p_two_endpoint (odd : Bool) (z : Samples 2) :
    project odd z = 0 := project_p_two odd z

/-- This evaluates the actual primitive family for p=2, with arbitrary finite coefficients. -/
theorem p_two_arithmetic_endpoint (odd : Bool) (S : Finset ℕ) (a : ℕ → ℂ) :
    primitiveMean (p := 2) odd S a = 0 := by
  rw [primitiveMean_eq_projected_energy (by decide) odd S a, project_p_two]
  simp [energy]

theorem odd_character_endpoint {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p)
    (hχ : χ (-1) = -1) :
    project true (fun j => χ j) = (fun j => χ j) ∧
      project false (fun j => χ j) = 0 := odd_character_projection χ hχ

/-- No zero-mean hypothesis is imposed on this full Fourier polynomial. -/
theorem full_arithmetic_endpoint {p : ℕ} [NeZero p] (hp : p.Prime)
    (odd : Bool) (S : Finset ℕ) (a : ℕ → ℂ) :
    primitiveMean (p := p) odd S a = ((p : ℝ) - 1) / p *
      ∑ j : ZMod p, Complex.normSq (project odd (lemma33AdditivePolynomial S a) j) :=
  primitiveMean_eq_projected_energy hp odd S a

/-- Unit deletion is invisible to the actual projector, with its constant term proved by DFT. -/
theorem unit_deletion_endpoint {p : ℕ} [NeZero p] (hp : p.Prime)
    (odd : Bool) (S : Finset ℕ) (a : ℕ → ℂ) :
    project odd (lemma33AdditivePolynomial (p := p) S a) =
      project odd (lemma33AdditivePolynomial (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a) :=
  project_additivePolynomial_unitFilter hp odd S a

/-- The local polar sample can be an arbitrary vector of any mean. -/
theorem full_local_error_endpoint {p : ℕ} [NeZero p] (hp : p.Prime)
    (odd : Bool) (S : Finset ℕ) (a : ℕ → ℂ) (A : Samples p) (diagonal : ℝ) :
    primitiveMean (p := p) odd S a =
      nonpolarRemainder odd (lemma33AdditivePolynomial S a) A diagonal +
      ((p : ℝ) - 1) / 2 * diagonal + polarEnergy odd A :=
  primitiveMean_local_error_identity hp odd S a A diagonal

theorem polar_energy_endpoint {p : ℕ} [NeZero p] (hp : 2 ≤ p)
    (odd : Bool) (A : Samples p) :
    0 ≤ polarEnergy odd A ∧
      polarEnergy odd A ≤ ((p : ℝ) - 1) * (energy A / p) :=
  ⟨polarEnergy_nonneg hp odd A, polarEnergy_le hp odd A⟩

theorem hilbert_triangle_endpoint {p : ℕ} [NeZero p] (odd : Bool) (F A : Samples p) :
    Real.sqrt (energy (project odd F)) ≤
      Real.sqrt (energy (project odd (fun j => F j - A j))) +
      Real.sqrt (energy (project odd A)) := projected_error_triangle odd F A

end
end ZhangLS.Spec.ActualSampleProjection.Regression
