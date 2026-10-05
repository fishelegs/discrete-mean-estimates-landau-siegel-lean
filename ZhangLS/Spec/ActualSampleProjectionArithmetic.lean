import ZhangLS.Spec.ActualSampleProjection
import ZhangLS.Spec.ActualSampleProjectionFourier

/-! # Genuine primitive Dirichlet mean equals projected finite sample energy

The arithmetic polynomial, primitive character family, and Gauss normalization are the
published objects. Unit deletion supplies the zero-mean property used in the exact projection
identity. No premise bounds the desired mean or the nonpolar energy.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.ActualSampleProjection
open scoped BigOperators Classical
noncomputable section
variable {p : ℕ} [NeZero p]

def paritySign (odd : Bool) : ℝ := if odd then -1 else 1

def primitiveMean (odd : Bool) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p =>
    χ.IsPrimitive ∧ χ (-1) = (paritySign odd : ℂ)),
    ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2

theorem primitiveMean_eq_moment (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hF : (∑ j : ZMod p, lemma33AdditivePolynomial S a j) = 0) :
    primitiveMean (p := p) odd S a = moment odd (lemma33AdditivePolynomial (p := p) S a) := by
  have hs : paritySign odd = 1 ∨ paritySign odd = -1 := by
    cases odd <;> simp [paritySign]
  unfold primitiveMean
  rw [actualSample_additivePolynomial_primitive_parity_mean_exact_of_zero_mean hp S a hF _ hs]
  cases odd <;> norm_num [moment, evenMoment, oddMoment, paritySign, energy, pairing,
    Complex.re_sum, Complex.normSq_eq_norm_sq, Finset.sum_add_distrib]
  all_goals ring_nf
  all_goals simp

theorem primitiveMean_eq_projected_energy_of_units (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, IsUnit (n : ZMod p)) :
    primitiveMean (p := p) odd S a = ((p : ℝ) - 1) / p *
      energy (project odd (lemma33AdditivePolynomial (p := p) S a)) := by
  have hz := actualSample_additivePolynomial_sum_eq_zero_of_units hp.one_lt S a hS
  rw [primitiveMean_eq_moment hp odd S a hz, moment_eq_projected_energy hp.two_le odd _ hz]

theorem primitiveMean_eq_projected_energy_of_nonunit_vanish (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ¬ IsUnit (n : ZMod p) → a n = 0) :
    primitiveMean (p := p) odd S a = ((p : ℝ) - 1) / p *
      energy (project odd (lemma33AdditivePolynomial (p := p) S a)) := by
  have hz := actualSample_additivePolynomial_sum_eq_zero_of_nonunit_vanish hp.one_lt S a ha
  rw [primitiveMean_eq_moment hp odd S a hz, moment_eq_projected_energy hp.two_le odd _ hz]

theorem primitiveMean_local_error_identity_of_units (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, IsUnit (n : ZMod p))
    (A : Samples p) (diagonal : ℝ) :
    primitiveMean (p := p) odd S a =
      nonpolarRemainder odd (lemma33AdditivePolynomial S a) A diagonal +
      ((p : ℝ) - 1) / 2 * diagonal + polarEnergy odd A := by
  have hz := actualSample_additivePolynomial_sum_eq_zero_of_units hp.one_lt S a hS
  rw [primitiveMean_eq_moment hp odd S a hz]
  exact actual_moment_local_error_identity hp.two_le odd _ A hz diagonal


/-- Actual deleted Fourier terms are constant, and both projections annihilate them. -/
theorem project_additivePolynomial_unitFilter (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    project odd (lemma33AdditivePolynomial (p := p) S a) =
      project odd (lemma33AdditivePolynomial (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a) := by
  have hf : lemma33AdditivePolynomial (p := p) S a = fun j =>
      lemma33AdditivePolynomial (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a j +
        ∑ n ∈ S.filter (fun n : ℕ => p ∣ n), a n := by
    funext j
    exact actualSample_additivePolynomial_eq_unitFilter_add_constant hp S a j
  rw [hf, project_add, project_constant]
  funext j
  simp

theorem primitiveMean_unitFilter (odd : Bool) (S : Finset ℕ) (a : ℕ → ℂ) :
    primitiveMean (p := p) odd S a =
      primitiveMean (p := p) odd (S.filter (fun n : ℕ => IsUnit (n : ZMod p))) a := by
  unfold primitiveMean
  apply Finset.sum_congr rfl
  intro χ hχ
  apply congrArg (fun x : ℂ => ‖x‖ ^ 2)
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hnu : ¬ IsUnit (n : ZMod p) := by
    intro hu
    exact hnot (Finset.mem_filter.mpr ⟨hn, hu⟩)
  rw [χ.map_nonunit hnu, mul_zero]

/-- Strongest finite arithmetic endpoint: arbitrary finite coefficients, actual primitive
parity family, exact normalization, and no zero-mean premise on the full additive vector. -/
theorem primitiveMean_eq_projected_energy (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    primitiveMean (p := p) odd S a = ((p : ℝ) - 1) / p *
      energy (project odd (lemma33AdditivePolynomial (p := p) S a)) := by
  rw [primitiveMean_unitFilter odd S a]
  rw [primitiveMean_eq_projected_energy_of_units hp odd _ a
    (fun n hn => (Finset.mem_filter.mp hn).2)]
  rw [project_additivePolynomial_unitFilter hp odd S a]

/-- Full finite arithmetic local error identity. The polar vector and the full additive
vector need not have mean zero; unit deletion is handled internally by the proved projector. -/
theorem primitiveMean_local_error_identity (hp : p.Prime) (odd : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ) (A : Samples p) (diagonal : ℝ) :
    primitiveMean (p := p) odd S a =
      nonpolarRemainder odd (lemma33AdditivePolynomial S a) A diagonal +
      ((p : ℝ) - 1) / 2 * diagonal + polarEnergy odd A := by
  rw [primitiveMean_eq_projected_energy hp odd S a,
    projected_error_identity odd (lemma33AdditivePolynomial S a) A]
  unfold nonpolarRemainder polarEnergy
  ring

omit [NeZero p] in
theorem odd_character_is_odd (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) :
    Odd (fun j => χ j) := by
  intro j
  change χ (-j) = -χ j
  rw [← neg_one_mul, map_mul, hχ, neg_one_mul]

theorem odd_character_projection (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) :
    project true (fun j => χ j) = (fun j => χ j) ∧
      project false (fun j => χ j) = 0 := by
  exact ⟨oddProjection_fixed (odd_character_is_odd χ hχ),
    evenProjection_of_odd (odd_character_is_odd χ hχ)⟩

end
end ZhangLS.Spec.ActualSampleProjection
