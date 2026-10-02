import ZhangLS.Spec.Lemma23DirichletConjugation

/-!
# The uncompleted Dirichlet functional equation in Lemma 2.3

This module expands mathlib's completed functional equation into the factor
`Z(s, χ)` used in Zhang's paper.  The quotient is stated where its gamma
denominator is nonzero; later lemmas establish that condition on the upper
half-plane / critical line.
-/

namespace ZhangLS.Spec

open Complex

/-- The paper's functional-equation factor, written using mathlib's completed
L-function and archimedean gamma factors. -/
noncomputable def lemma23DirichletZ {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ ((1 / 2 : ℂ) - s) * DirichletCharacter.rootNumber χ *
    (DirichletCharacter.gammaFactor χ⁻¹ (1 - s) /
      DirichletCharacter.gammaFactor χ s)

/-- The archimedean factor does not vanish in the right half-plane. -/
theorem lemma23_gammaFactor_ne_zero_of_re_pos
    {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hodd.gammaFactor_def]
    have hs' : 0 < s.re + 1 := by linarith
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simpa [Complex.add_re] using hs'

/-- Mathlib's completed functional equation, divided by the gamma factors,
gives Zhang's uncompleted equation `L(s,χ)=Z(s,χ)L(1-s,χ⁻¹)`. -/
theorem lemma23_dirichletLFunction_functional_equation
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1) {s : ℂ}
    (hγ : DirichletCharacter.gammaFactor χ s ≠ 0)
    (hγinv : DirichletCharacter.gammaFactor χ⁻¹ (1 - s) ≠ 0) :
    DirichletCharacter.LFunction χ s =
      lemma23DirichletZ χ s * DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN)
  have hLinv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    χ⁻¹ (1 - s) (Or.inr hN)
  have hcompletedInv : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) =
      DirichletCharacter.LFunction χ⁻¹ (1 - s) *
        DirichletCharacter.gammaFactor χ⁻¹ (1 - s) := by
    calc
      _ = (DirichletCharacter.completedLFunction χ⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor χ⁻¹ (1 - s)) *
            DirichletCharacter.gammaFactor χ⁻¹ (1 - s) :=
        (div_mul_cancel₀ _ hγinv).symm
      _ = _ := by rw [← hLinv]
  have hcompletedFE : DirichletCharacter.completedLFunction χ s =
      (N : ℂ) ^ ((1 / 2 : ℂ) - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hχ.completedLFunction_one_sub (1 - s)
    have harg : 1 - (1 - s) = s := by ring
    have hexp : (1 - s) - (1 / 2 : ℂ) = (1 / 2 : ℂ) - s := by ring
    rw [harg, hexp] at h
    exact h
  calc
    DirichletCharacter.LFunction χ s =
        DirichletCharacter.completedLFunction χ s /
          DirichletCharacter.gammaFactor χ s := hL
    _ = ((N : ℂ) ^ ((1 / 2 : ℂ) - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s)) /
          DirichletCharacter.gammaFactor χ s := by rw [hcompletedFE]
    _ = ((N : ℂ) ^ ((1 / 2 : ℂ) - s) * DirichletCharacter.rootNumber χ *
        (DirichletCharacter.LFunction χ⁻¹ (1 - s) *
          DirichletCharacter.gammaFactor χ⁻¹ (1 - s))) /
          DirichletCharacter.gammaFactor χ s := by rw [hcompletedInv]
    _ = lemma23DirichletZ χ s * DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
      simp only [lemma23DirichletZ]
      field_simp [hγ]

end ZhangLS.Spec
