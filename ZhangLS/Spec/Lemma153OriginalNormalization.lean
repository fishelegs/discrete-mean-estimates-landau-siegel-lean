import ZhangLS.Spec.Lemma153ActualContinuation
/-! Exact relation to the literal normalization printed in Lemma15.3.
This is stated only on the absolute-convergence half-plane. It does not
assert removability at zeros of L(s,χ), or extend a totalized quotient. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1000000

lemma lemma153_original_normalization_on_convergence {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0)
    (s : ℂ) (hs : 1<s.re) :
    lemma153DirichletSeries χ β γ (lemma153GeneralMEulerProduct χ β) s /
      (riemannZeta s^2*dirichletLFunction χ s^2) =
        lemma153EulerProduct χ β γ s *
          (dirichletLFunction χ (s-γ)/dirichletLFunction χ s)^2 := by
  letI : NeZero D := ⟨hD⟩
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hl : dirichletLFunction χ s ≠ 0 := by
    unfold dirichletLFunction
    rw [DirichletCharacter.LFunction_eq_LSeries χ.chi hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ.chi hs
  have he := (lemma153_actual_shifted_continuation hD χ β γ hpar hM).2 s hs |>.2
  rw [← he]
  field_simp

end ZhangLS.Spec
