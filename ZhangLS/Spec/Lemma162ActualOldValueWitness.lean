import ZhangLS.Spec.Lemma162CorrectedAnalytic
import ZhangLS.Spec.Lemma162PaperArithmeticBridge

/-! Genuine original-quotient center witness. The corrected analytic Euler
product and its arithmetic identity are PROVED dependencies, not premises.
No assumption(A), existence of an(A)-character, or totalized pole value is used. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

noncomputable def lemma162OldActualExtension {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (s : ℂ) : ℂ :=
  lemma162RegularOldExtension χ γ (lemma162CorrectedEulerProduct χ β γ) s

/-- An explicit continuous extension at1 of the literal original quotient,
with its unique forced value0. Only ordinary convergent points define its agreement. -/
lemma lemma162_old_actual_continuous_extension {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (hγ0 : γ≠0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) :
    ContinuousAt (lemma162OldActualExtension χ β γ) 1 ∧
      lemma162OldActualExtension χ β γ 1=0 ∧
      ∀ s : ℂ, 1<s.re → lemma162OldActualExtension χ β γ s =
        lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s /
          (riemannZeta s^3*dirichletLFunction χ s^3) := by
  have hV : ContinuousAt (lemma162CorrectedEulerProduct χ β γ) 1 :=
    ((lemma162_corrected_euler_analytic χ β hβ γ hγ) 1 (by norm_num)).continuousAt
  refine ⟨lemma162_regular_old_extension_continuous χ hD γ hγ0 _ hV,
    lemma162_regular_old_extension_at_one χ γ _,?_⟩
  intro s hs
  rw [lemma162OldActualExtension,lemma162_regular_old_extension_eq_quotient χ γ _ s hs]
  have he := lemma162_actual_shifted_euler_identity χ β hβ γ hγ hstar s hs
  have he' : lemma162CorrectedEulerProduct χ β γ s*riemannZeta s^2*riemannZeta (s-γ)*
      dirichletLFunction χ s*dirichletLFunction χ (s-γ)^2 =
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s := by
    simpa only [lemma162ShiftedMainFactor,mul_assoc] using he
  rw [he']

/-- Any continuous extension of the ACTUAL old quotient has value0. The
former free corrected-factorization premise has now been discharged. -/
lemma lemma162_actual_original_value_forced_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (hγ0 : γ≠0)
    (hstar : lemma161Star χ β (1-γ) ≠ 0) (U : ℂ → ℂ) (hU : ContinuousAt U 1)
    (hquot : ∀ s : ℂ, 1<s.re → U s =
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s /
        (riemannZeta s^3*dirichletLFunction χ s^3)) : U 1=0 := by
  apply lemma162_original_value_forced_zero χ hD γ hγ0 U (lemma162CorrectedEulerProduct χ β γ)
    (lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β)) hU
    (((lemma162_corrected_euler_analytic χ β hβ γ hγ) 1 (by norm_num)).continuousAt) _ hquot
  intro s hs
  simpa only [lemma162ShiftedMainFactor,mul_assoc] using
    (lemma162_actual_shifted_euler_identity χ β hβ γ hγ hstar s hs).symm

/-- The exact shared-c′ paper parameters, with all denominator/shift
nonvanishing supplied by proved original16.1 and arithmetic threshold theorems. -/
theorem lemma162_paper_corrected_analytic_bridge (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      Lemma162ShiftedContinuation χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
        (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c))
        (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)) ∧
      (∀ s : ℂ, 9/10≤s.re →
        ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s‖ ≤
          lemma162RawDBound D/‖lemma161Star χ (lemma52PaperBetaOne D c) (1-lemma162PaperShift D c j)‖) ∧
      ContinuousAt (lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)) 1 ∧
      lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) 1=0 ∧
      ∀ s : ℂ, 1<s.re →
        lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s =
          lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
              (riemannZeta s^3*dirichletLFunction χ s^3) := by
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_actual_arithmetic_bridge c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ j
  have hd : 1<D := by omega
  have hh := (h D hD χ).2 j
  have hβ := lemma161_paper_beta_re D c
  have hγ := lemma162_paper_shift_re D c j
  refine ⟨lemma162_actual_shifted_continuation χ _ hβ _ hγ hh.2.1,
    fun s hs => lemma162_corrected_euler_bound χ _ hβ _ hγ s hs,?_⟩
  exact lemma162_old_actual_continuous_extension χ hd _ hβ _ hγ hh.1 hh.2.1

/-- The explicit old-center extension is constructed in the previous theorem;
this states uniqueness for other claimed extensions and makes no assertion that an(A)-character exists. -/
theorem lemma162_paper_old_center_forced_zero (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      ∀ U : ℂ → ℂ, ContinuousAt U 1 →
        (∀ s : ℂ, 1<s.re → U s =
          lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
              (riemannZeta s^3*dirichletLFunction χ s^3)) → U 1=0 := by
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_actual_arithmetic_bridge c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ j U hU hquot
  have hh := (h D hD χ).2 j
  exact lemma162_actual_original_value_forced_zero χ (by omega) _ (lemma161_paper_beta_re D c)
    _ (lemma162_paper_shift_re D c j) hh.1 hh.2.1 U hU hquot

end ZhangLS.Spec
