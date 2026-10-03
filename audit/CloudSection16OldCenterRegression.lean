import ZhangLS.Spec.Lemma162OldCenterIncompatibility

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

-- Exact positive constant, including the branch-sensitive factor 2.
example : 0 < 6/(Real.pi^2*(2*lemma152ProductBound)*(Real.exp (2/Real.log 2))^2) :=
  lemma162_old_main_lower_constant_pos

-- Every ramified prime is retained, including 2 when it divides D.
example {D : ℕ} (hD : 0<D) :
    (Nat.totient D:ℝ)/(D:ℝ) ≤ ∏ q ∈ D.primeFactors, (q:ℝ)/((q:ℝ)+1) :=
  lemma162_old_ramified_product_lower hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (h2 : χ.evalNat 2=1) :
    ‖2*∏' q : {q : Nat.Primes // 2<q.val}, lemma161MainFactor χ q.val‖≤
      2*lemma152ProductBound := by
  simpa [lemma161MainTerm,h2] using lemma162_old_main_denominator_upper χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (h2 : χ.evalNat 2≠1) :
    ‖∏' q : Nat.Primes, lemma161MainFactor χ q‖≤2*lemma152ProductBound := by
  simpa [lemma161MainTerm,h2] using lemma162_old_main_denominator_upper χ

-- The source main expression is expanded literally here.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hL : 1<Real.log (D:ℝ)) :
    (6/(Real.pi^2*(2*lemma152ProductBound)*(Real.exp (2/Real.log 2))^2))/
      (1+Real.log (Real.log (D:ℝ)))^12 ≤
      ‖(6/(Real.pi:ℂ)^2)*((Nat.totient D:ℂ)/((D:ℂ)*lemma161MainTerm χ))*
        ∏ q ∈ D.primeFactors, (q:ℂ)/((q:ℂ)+1)‖ := by
  exact lemma162_old_main_lower χ hL

example (C : ℝ) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → 1<Real.log (D:ℝ) ∧
    C/(Real.log (D:ℝ))^4 <
      lemma162OldMainLowerConstant/(1+Real.log (Real.log (D:ℝ)))^12 :=
  lemma162_old_main_eventually_large C

-- Finite-D β1, not a zero-shift substitution; original ζ³L³ denominator.
example (C c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
    ∀ χ : RealPrimitiveCharacter D, ∀ U : ℂ → ℂ, ContinuousAt U 1 →
      (∀ s : ℂ, 1<s.re → U s =
        lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c)
          (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
            (riemannZeta s^3*dirichletLFunction χ s^3)) →
      C/(Real.log (D:ℝ))^4 <
        ‖U 1-(6/(Real.pi:ℂ)^2)*((Nat.totient D:ℂ)/((D:ℂ)*lemma161MainTerm χ))*
          ∏ q ∈ D.primeFactors, (q:ℂ)/((q:ℂ)+1)‖ := by
  obtain ⟨D₀,_,_,h⟩ := lemma162_paper_old_center_strict_error C c hc
  refine ⟨D₀,?_⟩
  intro D hD χ U hU hquot
  simpa only [lemma162_paper_shift_zero,lemma162CorrectedCenterMain] using
    h D hD χ 0 U hU (by simpa only [lemma162_paper_shift_zero] using hquot)

-- Finite-D β2 with the same fixed c′, and all source arithmetic unchanged.
example (C c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
    ∀ χ : RealPrimitiveCharacter D, ∀ U : ℂ → ℂ, ContinuousAt U 1 →
      (∀ s : ℂ, 1<s.re → U s =
        lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)
          (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
            (riemannZeta s^3*dirichletLFunction χ s^3)) →
      C/(Real.log (D:ℝ))^4 <
        ‖U 1-(6/(Real.pi:ℂ)^2)*((Nat.totient D:ℂ)/((D:ℂ)*lemma161MainTerm χ))*
          ∏ q ∈ D.primeFactors, (q:ℂ)/((q:ℂ)+1)‖ := by
  obtain ⟨D₀,_,_,h⟩ := lemma162_paper_old_center_strict_error C c hc
  refine ⟨D₀,?_⟩
  intro D hD χ U hU hquot
  simpa only [lemma162_paper_shift_one,lemma162CorrectedCenterMain] using
    h D hD χ 1 U hU (by simpa only [lemma162_paper_shift_one] using hquot)

-- Source (A) is an explicit premise, with no existence conclusion.
example (C c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
    ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 2, ∀ U : ℂ → ℂ, ContinuousAt U 1 →
        (∀ s : ℂ, 1<s.re → U s =
          lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
              (riemannZeta s^3*dirichletLFunction χ s^3)) →
        ¬ ‖U 1-(6/(Real.pi:ℂ)^2)*((Nat.totient D:ℂ)/((D:ℂ)*lemma161MainTerm χ))*
          ∏ q ∈ D.primeFactors, (q:ℂ)/((q:ℂ)+1)‖≤C/(Real.log (D:ℝ))^4 := by
  obtain ⟨D₀,_,_,h⟩ := lemma162_source_A_old_center_incompatibility C c hc
  exact ⟨D₀,h⟩

example (C c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
    ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 2, ∀ U : ℂ → ℂ,
        Lemma162OriginalContinuation χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
          (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) U →
        ¬ ‖U 1-lemma162CorrectedCenterMain χ‖≤C/(Real.log (D:ℝ))^4 := by
  obtain ⟨D₀,_,_,h⟩ := lemma162_source_A_old_continuation_incompatibility C c hc
  exact ⟨D₀,h⟩

-- The concrete old extension supplies the continuity/quotient premises.
example (C c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
    ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      ContinuousAt (lemma162OldActualExtension χ (lemma52PaperBetaOne D c)
        (lemma162PaperShift D c j)) 1 ∧
      C/(Real.log (D:ℝ))^4 <
        ‖lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) 1-
          lemma162CorrectedCenterMain χ‖ := by
  obtain ⟨D₀,_,_,h⟩ := lemma162_paper_old_actual_extension_strict_error C c hc
  exact ⟨D₀,fun D hD χ j => ⟨(h D hD χ j).1,(h D hD χ j).2.2⟩⟩

example : ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
    ∀ C : ℝ, ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 2, ∀ U : ℂ → ℂ, ContinuousAt U 1 →
          (∀ s : ℂ, 1<s.re → U s =
            lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
              (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
                (riemannZeta s^3*dirichletLFunction χ s^3)) →
          ¬ ‖U 1-lemma162CorrectedCenterMain χ‖≤C/lemma23PaperL D^4 :=
  lemma162_old_center_shared_constant

end ZhangLS.Spec
