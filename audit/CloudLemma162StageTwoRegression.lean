import ZhangLS.Spec.Lemma162ActualOldValueWitness

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1800000

-- Actual shifted arithmetic identity and analyticity, not a free model V.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) (hstar : lemma161Star χ β (1-γ)≠0) :
    AnalyticOnNhd ℂ (lemma162CorrectedEulerProduct χ β γ) {s : ℂ | 9/10<s.re} ∧
      ∀ s : ℂ, 1<s.re →
        lemma162CorrectedEulerProduct χ β γ s*riemannZeta s^2*riemannZeta (s-γ)*
          dirichletLFunction χ s*dirichletLFunction χ (s-γ)^2 =
            lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s := by
  have h := lemma162_actual_shifted_continuation χ β hβ γ hγ hstar
  exact ⟨h.1,fun s hs => (h.2 s hs).2⟩

-- Original shared c′ and both nonzero paper shifts; no assumption(A).
example (c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      AnalyticOnNhd ℂ (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
        (lemma162PaperShift D c j)) {s : ℂ | 9/10<s.re} := by
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_corrected_analytic_bridge c hc
  exact ⟨D₀,hD₀,fun D hD χ j => (h D hD χ j).1.1⟩

-- The explicit old extension exists at1 and has value0, agreeing at genuine convergent points.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (hγ0 : γ≠0)
    (hstar : lemma161Star χ β (1-γ)≠0) :
    ContinuousAt (lemma162OldActualExtension χ β γ) 1 ∧
      lemma162OldActualExtension χ β γ 1=0 ∧
      ∀ s : ℂ, 1<s.re → lemma162OldActualExtension χ β γ s =
        lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s /
          (riemannZeta s^3*dirichletLFunction χ s^3) :=
  lemma162_old_actual_continuous_extension χ hD β hβ γ hγ hγ0 hstar

-- The former corrected-factorization premise is absent from the actual uniqueness witness.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (β : ℂ) (hβ : β.re=0) (γ : ℂ) (hγ : γ.re=0) (hγ0 : γ≠0)
    (hstar : lemma161Star χ β (1-γ)≠0) (U : ℂ → ℂ) (hU : ContinuousAt U 1)
    (hquot : ∀ s : ℂ, 1<s.re → U s =
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s /
        (riemannZeta s^3*dirichletLFunction χ s^3)) : U 1=0 :=
  lemma162_actual_original_value_forced_zero χ hD β hβ γ hγ hγ0 hstar U hU hquot

-- All actual local normalizers, including the exceptional prime, multiply to M₂*.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) :
    HasProd (lemma162LocalNormalizer χ β γ) (lemma161Star χ β (1-γ)) :=
  lemma162_normalizers_hasProd χ β hβ γ hγ

-- The exact finite-D ramified factor is separate from the absolute unramified majorant.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β γ : ℂ) (q : Nat.Primes)
    (hq : q.val∣D) (s : ℂ) :
    lemma162RawPrimeCorrection χ β γ q s = (1-lemma32PrimeMonomial q.val s)^2 := by
  simp only [lemma162RawPrimeCorrection,if_pos (χ.evalNat_eq_zero_of_dvd_modulus hq q.property.ne_one)]

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) (q : Nat.Primes) (hq : ¬q.val∣D) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162RawPrimeCorrection χ β γ q s-1‖≤lemma162UnramifiedMajorant q :=
  lemma162_unramified_raw_error_majorized χ β hβ γ hγ q hq s hs

-- The actual full-half-plane bound retains D and normalization dependence explicitly.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) (s : ℂ) (hs : 9/10≤s.re) :
    ‖lemma162CorrectedEulerProduct χ β γ s‖≤
      lemma162RawDBound D/‖lemma161Star χ β (1-γ)‖ :=
  lemma162_corrected_euler_bound χ β hβ γ hγ s hs

-- Fully expanded actual divisor coefficients and actual convolution, rather than a model series.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (γ : ℂ) (hγ : γ.re=0) (hstar : lemma161Star χ β (1-γ)≠0)
    (s : ℂ) (hs : 1<s.re) :
    lemma162CorrectedEulerProduct χ β γ s*riemannZeta s^2*riemannZeta (s-γ)*
      dirichletLFunction χ s*dirichletLFunction χ (s-γ)^2 =
    LSeries (fun n : ℕ =>
      (∑ dl ∈ n.divisorsAntidiagonal,
        lemma161Lambda χ β dl.1*(dl.1:ℂ)^γ*χ.evalNat dl.2*
          (lemma162GeneralMEulerProduct χ β dl.1 dl.2 (1-γ)/lemma161Star χ β (1-γ))) *
        (lemma23NuArithmeticFunction χ*lemma23CharacterArithmeticFunction χ) n) s := by
  change _ = lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s
  simpa only [lemma162ShiftedMainFactor,mul_assoc] using
    lemma162_actual_shifted_euler_identity χ β hβ γ hγ hstar s hs

-- Raw q=2 degree zero remains F00, with the exceptional normalizer exactly 2.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β γ : ℂ) (h2 : χ.evalNat 2=1) :
    lemma162RawPrimeCoefficient χ β γ lemma162PrimeTwo 0 /
      lemma162LocalNormalizer χ β γ lemma162PrimeTwo =
        lemma161PrimeFactor χ β lemma162PrimeTwo (1-γ)/2 := by
  simp [lemma162RawPrimeCoefficient,lemma162_raw_coefficient_zero,lemma83LocalH3,
    lemma83AddConvolution,lemma162LocalNormalizer,lemma162Local00,lemma162TwoNormalizer,h2]

-- Both original nonzero paper shifts appear explicitly in the corrected extraction.
example (c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ s : ℂ, 1<s.re →
      (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c) s *
        riemannZeta s^2*riemannZeta (s-lemma52PaperBetaOne D c)*dirichletLFunction χ s*
        dirichletLFunction χ (s-lemma52PaperBetaOne D c)^2 =
          lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaOne D c)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s) ∧
      (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c) s *
        riemannZeta s^2*riemannZeta (s-lemma52PaperBetaTwo D c)*dirichletLFunction χ s*
        dirichletLFunction χ (s-lemma52PaperBetaTwo D c)^2 =
          lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s) := by
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_corrected_analytic_bridge c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ s hs
  constructor
  · simpa only [lemma162_paper_shift_zero] using ((h D hD χ (0:Fin 2)).1.2 s hs).2
  · simpa only [lemma162_paper_shift_one] using ((h D hD χ (1:Fin 2)).1.2 s hs).2

-- The analytic wrapper admits the same compatible c′ already used in Lemma 5.2.
example : ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      Lemma162ShiftedContinuation χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
        (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c))
        (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)) ∧
      ContinuousAt (lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)) 1 ∧
      lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) 1=0 := by
  obtain ⟨c,hc,hcompatible,_⟩ := lemma162_arithmetic_bridge_with_shared_shift_constant
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_corrected_analytic_bridge c hc
  exact ⟨c,hc,hcompatible,D₀,hD₀,fun D hD χ j =>
    ⟨(h D hD χ j).1,(h D hD χ j).2.2.1,(h D hD χ j).2.2.2.1⟩⟩

end ZhangLS.Spec
