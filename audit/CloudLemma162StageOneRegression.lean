import ZhangLS.Spec.Lemma162PaperArithmeticBridge
import ZhangLS.Spec.Lemma162LocalExtraction
import ZhangLS.Spec.Lemma162HadamardH2H3
import ZhangLS.Spec.Lemma162NuChiLocalH3

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

-- Expanded original first-shift arithmetic-series regression.
example (c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ s : ℂ, 1<s.re →
      LSeriesSummable (lemma162Coefficient χ (lemma52PaperBetaOne D c)
        (lemma52PaperBetaOne D c) (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c))) s := by
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_actual_arithmetic_bridge c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ s hs
  simpa only [lemma162_paper_shift_zero] using (((h D hD χ).2 (0:Fin 2)).2.2 s hs).1

-- Expanded second-shift Euler identity, not a zero-shift replacement.
example (c : ℝ) (hc : 0<c) : ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ s : ℂ, 1<s.re →
      HasProd (fun q : Nat.Primes => lemma162ActualLocalSeries χ (lemma52PaperBetaOne D c)
        (lemma52PaperBetaTwo D c) q s)
        (lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma52PaperBetaTwo D c)
          (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s) := by
  obtain ⟨D₀,hD₀,h⟩ := lemma162_paper_actual_arithmetic_bridge c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ s hs
  simpa only [lemma162_paper_shift_one] using (((h D hD χ).2 (1:Fin 2)).2.2 s hs).2

-- The exceptional degree-zero coefficient is retained literally.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β γ : ℂ) (h2 : χ.evalNat 2=1) :
    lemma162TwoCoefficientArithmetic χ β γ 1 =
      lemma161PrimeFactor χ β lemma162PrimeTwo (1-γ)/2 := by
  change χ.chi (2:ZMod D)=1 at h2
  simp [lemma162TwoCoefficientArithmetic,lemma162PrimePowerPart,
    show ∃ r : ℕ, (1:ℕ)=2^r from ⟨0,by simp⟩,
    ArithmeticFunction.pmul_apply,lemma152DivisorKernelSum,lemma162TwoVarpiKernel,
    lemma162TwoNormalizer,h2,RealPrimitiveCharacter.evalNat]

-- Actual q=2 isolation, with no denominator F00₂.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re=0)
    (s : ℂ) (hs : 9/10≤s.re) (h2 : χ.evalNat 2=1) :
    lemma161Star χ β s = 2*lemma162OddMEulerProduct χ β 1 1 s := by
  simpa [lemma162TwoNormalizer,h2] using lemma162_star_odd_decomposition χ β hβ s hs

-- This witness remains explicitly conditional on the NOT-YET-PROVED corrected extraction.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) (β γ : ℂ) (hγ : γ≠0)
    (U V : ℂ → ℂ) (hU : ContinuousAt U 1) (hV : ContinuousAt V 1)
    (hbridge : ∀ s : ℂ, 1<s.re →
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s =
        V s*riemannZeta s^2*riemannZeta (s-γ)*dirichletLFunction χ s*dirichletLFunction χ (s-γ)^2)
    (hquot : ∀ s : ℂ, 1<s.re → U s =
      lemma162DirichletSeries χ β γ (lemma162GeneralMEulerProduct χ β) s /
        (riemannZeta s^3*dirichletLFunction χ s^3)) : U 1=0 :=
  lemma162_original_value_forced_zero χ hD γ hγ U V _ hU hV hbridge hquot

-- Coincident phases use a genuine convergent-series proof.
example (z : ℂ) (hz : ‖z‖<1) :
    HasSum (fun n : ℕ => lemma83LocalH2 1 1 n*lemma83LocalH3 1 1 1 n*z^n)
      ((1-3*z^2+2*z^3)/(1-z)^6) := by
  convert lemma162_h2_h3_hadamard_hasSum 1 1 1 1 1 z
    (by simpa using hz) (by simpa using hz) (by simpa using hz)
    (by simpa using hz) (by simpa using hz) (by simpa using hz) using 1
  congr 1 <;> ring

-- Exact ramification branch, retaining the actual nonzero phase parameter.
example (a u x : ℂ) (hx : 1-x≠0) :
    lemma162M00 a u 0 x=1 ∧ lemma162M01 a u 0 x=1 ∧
      lemma162M10 u 0 x=1 ∧ lemma162M11 0 x=1 := lemma162_ramified_factors a u x hx

end ZhangLS.Spec
