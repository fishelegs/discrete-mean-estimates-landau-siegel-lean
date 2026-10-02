import ZhangLS.Spec.Lemma82UniformThreshold
import ZhangLS.Spec.Lemma111SmoothedTent
import ZhangLS.Spec.PaperErrorScaleBudget

/-! Original Lemma 10.1, arXiv:2211.02515v1, pp. 53–55.
The decimal exponents are exact rationals. All constants precede the fixed
positive c′; only the modulus threshold may depend on c′. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

noncomputable def lemma101Cutoff (D : ℕ) (y a : ℝ) : ℝ :=
  lemma23PaperP D ^ a / y

/-- The actual finitely supported character sum in Lemma 10.1. The included
upper endpoint contributes zero, exactly as in the paper's tent (2.28). -/
noncomputable def lemma101Sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (y : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊lemma101Cutoff D y (63/125)⌋₊,
    χ.evalNat m / (m:ℂ)^(1-lemma82PaperBeta D c j) *
      (lemma111Tent (Real.log (y*(m:ℝ)) / Real.log (lemma23PaperP D)) : ℂ)

noncomputable def lemma101MainLower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (y : ℝ) : ℂ :=
  (500 * LDerivAtOne χ / (Real.log (lemma23PaperP D):ℂ)) *
    (-1-lemma82PaperBeta D c j * (Real.log (y / lemma23PaperP D^(1/2:ℝ)):ℂ))

noncomputable def lemma101MainUpper {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (y : ℝ) : ℂ :=
  (500 * LDerivAtOne χ / (Real.log (lemma23PaperP D):ℂ)) *
    (1-lemma82PaperBeta D c j * (Real.log (lemma23PaperP D^(63/125:ℝ) / y):ℂ))

def Lemma101Transition (D : ℕ) (y : ℝ) : Prop :=
  y ∈ Set.Ioc (lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D) (lemma23PaperP D^(1/2:ℝ)) ∪
    Set.Ioc (lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D) (lemma23PaperP D^(251/500:ℝ)) ∪
    Set.Ioo (lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D) (lemma23PaperP D^(63/125:ℝ))

def Lemma101Target : Prop :=
  ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ y : ℝ,
      (1≤y → y≤lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D →
        ‖lemma101Sum χ c j y‖ ≤ C * lemma56PaperT D^(-κ)) ∧
      (lemma23PaperP D^(1/2:ℝ)<y → y≤lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D →
        ‖lemma101Sum χ c j y-lemma101MainLower χ c j y‖ ≤ C * lemma23PaperL D^(-15:ℤ)) ∧
      (lemma23PaperP D^(251/500:ℝ)<y → y≤lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D →
        ‖lemma101Sum χ c j y-lemma101MainUpper χ c j y‖ ≤ C * lemma23PaperL D^(-15:ℤ)) ∧
      (Lemma101Transition D y → ‖lemma101Sum χ c j y‖ ≤ C * lemma23PaperL D^(-7:ℤ))

end ZhangLS.Spec
