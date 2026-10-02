import ZhangLS.Spec.Lemma121PhaseAudit

/-! Exact arithmetic data of original Lemma 12.1, arXiv:2211.02515v1.
The strict support of κ13 is retained at both endpoints. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

noncomputable def lemma121P1 (D : ℕ) : ℝ := lemma23PaperP D^(63/125:ℝ)
noncomputable def lemma121P2 (D : ℕ) : ℝ :=
  lemma23PaperP D^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ)
noncomputable def lemma121PDoublePrimeOne (D : ℕ) : ℝ :=
  lemma23PaperP D^(62/125:ℝ)*(D:ℝ)*lemma51PaperT0 D
noncomputable def lemma121PDoublePrimeTwo (D : ℕ) : ℝ :=
  lemma23PaperP D^(1/2:ℝ)*(D:ℝ)*lemma51PaperT0 D

/-- Generic form of the exact compactly supported κ13 weight. Q is log P1. -/
noncomputable def lemma121Kernel (A B Q : ℝ) (b : ℂ) (n : ℝ) : ℂ :=
  if A<n ∧ n<B then (1/(Q:ℂ))*((n/A:ℝ):ℂ)^(-b)*(Real.log (n/A):ℂ) else 0

noncomputable def lemma121Kappa13 (D : ℕ) (n : ℝ) : ℂ :=
  lemma121Kernel (lemma121PDoublePrimeOne D) (lemma121PDoublePrimeTwo D)
    (Real.log (lemma121P1 D)) (lemma82SmoothingBeta D 6) n

/-- Actual finite sum, with original strict upper cutoff. The lower cutoff
is enforced by κ13; no endpoint term has been discarded. -/
noncomputable def lemma121Sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d : ℝ) : ℂ :=
  ∑ n ∈ lemma82StrictCutoff (lemma121PDoublePrimeTwo D/d),
    χ.evalNat n * lemma121Kappa13 D (d*(n:ℝ)) /
      (n:ℂ)^(1-lemma82PaperBeta D c j)

/-- Exact pre-linearization phase main term in the original proof. -/
noncomputable def lemma121ExactMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d : ℝ) : ℂ :=
  LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
    lemma121Phase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
      (Real.log (d/lemma121PDoublePrimeOne D))

/-- Printed linear main term, excluding the printed normalized ε. -/
noncomputable def lemma121PrintedMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d : ℝ) : ℂ :=
  LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
    lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
      (Real.log (d/lemma121PDoublePrimeOne D))

/-- Original high-range target, frozen separately because the printed
transition symbol α1 is not defined in the supplied source. This proposition
preserves the exact shared c′, natural d, range, normalized error and strict
10^-5 bound. No theorem in this work claims this proposition. -/
def Lemma121PrintedHighTarget : Prop :=
  ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℕ,
      lemma121PDoublePrimeOne D<(d:ℝ) → (d:ℝ)<lemma121P2 D →
      ∃ ε : ℂ, ‖ε‖<(1:ℝ)/100000 ∧
        lemma121Sum χ c j d = LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
          (lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
            (Real.log ((d:ℝ)/lemma121PDoublePrimeOne D))+ε)

/-- Full printed target with the source's undefined α1 explicitly exposed as
an unresolved parameter, rather than silently assigned a meaning. This is a
statement freeze only; no theorem here proves it. -/
def Lemma121PrintedTarget (alphaOne : ℕ → ℝ) : Prop :=
  ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℕ,
      (1≤d → (d:ℝ)≤lemma121PDoublePrimeOne D/lemma56PaperT D →
        ‖lemma121Sum χ c j d‖≤C*lemma56PaperT D^(-κ)) ∧
      (lemma121PDoublePrimeOne D/lemma56PaperT D<(d:ℝ) →
        (d:ℝ)≤lemma121PDoublePrimeOne D → ‖lemma121Sum χ c j d‖≤C*alphaOne D) ∧
      (lemma121PDoublePrimeOne D<(d:ℝ) → (d:ℝ)<lemma121P2 D →
        ∃ ε : ℂ, ‖ε‖<(1:ℝ)/100000 ∧
          lemma121Sum χ c j d = LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
            (lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
              (Real.log ((d:ℝ)/lemma121PDoublePrimeOne D))+ε))

lemma lemma121_kernel_lower_endpoint (A B Q : ℝ) (b : ℂ) :
    lemma121Kernel A B Q b A=0 := by simp [lemma121Kernel]
lemma lemma121_kernel_upper_endpoint (A B Q : ℝ) (b : ℂ) :
    lemma121Kernel A B Q b B=0 := by simp [lemma121Kernel]

end ZhangLS.Spec
