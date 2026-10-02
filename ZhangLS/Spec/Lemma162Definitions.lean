import ZhangLS.Spec.Lemma161Original
import ZhangLS.Spec.Lemma23ArithmeticCoefficients

/-! Literal Section16.13 data and frozen16.2 analytic target. No theorem
asserts the original or repaired target here. The family M must later be
constructed from the actual Section16 Dirichlet series. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def lemma162Varpi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (n : ℕ) : ℂ :=
  ∑ dl ∈ n.divisorsAntidiagonal,
    lemma161Lambda χ β dl.1 * (dl.1 : ℂ)^γ * χ.evalNat dl.2 *
      (M dl.1 dl.2 (1-γ) / lemma161Star χ β (1-γ))

noncomputable def lemma162NuChi {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ArithmeticFunction ℂ :=
  lemma23NuArithmeticFunction χ * lemma23CharacterArithmeticFunction χ

noncomputable def lemma162Coefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (n : ℕ) : ℂ :=
  lemma162Varpi χ β γ M n * lemma162NuChi χ n

noncomputable def lemma162DirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (s : ℂ) : ℂ :=
  LSeries (lemma162Coefficient χ β γ M) s

/-- The original unshifted analytic claim, explicitly frozen. -/
def Lemma162OriginalContinuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (U : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ U {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (lemma162Coefficient χ β γ M) s ∧
      U s * riemannZeta s^3 * dirichletLFunction χ s^3 =
        lemma162DirichletSeries χ β γ M s

/-- Candidate shifted continuation. This definition is not a proof. -/
def Lemma162ShiftedContinuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (U : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ U {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (lemma162Coefficient χ β γ M) s ∧
      U s * riemannZeta s^2 * riemannZeta (s-γ) *
        dirichletLFunction χ s * dirichletLFunction χ (s-γ)^2 =
          lemma162DirichletSeries χ β γ M s

@[simp] lemma lemma162_lambda_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) : lemma161Lambda χ β 1 = 1 := by simp [lemma161Lambda]

lemma lemma162_lambda_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) :
    lemma161Lambda χ β p = lemma161LambdaFactor χ β p 1 := by
  simp [lemma161Lambda,hp.primeFactors]

/-- The true degree-zero coefficient. In the χ(2)=1 branch it is not 1. -/
lemma lemma162_varpi_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) :
    lemma162Varpi χ β γ M 1 = M 1 1 (1-γ) / lemma161Star χ β (1-γ) := by
  simp [lemma162Varpi,RealPrimitiveCharacter.evalNat]

/-- No division by any individual Euler factor is used. -/
lemma lemma162_varpi_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (hp : p.Prime) :
    lemma162Varpi χ β γ M p =
      χ.evalNat p * (M 1 p (1-γ) / lemma161Star χ β (1-γ)) +
      lemma161LambdaFactor χ β p 1 * (p:ℂ)^γ *
        (M p 1 (1-γ) / lemma161Star χ β (1-γ)) := by
  unfold lemma162Varpi
  rw [Nat.sum_divisorsAntidiagonal (fun d l =>
    lemma161Lambda χ β d * (d:ℂ)^γ * χ.evalNat l *
      (M d l (1-γ) / lemma161Star χ β (1-γ)))]
  rw [hp.divisors,Finset.sum_pair (Ne.symm hp.ne_one)]
  simp [Nat.div_self hp.pos,lemma162_lambda_prime χ β hp,RealPrimitiveCharacter.evalNat]

end ZhangLS.Spec
