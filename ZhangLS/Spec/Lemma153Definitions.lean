import ZhangLS.Spec.Lemma152LocalSeries
import ZhangLS.Spec.Lemma34DivisorFunction

/-! Exact Section 15.3 definitions. The argument `M` is the Section 15 M₁ family,
not an invented Euler correction. This interface intentionally does not claim
that every family `M` has the required analytic continuation or nonzero value. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

/-- Equation (15.19), before a separately proved Euler-ratio bridge. -/
noncomputable def lemma153Varpi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (n : ℕ) : ℂ :=
  ∑ dl ∈ n.divisorsAntidiagonal,
    lemma152Lambda χ β dl.1 * (dl.1 : ℂ)^γ * χ.evalNat dl.2 *
      (M dl.1 dl.2 (1-γ) / M 1 1 (1-γ))

/-- The actual χ(n)τ₂(n)varpi₁ⱼ(n) Dirichlet coefficient. -/
noncomputable def lemma153Coefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (n : ℕ) : ℂ :=
  χ.evalNat n * (lemma34Tau 2 n : ℂ) * lemma153Varpi χ β γ M n

noncomputable def lemma153DirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (s : ℂ) : ℂ :=
  LSeries (lemma153Coefficient χ β γ M) s

/-- Literal original Lemma 15.3 continuation, not claimed in this file. -/
def Lemma153OriginalContinuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (U : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ U {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (lemma153Coefficient χ β γ M) s ∧
      U s * riemannZeta s ^ 2 * dirichletLFunction χ s ^ 2 =
        lemma153DirichletSeries χ β γ M s

/-- Corrected extraction: the genuine prime term requires L(s−βⱼ,χ)².
Its eventual proof must include summability and the arithmetic Euler bridge. -/
def Lemma153ShiftedContinuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (U : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ U {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (lemma153Coefficient χ β γ M) s ∧
      U s * riemannZeta s ^ 2 * dirichletLFunction χ (s-γ) ^ 2 =
        lemma153DirichletSeries χ β γ M s

@[simp] lemma lemma153_lambda_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) : lemma152Lambda χ β 1 = 1 := by simp [lemma152Lambda]

lemma lemma153_lambda_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : p.Prime) :
    lemma152Lambda χ β p = lemma152LambdaFactor χ β p 1 := by
  simp [lemma152Lambda,hp.primeFactors]

lemma lemma153_varpi_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hM : M 1 1 (1-γ) ≠ 0) : lemma153Varpi χ β γ M 1 = 1 := by
  simp [lemma153Varpi,RealPrimitiveCharacter.evalNat,hM]

/-- Exact prime coefficient from the original divisor sum, with no analytic
estimate or main lemma assumed. The two ratios are retained explicitly. -/
lemma lemma153_varpi_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (hp : p.Prime) :
    lemma153Varpi χ β γ M p =
      χ.evalNat p * (M 1 p (1-γ) / M 1 1 (1-γ)) +
      lemma152LambdaFactor χ β p 1 * (p:ℂ)^γ *
        (M p 1 (1-γ) / M 1 1 (1-γ)) := by
  unfold lemma153Varpi
  rw [Nat.sum_divisorsAntidiagonal (fun d l =>
    lemma152Lambda χ β d * (d:ℂ)^γ * χ.evalNat l *
      (M d l (1-γ) / M 1 1 (1-γ)))]
  rw [hp.divisors]
  rw [Finset.sum_pair (Ne.symm hp.ne_one)]
  simp [Nat.div_self hp.pos,lemma153_lambda_prime χ β hp,RealPrimitiveCharacter.evalNat]

end ZhangLS.Spec
