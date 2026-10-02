import ZhangLS.Spec.Lemma83KappaPrimePower
import ZhangLS.Spec.Lemma83SupportedPrimePower
/-!
# Section 15 actual arithmetic data

The two shifts are exactly the shared paper shifts (2.13). The modified
coefficient is the actual supported infinite sum (15.9), not a product
chosen to make an Euler identity true. Convergence is proved separately.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def lemma152PaperBeta (D : ℕ) (c : ℝ) (j : Fin 2) : ℂ :=
  if j = 0 then lemma52PaperBetaOne D c else lemma52PaperBetaTwo D c

lemma lemma152_beta_re (D : ℕ) (c : ℝ) (j : Fin 2) :
    (lemma152PaperBeta D c j).re = 0 := by
  unfold lemma152PaperBeta
  split_ifs <;> simp [lemma52PaperBetaOne,lemma52PaperBetaTwo]

/-- Coefficient of ζ(s+β₁)ζ(s+β₂)/ζ(s), Section 15 p.81. -/
noncomputable def lemma152Kappa (β : Fin 2 → ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
    (lemma83PowerCoefficient (β 0) * lemma83PowerCoefficient (β 1))

lemma lemma152_kappa_multiplicative (β : Fin 2 → ℂ) :
    (lemma152Kappa β).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    ((lemma83_power_coefficient_multiplicative (β 0)).mul
      (lemma83_power_coefficient_multiplicative (β 1)))

@[simp] lemma lemma152_kappa_one (β : Fin 2 → ℂ) : lemma152Kappa β 1 = 1 :=
  (lemma152_kappa_multiplicative β).map_one

/-- The actual χ-weighted supported sum in (15.9). -/
noncomputable def lemma152ModifiedKappa {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d r : ℕ) (s : ℂ) : ℂ :=
  ∑' h : Lemma83SupportedIndex d r,
    lemma152Kappa β (d*h.val) * χ.evalNat h.val / (h.val : ℂ)^s

/-- The exact local factor of (15.10), including χ at ramified primes. -/
noncomputable def lemma152LambdaFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  ((1 - χ.evalNat q * (q : ℂ)^(-s-β 0)) *
    (1 - χ.evalNat q * (q : ℂ)^(-s-β 1))) /
      (1 - χ.evalNat q * (q : ℂ)^(-s))

noncomputable def lemma152Lambda {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (n : ℕ) : ℂ :=
  ∏ q ∈ n.primeFactors, lemma152LambdaFactor χ β q 1

noncomputable def lemma152ModifiedLambda {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (n d : ℕ) : ℂ :=
  ∏ q ∈ n.primeFactors.filter (fun q => ¬ q ∣ d), lemma152LambdaFactor χ β q 1

/-- ξ₁ of (15.13), with its original coprimality restriction. -/
noncomputable def lemma152Xi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (n d l : ℕ) : ℂ :=
  ∑ a ∈ n.divisorsAntidiagonal.filter (fun a => a.2.Coprime l),
    (ArithmeticFunction.moebius a.2 : ℂ) * χ.evalNat a.2 * (a.2 : ℂ) /
      (Nat.totient a.2 : ℂ) * lemma152ModifiedKappa χ β a.1 (d*a.2) 1

noncomputable def lemma152Coefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l n : ℕ) : ℂ :=
  lemma152ModifiedLambda χ β n d * lemma152Xi χ β n d l

noncomputable def lemma152DirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) (s : ℂ) : ℂ :=
  LSeries (lemma152Coefficient χ β d l) s

/-- Agreement with the actual Dirichlet series only in Re s>1, alongside
an independently proved holomorphic extension. This avoids totalized quotients
at the zeros and poles of the zeta and L functions. -/
def Lemma152Continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) (M : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ M {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (lemma152Coefficient χ β d l) s ∧
      M s * riemannZeta (s+β 0) * riemannZeta (s+β 1) =
        riemannZeta s * dirichletLFunction χ s * lemma152DirichletSeries χ β d l s

/-- The product in original Lemma 15.2, retaining the ramification exclusion. -/
noncomputable def lemma152MainTerm {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  ∏' q : {q : Nat.Primes // ¬ q.val ∣ D},
    (1-χ.evalNat q.val.val * (q.val.val : ℂ)^(-2 : ℤ)) /
      (1-(q.val.val : ℂ)^(-2 : ℤ))

end ZhangLS.Spec
