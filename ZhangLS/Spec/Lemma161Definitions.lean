import ZhangLS.Spec.Lemma152KappaLocal

/-! Exact Section 16 arithmetic definitions, arXiv:2211.02515v1 pp.89–92.
The supported sum and divisor convolution are the actual paper data.
The analytic continuation will be constructed, not assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def lemma161Kappa (β : ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) * lemma83PowerCoefficient β

lemma lemma161_kappa_multiplicative (β : ℂ) : (lemma161Kappa β).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (lemma83_power_coefficient_multiplicative β)

@[simp] lemma lemma161_kappa_one (β : ℂ) : lemma161Kappa β 1 = 1 :=
  (lemma161_kappa_multiplicative β).map_one

noncomputable def lemma161ModifiedKappa {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d r : ℕ) (s : ℂ) : ℂ :=
  ∑' h : Lemma83SupportedIndex d r,
    lemma161Kappa β (d*h.val) * χ.evalNat h.val / (h.val : ℂ)^s

noncomputable def lemma161LambdaFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  (1 - χ.evalNat q * (q : ℂ)^(-s-β)) / (1 - χ.evalNat q * (q : ℂ)^(-s))

noncomputable def lemma161Lambda {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (n : ℕ) : ℂ :=
  ∏ q ∈ n.primeFactors, lemma161LambdaFactor χ β q 1

noncomputable def lemma161ModifiedLambda {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (n d : ℕ) : ℂ :=
  ∏ q ∈ n.primeFactors.filter (fun q => ¬ q ∣ d), lemma161LambdaFactor χ β q 1

noncomputable def lemma161Xi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (n d l : ℕ) : ℂ :=
  ∑ a ∈ n.divisorsAntidiagonal.filter (fun a => a.2.Coprime l),
    (ArithmeticFunction.moebius a.2 : ℂ) * χ.evalNat a.2 * (a.2 : ℂ) /
      (Nat.totient a.2 : ℂ) * lemma161ModifiedKappa χ β a.1 (d*a.2) 1

noncomputable def lemma161Coefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l n : ℕ) : ℂ :=
  lemma161ModifiedLambda χ β n d * lemma161Xi χ β n d l

noncomputable def lemma161DirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (s : ℂ) : ℂ :=
  LSeries (lemma161Coefficient χ β d l) s

/-- Agreement on the absolutely convergent half-plane, with an independently
proved extension across zeta zeros and poles; there are no totalized quotients. -/
def Lemma161Continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (M : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ M {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (lemma161Coefficient χ β d l) s ∧
      M s * riemannZeta (s+β) =
        riemannZeta s * dirichletLFunction χ s * lemma161DirichletSeries χ β d l s

noncomputable def lemma161MainFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) : ℂ :=
  (1-χ.evalNat q.val/(q.val:ℂ))⁻¹ * (1-χ.evalNat q.val/(q.val-1:ℕ))

/-- The literal two cases of original Lemma16.1. In the second case the
q=2 factor is replaced by 2 rather than canceled by division. -/
noncomputable def lemma161MainTerm {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  if χ.evalNat 2 = 1 then
    2 * ∏' q : {q : Nat.Primes // 2 < q.val}, lemma161MainFactor χ q.val
  else ∏' q : Nat.Primes, lemma161MainFactor χ q

end ZhangLS.Spec
