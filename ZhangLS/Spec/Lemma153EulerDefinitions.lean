import ZhangLS.Spec.Lemma153RatioBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

/-- Numerical small-shift conditions only; no analytic or Euler-product
conclusion is built into this structure. -/
structure Lemma153SmallParameters (β : Fin 2 → ℂ) (γ : ℂ) : Prop where
  beta_re : ∀ i, (β i).re = 0
  beta_small : ∀ i, ‖β i‖ ≤ 1/10
  gamma_re : γ.re = 0
  gamma_small : ‖γ‖ ≤ 1/10
  small_error : 10*lemma152CorrectionConstant*(‖β 0‖+‖β 1‖+‖γ‖) ≤ 1/2

noncomputable def lemma153Baseline {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (q : Nat.Primes) : ℂ :=
  lemma153BaseClosed ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
    (q.val:ℂ)⁻¹ (χ.evalNat q.val) (lemma32PrimeMonomial q.val (1-γ))

noncomputable def lemma153UnramifiedPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  let B := lemma153Baseline χ β γ q
  let lam := lemma152LambdaFactor χ β q.val 1
  let A := χ.evalNat q.val/(1-(q.val:ℂ)⁻¹)
  let y := lemma32PrimeMonomial q.val (1-γ)
  let K := lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) y
  lemma153ShiftedLocalCorrection B (B+lam*A*y*K) ((1-A*y)*K) K lam
    (χ.evalNat q.val*(q.val:ℂ)^γ) (lemma32PrimeMonomial q.val s)

/-- The ramified factor is kept exact. -/
noncomputable def lemma153PrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if q.val ∣ D then (1-lemma32PrimeMonomial q.val s)^2
  else lemma153UnramifiedPrimeFactor χ β γ q s

/-- Proposed repaired U, with normal convergence and the arithmetic bridge
proved separately rather than included in the definition. -/
noncomputable def lemma153EulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes, lemma153PrimeFactor χ β γ q s

end ZhangLS.Spec
