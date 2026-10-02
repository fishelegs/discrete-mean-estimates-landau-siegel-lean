import ZhangLS.Spec.Lemma171DirichletSeries
import ZhangLS.Spec.Lemma52Product
import ZhangLS.Spec.Lemma56

/-!
# Section 7 coefficients and the faithful original Lemma 8.3 target

Source: arXiv:2211.02515v1, pp.32–34 and 46. The modified coefficient is the
actual supported infinite sum, and ξ is the actual divisor sum. The target
requires an analytic continuation agreeing with the Dirichlet series on the
convergence half-plane. It does not extend a totalized L-quotient by fiat.

Appendix A pp.101–103 contains inconsistent ξ/d/h/h₁ notation and an extra
λ(dh) prefactor. The definitions here follow Section 7, whose zero-shift
specialization agrees exactly with Π on p.46.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- The three shifts in (2.13), indexed cyclically by `Fin 3`. -/
noncomputable def lemma83PaperBeta (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  if j = 0 then lemma52PaperBetaOne D c else
  if j = 1 then lemma52PaperBetaTwo D c else lemma52PaperBetaThree D c

lemma lemma83_beta_re (D : ℕ) (c : ℝ) (j : Fin 3) :
    (lemma83PaperBeta D c j).re = 0 := by
  unfold lemma83PaperBeta
  split_ifs <;> simp [lemma52PaperBetaOne,lemma52PaperBetaTwo,lemma52PaperBetaThree]

/-- The coefficients of ζ(s+β), with the arithmetic-function zero convention. -/
noncomputable def lemma83PowerCoefficient (β : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ)^(-β), by simp⟩

lemma lemma83_power_coefficient_multiplicative (β : ℂ) :
    (lemma83PowerCoefficient β).IsMultiplicative := by
  refine ⟨by simp [lemma83PowerCoefficient], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · subst m; simp [lemma83PowerCoefficient]
  by_cases hn : n = 0
  · subst n; simp [lemma83PowerCoefficient]
  simp only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,
    if_neg hm,if_neg hn,if_neg (mul_ne_zero hm hn),Nat.cast_mul]
  exact Complex.natCast_mul_natCast_cpow m n (-β)

/-- κ is the actual Dirichlet-convolution coefficient of
ζ(s+β₁)ζ(s+β₂)ζ(s+β₃)/ζ(s). -/
noncomputable def lemma83Kappa (β : Fin 3 → ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
    (lemma83PowerCoefficient (β 0) * lemma83PowerCoefficient (β 1) *
      lemma83PowerCoefficient (β 2))

lemma lemma83_kappa_multiplicative (β : Fin 3 → ℂ) :
    (lemma83Kappa β).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (((lemma83_power_coefficient_multiplicative (β 0)).mul
      (lemma83_power_coefficient_multiplicative (β 1))).mul
        (lemma83_power_coefficient_multiplicative (β 2)))

@[simp] lemma lemma83_kappa_one (β : Fin 3 → ℂ) : lemma83Kappa β 1 = 1 :=
  (lemma83_kappa_multiplicative β).map_one

/-- Positive h supported on the primes of d, and coprime to m. -/
def Lemma83SupportedIndex (d m : ℕ) :=
  {h : ℕ // h ≠ 0 ∧ h.primeFactors ⊆ d.primeFactors ∧ h.Coprime m}

/-- The actual κ̃(d;m,s) on p.32. Convergence is a separate obligation. -/
noncomputable def lemma83ModifiedKappa (β : Fin 3 → ℂ) (d m : ℕ) (s : ℂ) : ℂ :=
  ∑' h : Lemma83SupportedIndex d m,
    lemma83Kappa β (d * h.val) / (h.val : ℂ)^s

/-- The local factor in λ(m,s), including all three shifted denominators. -/
noncomputable def lemma83LambdaFactor (β : Fin 3 → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  ((1 - (q : ℂ)^(-s-β 0)) * (1 - (q : ℂ)^(-s-β 1)) *
    (1 - (q : ℂ)^(-s-β 2))) / (1 - (q : ℂ)^(-s))

noncomputable def lemma83Lambda (β : Fin 3 → ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  ∏ q ∈ m.primeFactors, lemma83LambdaFactor β q s

/-- λ̃₀ⱼ(n,dr) on p.33; primes dividing dr are omitted. -/
noncomputable def lemma83ModifiedLambda (β : Fin 3 → ℂ)
    (j : Fin 3) (n m : ℕ) : ℂ :=
  ∏ q ∈ n.primeFactors.filter (fun q => ¬ q ∣ m),
    lemma83LambdaFactor β q (1 - β j)

/-- ξ₀ⱼ(n;d,r) exactly as defined on p.33. -/
noncomputable def lemma83Xi (β : Fin 3 → ℂ) (j : Fin 3) (n d r : ℕ) : ℂ :=
  lemma83ModifiedLambda β j n (d*r) *
    ∑ a ∈ n.divisorsAntidiagonal.filter (fun a => a.2.Coprime r),
      lemma83ModifiedKappa β a.1 (d*r*a.2) (1-β j) *
        (ArithmeticFunction.moebius a.2 : ℂ) *
          (a.2 : ℂ)^(1-β j) / (Nat.totient a.2 : ℂ)

/-- The actual ξ Dirichlet series, used only with an explicit convergence proof. -/
noncomputable def lemma83XiDirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) (s : ℂ) : ℂ :=
  LSeries (fun n => χ.evalNat n * lemma83Xi β j n d r) s

/-- Π(d,r), without division by any potentially vanishing numerator factor. -/
noncomputable def lemma83Pi {D : ℕ} (χ : RealPrimitiveCharacter D) (d r : ℕ) : ℂ :=
  (∏ q ∈ (d*r).primeFactors, (1 - χ.evalNat q / (q : ℂ))⁻¹) *
    ∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ r),
      (1 - (q : ℂ)⁻¹ - χ.evalNat q / (q : ℂ)) / (1 - (q : ℂ)⁻¹)

/-- One actual continuation, together with its identity in the genuine
convergence region. No assertion is made about L-quotients at their zeros. -/
def Lemma83Continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) (U : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ U {s : ℂ | 9/10 < s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (fun n => χ.evalNat n * lemma83Xi β j n d r) s ∧
      U s * dirichletLFunction χ (s + β (j+1)) *
        dirichletLFunction χ (s + β (j+2)) =
      dirichletLFunction χ s * lemma83XiDirichletSeries χ β j d r s

/-- Original 8.3, including positive d,r, strict dr cutoff, the whole half-plane,
closed small-shift disc, absolute (not relative) error, and uniform quantifiers.
The shift parameter c is fixed before the asymptotic threshold. -/
def Lemma83Target : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3, ∀ d r : ℕ, 0 < d → 0 < r →
        (d*r : ℝ) < lemma23PaperP D * lemma56PaperT D ^ (-2 : ℤ) →
        ∃ U : ℂ → ℂ,
          Lemma83Continuation χ (lemma83PaperBeta D c) j d r U ∧
          (∀ s : ℂ, 9/10 < s.re →
            ‖U s‖ < C * ∏ q ∈ (d*r).primeFactors,
              (1 + C * (q : ℝ)^(-s.re))) ∧
          (∀ s : ℂ, ‖s-1‖ ≤ 5 * lemma44PaperAlpha D →
            ‖U s - lemma83Pi χ d r‖ ≤ C * lemma23PaperL D ^ (-8 : ℤ))

end ZhangLS.Spec
