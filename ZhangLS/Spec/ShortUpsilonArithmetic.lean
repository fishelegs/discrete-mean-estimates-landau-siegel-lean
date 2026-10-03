import ZhangLS.Spec.Lemma36CoefficientMajorant
import ZhangLS.Spec.Lemma83LocalAgreement
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Lemma34TauProduct
import ZhangLS.Spec.Lemma31RealCoefficients

/-! Exact actual short-υ arithmetic. No coprimality with D is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open ArithmeticFunction Finset
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation

@[simp] lemma shortUpsilon_sub_apply (f g : ArithmeticFunction ℂ) (n : ℕ) :
    (f-g) n = f n-g n := by
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]

theorem shortUpsilon_character_inverse {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma23CharacterMoebiusArithmeticFunction χ * lemma23CharacterArithmeticFunction χ = 1 := by
  rw [mul_comm]
  have hseq := DirichletCharacter.convolution_mul_moebius χ.chi
  have hseq' : (lemma23CharacterArithmeticFunction χ : ℕ → ℂ) ⍟
      (lemma23CharacterMoebiusArithmeticFunction χ : ℕ → ℂ) = δ := by
    calc
      _ = (fun n : ℕ => χ.chi n) ⍟ (fun n : ℕ => χ.chi n * (μ n : ℂ)) := by
        apply LSeries.convolution_congr
        · intro n hn
          simp [lemma23CharacterArithmeticFunction, toArithmeticFunction, hn]
        · intro n hn
          simp [lemma23CharacterMoebiusArithmeticFunction, toArithmeticFunction, hn]
      _ = _ := hseq
  rw [ArithmeticFunction.coe_mul, ← ArithmeticFunction.one_eq_delta] at hseq'
  exact ArithmeticFunction.coe_inj.mp hseq'

theorem shortUpsilon_mul_character_eq_moebius {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma23UpsilonArithmeticFunction χ * lemma23CharacterArithmeticFunction χ =
      (μ : ArithmeticFunction ℂ) := by
  rw [lemma23UpsilonArithmeticFunction, mul_assoc, shortUpsilon_character_inverse, mul_one]

noncomputable def shortUpsilonFourfold {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) : ArithmeticFunction ℂ :=
  lemma23CharacterArithmeticFunction χ *
    (lemma83PowerCoefficient (β 0) * lemma83PowerCoefficient (β 1) *
      lemma83PowerCoefficient (β 2))

theorem shortUpsilon_kappa_eq_fivefold {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) :
    lemma83Kappa β = lemma23UpsilonArithmeticFunction χ * shortUpsilonFourfold χ β := by
  rw [shortUpsilonFourfold, ← mul_assoc, shortUpsilon_mul_character_eq_moebius]
  rfl

theorem shortUpsilon_norm_prime_power_le_nu {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (e : ℕ) :
    ‖lemma23UpsilonArithmeticFunction χ (p^e)‖ ≤ ‖lemma23NuArithmeticFunction χ (p^e)‖ := by
  by_cases h0 : e = 0
  · subst e
    simp [(lemma36_upsilon_multiplicative χ).map_one, lemma31_actual_nu_one]
  by_cases h1 : e = 1
  · subst e
    have hn : lemma23NuArithmeticFunction χ p = 1+χ.evalNat p := by
      simpa [Finset.sum_range_succ] using lemma31_actual_nu_prime_power χ hp 1
    rw [pow_one, lemma36_upsilon_prime χ hp, norm_neg, hn]
  by_cases h2 : e = 2
  · subst e
    rw [lemma36_upsilon_prime_square χ hp, lemma31_actual_nu_prime_power χ hp]
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p : ZMod D) with hc | hc | hc
    all_goals
      change χ.evalNat p = _ at hc
      norm_num [hc, Finset.sum_range_succ]
  have he : e = (e-3)+3 := by omega
  rw [he, lemma36_upsilon_prime_power_ge_three χ hp, norm_zero]
  exact norm_nonneg _

theorem shortUpsilon_norm_le_nu {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23UpsilonArithmeticFunction χ n‖ ≤ ‖lemma23NuArithmeticFunction χ n‖ := by
  by_cases hn : n = 0
  · subst n; simp
  · have hU := lemma36_norm_arithmetic_multiplicative _ (lemma36_upsilon_multiplicative χ)
    have hN := lemma36_norm_arithmetic_multiplicative _ (lemma31_actual_nu_multiplicative χ)
    change lemma36NormArithmeticFunction (lemma23UpsilonArithmeticFunction χ) n ≤
      lemma36NormArithmeticFunction (lemma23NuArithmeticFunction χ) n
    rw [hU.multiplicative_factorization _ hn, hN.multiplicative_factorization _ hn]
    simp only [Finsupp.prod, lemma36_norm_arithmetic_apply]
    apply Finset.prod_le_prod
    · intro p hp; exact norm_nonneg _
    · intro p hp
      exact shortUpsilon_norm_prime_power_le_nu χ (Nat.prime_of_mem_primeFactors hp) _

theorem shortUpsilon_norm_le_nu_real {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23UpsilonArithmeticFunction χ n‖ ≤ (lemma23NuArithmeticFunction χ n).re := by
  change _ ≤ lemma31NuReal χ n
  rw [lemma31_nu_real_eq_norm]
  exact shortUpsilon_norm_le_nu χ n

/-- Only the υ factor is cut at D^4. -/
noncomputable def shortUpsilon {D : ℕ} (χ : RealPrimitiveCharacter D) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ D^4 then lemma23UpsilonArithmeticFunction χ n else 0, by simp⟩

noncomputable def shortUpsilonKappa {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) : ArithmeticFunction ℂ := shortUpsilon χ * shortUpsilonFourfold χ β

@[simp] theorem shortUpsilon_apply {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    shortUpsilon χ n = if n ≤ D^4 then lemma23UpsilonArithmeticFunction χ n else 0 := rfl

/-- The total product equals n even after shortening: no rectangular factor cutoff. -/
theorem shortUpsilon_kappa_divisor_formula {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (n : ℕ) :
    shortUpsilonKappa χ β n = ∑ q ∈ n.divisorsAntidiagonal with q.1 ≤ D^4,
      lemma23UpsilonArithmeticFunction χ q.1 * shortUpsilonFourfold χ β q.2 := by
  rw [shortUpsilonKappa, ArithmeticFunction.mul_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [shortUpsilon_apply]
  split_ifs <;> simp_all


/-- Full nested factor expansion; each antidiagonal retains its exact product. -/
theorem shortUpsilon_kappa_factor_expansion {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (n : ℕ) :
    shortUpsilonKappa χ β n = ∑ q ∈ n.divisorsAntidiagonal with q.1 ≤ D^4,
      lemma23UpsilonArithmeticFunction χ q.1 *
        (∑ r ∈ q.2.divisorsAntidiagonal, lemma23CharacterArithmeticFunction χ r.1 *
          (∑ t ∈ r.2.divisorsAntidiagonal,
            (∑ u ∈ t.1.divisorsAntidiagonal,
              lemma83PowerCoefficient (β 0) u.1 * lemma83PowerCoefficient (β 1) u.2) *
            lemma83PowerCoefficient (β 2) t.2)) := by
  simp only [shortUpsilon_kappa_divisor_formula, shortUpsilonFourfold,
    ArithmeticFunction.mul_apply]

theorem shortUpsilon_kappa_residual_convolution {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) :
    lemma83Kappa β - shortUpsilonKappa χ β =
      (lemma23UpsilonArithmeticFunction χ - shortUpsilon χ) * shortUpsilonFourfold χ β := by
  rw [shortUpsilon_kappa_eq_fivefold χ β, shortUpsilonKappa, sub_mul]

theorem shortUpsilon_kappa_residual_formula {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (n : ℕ) :
    lemma83Kappa β n - shortUpsilonKappa χ β n =
      ∑ q ∈ n.divisorsAntidiagonal with D^4 < q.1,
        lemma23UpsilonArithmeticFunction χ q.1 * shortUpsilonFourfold χ β q.2 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (shortUpsilon_kappa_residual_convolution χ β)
  change (lemma83Kappa β - shortUpsilonKappa χ β) n =
    ((lemma23UpsilonArithmeticFunction χ - shortUpsilon χ) * shortUpsilonFourfold χ β) n at h
  rw [ArithmeticFunction.mul_apply] at h
  rw [Finset.sum_filter]
  simpa only [shortUpsilon_sub_apply] using h.trans (by
    apply Finset.sum_congr rfl
    intro q hq
    simp only [shortUpsilon_sub_apply, shortUpsilon_apply]
    split_ifs <;> simp_all <;> omega)

lemma shortUpsilon_convolution_norm_le_tau (f g : ArithmeticFunction ℂ) (k l : ℕ)
    (hf : ∀ n, ‖f n‖ ≤ (lemma34Tau k n : ℝ))
    (hg : ∀ n, ‖g n‖ ≤ (lemma34Tau l n : ℝ)) (n : ℕ) :
    ‖(f*g) n‖ ≤ (lemma34Tau (k+l) n : ℝ) := by
  calc
    _ ≤ ∑ q ∈ n.divisorsAntidiagonal, ‖f q.1‖ * ‖g q.2‖ := by
      simpa only [ArithmeticFunction.mul_apply, norm_mul] using
        norm_sum_le n.divisorsAntidiagonal (fun q => f q.1*g q.2)
    _ ≤ ∑ q ∈ n.divisorsAntidiagonal,
        (lemma34Tau k q.1 : ℝ)*(lemma34Tau l q.2 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [lemma34Tau, pow_add, ArithmeticFunction.mul_apply, Nat.cast_sum, Nat.cast_mul]

lemma shortUpsilon_power_norm_le_tau_one (β : ℂ) (hβ : β.re = 0) (n : ℕ) :
    ‖lemma83PowerCoefficient β n‖ ≤ (lemma34Tau 1 n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp [lemma34Tau]
  · simp [lemma83PowerCoefficient, hn, lemma34Tau,
      lemma83_cpow_shift_norm (Nat.pos_of_ne_zero hn) β hβ]

lemma shortUpsilon_character_norm_le_tau_one {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23CharacterArithmeticFunction χ n‖ ≤ (lemma34Tau 1 n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp [lemma34Tau]
  · simpa [lemma23CharacterArithmeticFunction, toArithmeticFunction, hn, lemma34Tau] using
      χ.chi.norm_le_one (n : ZMod D)

theorem shortUpsilon_fourfold_norm_le_tau_four {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0) (n : ℕ) :
    ‖shortUpsilonFourfold χ β n‖ ≤ (lemma34Tau 4 n : ℝ) := by
  apply shortUpsilon_convolution_norm_le_tau _ _ 1 3
    (shortUpsilon_character_norm_le_tau_one χ)
  intro m
  apply shortUpsilon_convolution_norm_le_tau _ _ 2 1
    (fun m => shortUpsilon_convolution_norm_le_tau _ _ 1 1
      (shortUpsilon_power_norm_le_tau_one _ (hβ 0))
      (shortUpsilon_power_norm_le_tau_one _ (hβ 1)) m)
    (shortUpsilon_power_norm_le_tau_one _ (hβ 2))

theorem shortUpsilon_kappa_norm_le_tau_six {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re = 0) (n : ℕ) :
    ‖shortUpsilonKappa χ β n‖ ≤ (lemma34Tau 6 n : ℝ) := by
  apply shortUpsilon_convolution_norm_le_tau _ _ 2 4 _
    (shortUpsilon_fourfold_norm_le_tau_four χ β hβ)
  intro m
  rw [shortUpsilon_apply, lemma34_tau2_eq_divisor_card]
  split_ifs
  · exact lemma23UpsilonArithmeticFunction_norm_le_card_divisors χ m
  · simp

end ZhangLS.Spec
