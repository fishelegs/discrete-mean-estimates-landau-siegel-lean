import ZhangLS.Spec.Lemma31
import ZhangLS.Spec.RealAxisLFunction

/-!
# Lemma 17.1: faithful target, actual coefficients, and strict cutoff

Source: arXiv:2211.02515v1, p. 96 and pp. 108–109. The uniform o(1) target is proved in `Lemma171.lean`. The endpoint bridge is
proved exactly here; no final estimate is assumed.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- The actual nonnegative square coefficient, without the divisor weight of 3.2. -/
noncomputable def lemma171Coefficient {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) : ℝ :=
  ‖lemma23NuArithmeticFunction χ n‖ ^ 2

/-- The paper's strict short harmonic sum. -/
noncomputable def lemma171ShortHarmonicSum {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (D ^ 4), lemma171Coefficient χ n / (n : ℝ)

/-- The actual constant a appearing in the statement of Lemma 17.1. -/
noncomputable def lemma171MainTerm {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  (6 / Real.pi ^ 2) * realLDerivAtOne χ ^ 2 *
    ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

/-- An explicit actual error, not a freely chosen residual or an assumption. -/
noncomputable def lemma171Error {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  lemma171ShortHarmonicSum χ - lemma171MainTerm χ

/-- Uniform `o(1)` in the original normalized hypothesis (A).
The threshold precedes both the modulus and the character. -/
def Lemma171Target : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → |lemma171Error χ| < ε

lemma lemma171_coefficient_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    0 ≤ lemma171Coefficient χ n := sq_nonneg _

lemma lemma171_coefficient_eq_real_square {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma171Coefficient χ n = (lemma23NuArithmeticFunction χ n).re ^ 2 := by
  unfold lemma171Coefficient
  rw [← lemma31_nu_real_eq_norm]
  rfl

lemma lemma171_coefficient_complex {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (lemma171Coefficient χ n : ℂ) = lemma23NuArithmeticFunction χ n ^ 2 := by
  rw [lemma171_coefficient_eq_real_square,Complex.ofReal_pow]
  congr 1
  apply Complex.ext <;> simp [lemma31_nu_im_zero]

lemma lemma171_coefficient_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma171Coefficient χ 1 = 1 := by
  simp [lemma171Coefficient,lemma31_actual_nu_one]

lemma lemma171_coefficient_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D)
    (h : m.Coprime n) :
    lemma171Coefficient χ (m*n) = lemma171Coefficient χ m * lemma171Coefficient χ n := by
  simp only [lemma171Coefficient,
    (lemma31_actual_nu_multiplicative χ).map_mul_of_coprime h,norm_mul,mul_pow]

/-- Every prime divisor of D is ramified, so ν(D^k)=1 for every k, including k=0. -/
lemma lemma171_nu_modulus_power {D : ℕ} (χ : RealPrimitiveCharacter D) (k : ℕ) :
    lemma23NuArithmeticFunction χ (D^k) = 1 := by
  rw [(lemma31_actual_nu_multiplicative χ).multiplicative_factorization _
    (pow_ne_zero k χ.modulus_ne_zero)]
  simp only [Finsupp.prod]
  apply Finset.prod_eq_one
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ D := hpr.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp)
  rw [lemma31_actual_nu_prime_power χ hpr,
    χ.evalNat_eq_zero_of_dvd_modulus hpd hpr.ne_one]
  simp [zero_pow_eq]

lemma lemma171_coefficient_modulus_power {D : ℕ} (χ : RealPrimitiveCharacter D) (k : ℕ) :
    lemma171Coefficient χ (D^k) = 1 := by
  simp [lemma171Coefficient,lemma171_nu_modulus_power]

/-- Exact endpoint correction needed when using Lemma 3.1's tail D⁴<n. -/
lemma lemma171_strict_cutoff_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Icc 1 (D^4), lemma171Coefficient χ n / (n : ℝ)) =
      lemma171ShortHarmonicSum χ + (D : ℝ)^(-4 : ℤ) := by
  have hD : 1 ≤ D^4 := Nat.one_le_pow 4 D χ.modulus_pos
  have hh := Finset.sum_Ico_add_eq_sum_Icc
    (f := fun n : ℕ => lemma171Coefficient χ n/(n : ℝ)) hD
  dsimp only at hh
  rw [lemma171_coefficient_modulus_power, Nat.cast_pow] at hh
  simpa only [lemma171ShortHarmonicSum,zpow_neg,zpow_ofNat,one_div] using hh.symm

lemma lemma171_short_sum_eq_paper {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma171ShortHarmonicSum χ =
      ∑ n ∈ Finset.Ico 1 (D^4), (lemma23NuArithmeticFunction χ n).re^2/(n : ℝ) := by
  simp only [lemma171ShortHarmonicSum,lemma171_coefficient_eq_real_square]

/-- The formal target expands to the paper's actual sum and actual main term. -/
lemma lemma171_target_iff_paper : Lemma171Target ↔
    ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ →
          |(∑ n ∈ Finset.Ico 1 (D^4), (lemma23NuArithmeticFunction χ n).re^2/(n : ℝ)) -
            (6/Real.pi^2)*realLDerivAtOne χ^2*
              ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1)| < ε := by
  simp only [Lemma171Target,lemma171Error,lemma171_short_sum_eq_paper,lemma171MainTerm]


end ZhangLS.Spec
