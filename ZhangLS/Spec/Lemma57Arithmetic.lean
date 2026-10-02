import ZhangLS.Spec.DivisorCharacterSum
import ZhangLS.Spec.Lemma57

/-!
# Arithmetic extraction in Zhang's Lemma 5.7

Zhang's proof uses the smoothed sum

  ∑ n, νχ(n) / n * g(D^4 / n)

and lower-bounds it by the contribution of `n ∣ D`.  Step 09 proved the exact
identity `νχ(n) = 1` on those divisors.  This file formalizes the finite divisor
subsum and separates the two remaining quantitative facts:

* the smoothing weight is bounded below on `n ∣ D`;
* the reciprocal divisor sum is `≫ D / φ(D)`.

The infinite smoothed sum and the Mellin identity are intentionally left to the
analytic layer.
-/

namespace ZhangLS.Spec

open scoped BigOperators

/-- The reciprocal divisor sum occurring explicitly in the proof of Lemma 5.7. -/
noncomputable def reciprocalDivisorSum (D : ℕ) : ℝ :=
  ∑ n ∈ Nat.divisors D, ((n : ℝ)⁻¹)

/-- The argument at which Zhang evaluates the smoothing function in Lemma 5.7. -/
noncomputable def lemma57WeightArgument (D n : ℕ) : ℝ :=
  (D : ℝ) ^ 4 / (n : ℝ)

/-- The contribution to Zhang's smoothed sum coming only from divisors of `D`. -/
noncomputable def lemma57DivisorSubsum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Nat.divisors D,
    divisorCharacterSumReal χ n * (n : ℝ)⁻¹ * g (lemma57WeightArgument D n)

/-- Step 09 removes the character coefficient completely on the divisor subsum. -/
theorem lemma57DivisorSubsum_eq_weighted_reciprocal
    {D : ℕ} (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) :
    lemma57DivisorSubsum χ g =
      ∑ n ∈ Nat.divisors D, (n : ℝ)⁻¹ * g (lemma57WeightArgument D n) := by
  unfold lemma57DivisorSubsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [divisorCharacterSumReal_eq_one_of_dvd_modulus χ (Nat.mem_divisors.mp hn).1]
  simp

/-- If the smoothing function is at least `c_g` on all divisor arguments, then the
whole divisor contribution is at least `c_g` times the reciprocal divisor sum. -/
theorem lemma57DivisorSubsum_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ)
    (c_g : ℝ) (hc_g : 0 ≤ c_g)
    (hg : ∀ n ∈ Nat.divisors D, c_g ≤ g (lemma57WeightArgument D n)) :
    c_g * reciprocalDivisorSum D ≤ lemma57DivisorSubsum χ g := by
  rw [lemma57DivisorSubsum_eq_weighted_reciprocal]
  unfold reciprocalDivisorSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [mul_comm c_g]
  exact mul_le_mul_of_nonneg_left (hg n hn) (by positivity)

/-- A uniform explicit version of the elementary estimate
`∑_{n∣D} 1/n ≫ D/φ(D)` used by Zhang. -/
def ReciprocalDivisorLowerBound (c_d : ℝ) : Prop :=
  0 < c_d ∧
    ∀ {D : ℕ}, 1 < D →
      c_d * lemma57Scale D ≤ reciprocalDivisorSum D

/-- A uniform lower bound for a chosen smoothing function on the divisor arguments
`D^4 / n`, `n ∣ D`.  For Zhang's Gaussian cutoff this constant can be chosen absolute
once `D` is beyond the paper's effective threshold. -/
def Lemma57WeightLowerBound (g : ℕ → ℝ → ℝ) (c_g : ℝ) : Prop :=
  0 < c_g ∧
    ∀ {D n : ℕ}, 1 < D → n ∈ Nat.divisors D →
      c_g ≤ g D (lemma57WeightArgument D n)

/-- Combining the two elementary divisor-side estimates gives the exact arithmetic
scale required in Lemma 5.7. -/
theorem lemma57_divisor_arithmetic_scale
    (g : ℕ → ℝ → ℝ) (c_g c_d : ℝ)
    (hweight : Lemma57WeightLowerBound g c_g)
    (hdiv : ReciprocalDivisorLowerBound c_d)
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (c_g * c_d) * lemma57Scale D ≤ lemma57DivisorSubsum χ (g D) := by
  have hsub := lemma57DivisorSubsum_lower_bound χ (g D) c_g hweight.1.le
    (fun n hn => hweight.2 hD hn)
  have hrecip := hdiv.2 hD
  have hcg : 0 ≤ c_g := hweight.1.le
  calc
    (c_g * c_d) * lemma57Scale D = c_g * (c_d * lemma57Scale D) := by ring
    _ ≤ c_g * reciprocalDivisorSum D := mul_le_mul_of_nonneg_left hrecip hcg
    _ ≤ lemma57DivisorSubsum χ (g D) := hsub

/-- Interface between the finite arithmetic extraction and the full smoothed sum.
The analytic/nonnegativity layer must prove that the full sum dominates its divisor
subsum; it is not assumed silently inside `Lemma57ArithmeticLowerBound`. -/
def Lemma57MainSumDominatesDivisors {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) (mainSum : ℝ) : Prop :=
  lemma57DivisorSubsum χ g ≤ mainSum

/-- Once the full smoothed sum is known to dominate its divisor contribution, the
Step-08 arithmetic structure is obtained with the explicit product constant
`c_g * c_d`. -/
theorem lemma57ArithmeticLowerBound_of_divisor_extraction
    (g : ℕ → ℝ → ℝ) (c_g c_d : ℝ)
    (hweight : Lemma57WeightLowerBound g c_g)
    (hdiv : ReciprocalDivisorLowerBound c_d)
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (mainSum : ℝ)
    (hmain : Lemma57MainSumDominatesDivisors χ (g D) mainSum) :
    ∃ a : Lemma57ArithmeticLowerBound D,
      a.constant = c_g * c_d ∧ a.mainSum = mainSum := by
  have hc : 0 < c_g * c_d := mul_pos hweight.1 hdiv.1
  have hscale := lemma57_divisor_arithmetic_scale g c_g c_d hweight hdiv χ hD
  refine ⟨{
    constant := c_g * c_d
    mainSum := mainSum
    constant_pos := hc
    lower_bound := ?_
  }, rfl, rfl⟩
  exact le_trans hscale hmain

end ZhangLS.Spec
