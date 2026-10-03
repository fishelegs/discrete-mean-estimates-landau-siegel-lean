import ZhangLS.Spec.Lemma171MainLowerBound
set_option autoImplicit false
namespace ZhangLS.Spec

-- The actual coefficient at the included source endpoint.
example {D : ℕ} (χ : RealPrimitiveCharacter D) : lemma171Coefficient χ 1=1 :=
  lemma171_coefficient_one χ

-- Modulus one is correctly excluded: its strict finite interval is empty.
example (χ : RealPrimitiveCharacter 1) : lemma171ShortHarmonicSum χ=0 := by
  simp [lemma171ShortHarmonicSum]

-- The n=1 lower bound applies throughout the genuine D>1 range.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) :
    1≤∑ n∈Finset.Ico 1 (D^4), ‖lemma23NuArithmeticFunction χ n‖^2/(n : ℝ) :=
  lemma171_actual_short_sum_ge_one χ hD

-- Source (2.31) expanded; there is no phi(D)/D factor in a.
example : ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
    NormalizedAssumptionA χ →
      (1:ℝ)/2<(6/Real.pi^2)*realLDerivAtOne χ^2*
        ∏ p∈D.primeFactors, (p : ℝ)/((p : ℝ)+1) :=
  lemma171_actual_main_gt_half

-- Arbitrary epsilon retains the original uniform order of quantifiers.
example (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → 1-ε<lemma171MainTerm χ :=
  lemma171_actual_main_lower_uniform ε hε

-- The relative theorem concerns the actual harmonic-sum error.
example (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |(lemma171ShortHarmonicSum χ-lemma171MainTerm χ)/lemma171MainTerm χ|<ε :=
  lemma171_actual_relative_error_uniform ε hε

end ZhangLS.Spec
