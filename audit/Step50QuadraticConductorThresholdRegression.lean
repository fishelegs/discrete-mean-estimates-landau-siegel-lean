import ZhangLS.Spec.Lemma57QuadraticConductorThreshold

/-! # Step 50 conductor-linear quadratic criterion regression -/

namespace ZhangLS.Spec

example (n : ℕ) :
    Filter.Tendsto (fun D : ℕ => Real.log (D : ℝ) ^ n / (D : ℝ))
      Filter.atTop (nhds 0) :=
  tendsto_log_pow_div_modulus_zero n

example :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D) {C : ℝ},
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      C ≤ (D : ℝ) → Lemma57LeftQuadraticGrowth χ C →
      Lemma57GaussianAnalyticErrorBound χ :=
  exists_modulus_threshold_for_quadratic_coefficient_error

end ZhangLS.Spec
