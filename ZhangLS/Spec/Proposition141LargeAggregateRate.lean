import ZhangLS.Spec.Proposition141NormalizedLargeAggregate
import ZhangLS.Spec.PolynomialLogDecay

/-! # A fully specified rate for the actual localized large-conductor sum

The constant is explicit, albeit intentionally coarse. Thresholds precede
χ, β and both coefficient sequences; their norm constants scale linearly.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex

noncomputable def proposition141LargeAggregateConstant : ℝ :=
  16384*Real.exp 20*proposition141LargeMeanConstant*polynomialLogHalfConstant 3428

lemma proposition141_large_aggregate_constant_pos : 0<proposition141LargeAggregateConstant := by
  unfold proposition141LargeAggregateConstant
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
    proposition141_large_mean_constant_pos) (polynomialLogHalfConstant_pos _)

theorem proposition141_uniform_large_aggregate_rate :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141NormalizedLargeAggregate χ β κ a ≤
        proposition141LargeAggregateConstant*Bκ*Ba*lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
  obtain ⟨D₀,hD₀,hbound⟩ := proposition141_uniform_normalized_large_aggregate
  refine ⟨D₀,hD₀,?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hD : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by have := hD₀.trans hlarge; omega)
  have hp := polynomialLog_div_decay hD 3428
  have hM := lemma56_prime_mass_nonneg D
  have hC := proposition141_large_mean_constant_pos.le
  apply (hbound χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha).trans
  have hb := mul_le_mul_of_nonneg_left hp
    (show 0≤(16384*Real.exp 20*proposition141LargeMeanConstant)*Bκ*Ba*lemma56PrimeMass D by positivity)
  convert hb using 1 <;> simp only [proposition141LargeAggregateConstant,lemma23PaperL] <;> ring

/-- Uniform little-o conclusion for this explicit actual majorant. The
threshold depends on ε and fixed constants, never on χ, β, κ* or a*. -/
theorem proposition141_uniform_large_aggregate_little_o (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141NormalizedLargeAggregate χ β κ a ≤ ε*Bκ*Ba*lemma56PrimeMass D := by
  obtain ⟨N,hN2,hbound⟩ := proposition141_uniform_large_aggregate_rate
  let D₀ := max N ⌈(proposition141LargeAggregateConstant/ε)^2⌉₊
  refine ⟨D₀,hN2.trans (le_max_left _ _),?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hND : N≤D := (le_max_left _ _).trans hlarge
  have hDp : 0<(D:ℝ) := by exact_mod_cast (show 0<D by have := hN2.trans hND; omega)
  have hc := proposition141_large_aggregate_constant_pos
  have he : (proposition141LargeAggregateConstant/ε)^2≤(D:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hs : proposition141LargeAggregateConstant/ε≤Real.sqrt (D:ℝ) := by
    have hh := Real.sqrt_le_sqrt he
    simpa only [Real.sqrt_sq (div_nonneg hc.le hε.le)] using hh
  have hrate : proposition141LargeAggregateConstant/Real.sqrt (D:ℝ)≤ε := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hDp)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hs
  apply (hbound χ hND hA β hβ Bκ Ba hBκ hBa κ a hκ ha).trans
  have hM := lemma56_prime_mass_nonneg D
  have hb := mul_le_mul_of_nonneg_right hrate (show 0≤Bκ*Ba*lemma56PrimeMass D by positivity)
  convert hb using 1 <;> ring

end ZhangLS.Spec
