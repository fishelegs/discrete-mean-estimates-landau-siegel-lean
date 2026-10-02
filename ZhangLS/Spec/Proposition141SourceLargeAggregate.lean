import ZhangLS.Spec.Proposition141SourceLargeBlock
import ZhangLS.Spec.Proposition141DyadicCover
import ZhangLS.Spec.Proposition71ConductorWeights

/-! # The original large-conductor positive sum, through d, h and dyadic ranges

The literal short-coefficient and complementary-divisor conditions stay in every
block. Every totient and divisor factor is accounted for before simplification.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141SourceLargeAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) (D₁ D₂ X:ℕ) : ℝ :=
  ∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑j∈range (proposition141DyadicBlockCount D),
    proposition141SourceLargeBlock χ β κ a D₁ D₂ d h (proposition141DyadicScale D j)

lemma proposition141_large_outer_weight_sum (X:ℕ) (hX:1≤X) :
    (∑d∈Icc 1 X, ∑h∈Icc 1 X,
      ((lemma34Tau 5 d:ℝ)/(d:ℝ))*(h.totient:ℝ)⁻¹) ≤ (1+Real.log (X:ℝ))^7 := by
  have hd := proposition71_tau_harmonic_bound 5 X hX
  have hh : (∑h∈Icc 1 X,(h.totient:ℝ)⁻¹)≤(1+Real.log (X:ℝ))^2 := by
    apply (sum_le_sum (fun h hh=>proposition71_reciprocal_totient_le_tau (mem_Icc.mp hh).1)).trans
    exact proposition71_tau_harmonic_bound 2 X hX
  calc
    _=(∑d∈Icc 1 X,(lemma34Tau 5 d:ℝ)/(d:ℝ))*(∑h∈Icc 1 X,(h.totient:ℝ)⁻¹) := by
      rw [sum_mul]
      simp_rw [mul_sum]
    _≤(1+Real.log (X:ℝ))^5*(1+Real.log (X:ℝ))^2 := by
      apply mul_le_mul hd hh (sum_nonneg (fun _ _=>by positivity))
      positivity
    _=_ := by ring

/-- All original outer d,h and dyadic sums are bounded uniformly. No support
cutoff or averaged character estimate is assumed: each comes from the actual
source block and its proved weighted large-sieve estimate. -/
theorem proposition141_uniform_source_large_aggregate :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      ∀D₁ D₂:ℕ,D=D₁*D₂ → 0<D₁ → ∀X:ℕ,1≤X →
      proposition141SourceLargeAggregate χ β κ a D₁ D₂ X ≤
        4*proposition141LargeMeanConstant*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*lemma56PrimeMass D*
          lemma23PaperL D^3360*((D₂:ℝ)/(D:ℝ)^(3/2:ℝ))*(1+Real.log (X:ℝ))^7 := by
  obtain ⟨N,hN2,hblock⟩ := proposition141_uniform_source_large_block
  let D₀ := max N ⌈Real.exp 1⌉₊
  refine ⟨D₀,le_trans hN2 (le_max_left _ _),?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ D₂ hDD hD₁ X hX
  have hND : N≤D := (le_max_left _ _).trans hlarge
  have he : Real.exp 1≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hL : 1≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  let C := proposition141LargeMeanConstant*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*lemma56PrimeMass D*
    lemma23PaperL D^3351*((D₂:ℝ)/(D:ℝ)^(3/2:ℝ))
  have hC : 0≤C := by
    dsimp [C]
    have := proposition141_large_mean_constant_pos.le
    have := lemma56_prime_mass_nonneg D
    positivity
  have hpoint : proposition141SourceLargeAggregate χ β κ a D₁ D₂ X ≤
      C*(proposition141DyadicBlockCount D:ℝ)*(∑d∈Icc 1 X,∑h∈Icc 1 X,
        ((lemma34Tau 5 d:ℝ)/(d:ℝ))*(h.totient:ℝ)⁻¹) := by
    unfold proposition141SourceLargeAggregate
    calc
      _≤∑d∈Icc 1 X,∑h∈Icc 1 X,∑j∈range (proposition141DyadicBlockCount D),
          C*((lemma34Tau 5 d:ℝ)/(d:ℝ))*(h.totient:ℝ)⁻¹ := by
        apply sum_le_sum
        intro d hd
        apply sum_le_sum
        intro h hh
        apply sum_le_sum
        intro j _hj
        have hR : (D:ℝ)^3≤proposition141DyadicScale D j := by
          simpa only [Real.rpow_ofNat] using proposition141_dyadic_scale_lower D j
        exact hblock χ hND hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ D₂ d h hDD hD₁
          (mem_Icc.mp hd).1 (mem_Icc.mp hh).1 _ hR
      _=_ := by
        simp only [sum_const,card_range,nsmul_eq_mul,mul_sum]
        apply sum_congr rfl
        intro d hd
        apply sum_congr rfl
        intro h hh
        ring
  calc
    _≤C*(proposition141DyadicBlockCount D:ℝ)*(1+Real.log (X:ℝ))^7 :=
      hpoint.trans (mul_le_mul_of_nonneg_left (proposition141_large_outer_weight_sum X hX) (by positivity))
    _≤C*(4*lemma23PaperL D^9)*(1+Real.log (X:ℝ))^7 := by
      gcongr
      exact proposition141_dyadic_block_count_bound hL
    _=_ := by dsimp [C]; ring

end ZhangLS.Spec
