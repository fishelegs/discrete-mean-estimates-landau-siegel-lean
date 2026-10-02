import ZhangLS.Spec.Proposition141SmallConductorAggregate

/-! # The original a* coefficient in the finite small-conductor aggregate

After Dk=hr, the coefficient is literally a*(d*(rh/D)). Divisibility and
positivity prove its index is positive before the original a* bound is used.
The coefficient is not replaced by an unrelated model or residual.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141WeightedSmallConductorAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) (D₁ X:ℕ)
    (S:ℕ→ℕ→ℕ→Finset ℕ) : ℝ :=
  ∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈proposition141SmallSupportedModuli D h,
    ‖a (d*(r*h/D))‖*((D:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)))*
      ∑θ∈proposition141SmallPrimitiveFamily χ h r,
        ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖

/-- The original short coefficient contributes only its given uniform bound,
after the actual quotient-index positivity is proved. -/
theorem proposition141_weighted_small_aggregate_le {D:ℕ}
    (χ:RealPrimitiveCharacter D) (hD:0<D) (β:ℂ) (κ:ℕ→ℂ)
    {Ba:ℝ} {a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a) (D₁ X:ℕ)
    (S:ℕ→ℕ→ℕ→Finset ℕ) :
    proposition141WeightedSmallConductorAggregate χ β κ a D₁ X S ≤
      Ba*proposition141FiniteSmallConductorAggregate χ β κ D₁ X S := by
  unfold proposition141WeightedSmallConductorAggregate proposition141FiniteSmallConductorAggregate
  simp only [mul_sum]
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro h hh
  apply sum_le_sum
  intro r hr
  have hrs := proposition141_small_supported_mem hr
  have hhp : 0<h := (mem_Icc.mp hh).1
  have hdp : 0<d := (mem_Icc.mp hd).1
  have hrp : 0<r := by omega
  have hquot : 0<r*h/D := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hrp hhp) hrs.2.2.1) hD
  have ha' := ha.1 (d*(r*h/D)) (Nat.mul_pos hdp hquot)
  have hfactor : 0≤(D:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))*
      ∑θ∈proposition141SmallPrimitiveFamily χ h r,
        ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖ := by positivity
  have hb := mul_le_mul_of_nonneg_right ha' hfactor
  simpa only [mul_assoc,mul_sum] using hb

/-- The actual finite-long small-conductor source majorant, now including
both original coefficient constants and the literal a*(d rh/D). -/
theorem proposition141_uniform_weighted_small_conductor_aggregate :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      ∀D₁ X Y:ℕ,0<D₁ → 1≤X → 1≤Y → ∀S:ℕ→ℕ→ℕ→Finset ℕ,
      (∀d∈Icc 1 X,∀h∈Icc 1 X,∀r∈proposition141SmallSupportedModuli D h,S d h r⊆Icc 1 Y) →
      proposition141WeightedSmallConductorAggregate χ β κ a D₁ X S ≤
        C*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
          (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*
          ((D:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ))*(1+Real.log (Y:ℝ))^5*(1+Real.log (X:ℝ))^7 := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_finite_small_conductor_aggregate
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ X Y hD₁ hX hY S hS
  have hDp : 0<D := by have := hD₀.trans hlarge; omega
  apply (proposition141_weighted_small_aggregate_le χ hDp β κ ha D₁ X S).trans
  have hb := mul_le_mul_of_nonneg_left
    (hbound χ hlarge hA β hβ Bκ hBκ κ hκ D₁ X Y hD₁ hX hY S hS) hBa
  convert hb using 1; ring

end ZhangLS.Spec
