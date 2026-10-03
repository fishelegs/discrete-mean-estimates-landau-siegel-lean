import ZhangLS.Spec.Proposition141UnlocalizedSmallAggregate
import ZhangLS.Spec.Proposition141UnlocalizedLargeAggregate

/-! # The complete original small/large conductor positive majorant

All positive l, both D₁ branches, the source short coefficients, all original
outer indices and the exterior normalization are present. This is still an
arithmetic/analytic majorant awaiting its exact attachment to the original
contour mean, not an assumed residual or the final numbered proposition.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex

noncomputable def proposition141CompleteConductorMajorant {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  proposition141NormalizedUnlocalizedSmallAggregate χ β κ a+
    proposition141NormalizedUnlocalizedLargeAggregate χ β κ a

theorem proposition141_complete_conductor_rate :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141CompleteConductorMajorant χ β κ a≤C*Bκ*Ba*lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
  obtain ⟨C,hC,N₁,hN₁,hsmall⟩ := proposition141_uniform_unlocalized_small_aggregate_rate
  obtain ⟨N₂,hN₂,hlarge⟩ := proposition141_uniform_unlocalized_large_aggregate_rate
  let CL := proposition141LargeAggregateConstant+proposition141OffLocalAggregateConstant
  have hCL:0<CL := add_pos proposition141_large_aggregate_constant_pos proposition141_offlocal_aggregate_constant_pos
  refine ⟨C+CL,add_pos hC hCL,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D χ hDN hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hs := hsmall χ ((le_max_left _ _).trans hDN) hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hl := hlarge χ ((le_max_right _ _).trans hDN) hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hb := add_le_add hs hl
  unfold proposition141CompleteConductorMajorant
  convert hb using 1; dsimp [CL]; ring

/-- The coefficient constants and ε precede one threshold, followed by χ,
κ*, a* and the entire complex β disk, exactly as in the original target. -/
theorem proposition141_complete_conductor_little_o (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba)
    (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          proposition141CompleteConductorMajorant χ β κ a≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨C,hC,N,hN,hbound⟩ := proposition141_complete_conductor_rate
  let A := C*Bκ*Ba
  have hAp:0<A := mul_pos (mul_pos hC hBκ) hBa
  let D₀ := max N ⌈(A/ε)^2⌉₊
  refine ⟨D₀,hN.trans (le_max_left _ _),?_⟩
  intro D hlarge χ hA κ a hκ ha β hβ
  have hND:N≤D := (le_max_left _ _).trans hlarge
  have hDp:0<(D:ℝ) := by exact_mod_cast (show 0<D by have := hN.trans hND; omega)
  have he:(A/ε)^2≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hs:A/ε≤Real.sqrt (D:ℝ) := by
    have hh := Real.sqrt_le_sqrt he
    simpa only [Real.sqrt_sq (div_nonneg hAp.le hε.le)] using hh
  have hrate:A/Real.sqrt (D:ℝ)≤ε := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hDp)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hs
  have hb := hbound χ hND hA β hβ Bκ Ba hBκ.le hBa.le κ a hκ ha
  apply hb.trans
  rw [proposition141_actual_prime_masses_equal]
  have hh := mul_le_mul_of_nonneg_right hrate (lemma56_prime_mass_nonneg D)
  convert hh using 1; dsimp [A]; ring

end ZhangLS.Spec
