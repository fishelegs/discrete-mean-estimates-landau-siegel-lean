import ZhangLS.Spec.Proposition141OffLocalAggregate
import ZhangLS.Spec.Proposition141LargeAggregateRate

/-! # The actual full large-conductor source majorant

Every l is present in σ. The localization split is an exact identity of
absolutely convergent series, and its literal complement has already been
summed over every original outer index and character.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141SourceUnlocalizedLargeBlock {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) (D₁ D₂ d h:ℕ) (R:ℝ) : ℝ :=
  ∑r∈proposition141SourceLargeModuli D₁ D₂ d h R a,
    ‖a (d*(h*r/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
      ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
        ‖proposition141Sigma χ θ β κ D₁ d h‖

noncomputable def proposition141NormalizedUnlocalizedLargeAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    ∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
      ∑j∈range (proposition141DyadicBlockCount D),
        proposition141SourceUnlocalizedLargeBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)

theorem proposition141_source_unlocalized_large_block_split {D D₁ D₂ d h:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) {Bκ Ba:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hBκ:0≤Bκ) (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hDD:D=D₁*D₂) (hD₁:0<D₁) (hd:0<d) (hh:0<h) {R:ℝ} (hR:1≤R) :
    proposition141SourceUnlocalizedLargeBlock χ β κ a D₁ D₂ d h R ≤
      proposition141SourceLargeBlock χ β κ a D₁ D₂ d h R+
        proposition141SourceOffLocalBlock χ β κ a D₁ D₂ d h R := by
  unfold proposition141SourceUnlocalizedLargeBlock proposition141SourceLargeBlock proposition141SourceOffLocalBlock
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro r hr
  have hp := proposition141_source_large_moduli_mem hr
  have hs := proposition141_source_outer_support ha hD hmod hDD hD₁ hd hh
    (by omega : 0<r) hp.2.2.2.1 hp.2.2.2.2.2
  have hhr : ((h*r:ℕ):ℝ)≤lemma23PaperP D :=
    (by exact_mod_cast hs.2.2.2 : ((h*r:ℕ):ℝ)≤⌊lemma23PaperP D⌋₊).trans (Nat.floor_le (Real.exp_pos _).le)
  have hchar (θ:DirichletCharacter ℂ r) : ‖proposition141Sigma χ θ β κ D₁ d h‖≤
      ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)‖+
        ‖proposition141SigmaOffLocalTail χ θ β κ D₁ d h R‖ := by
    rw [(proposition141_actual_sigma_localization χ θ hD hL hβ hBκ hκ hD₁ hd hR hh
      (mem_filter.mp hr).1 hhr).2]
    exact norm_add_le _ _
  have hb := sum_le_sum (s:=(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive)) (fun θ _=>hchar θ)
  rw [sum_add_distrib] at hb
  have hw : 0≤‖a (d*(h*r/D₂))‖*(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹ := by positivity
  have hh' := mul_le_mul_of_nonneg_left hb hw
  convert hh' using 1; ring

theorem proposition141_actual_unlocalized_large_aggregate_split {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) {Bκ Ba:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hBκ:0≤Bκ) (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    proposition141NormalizedUnlocalizedLargeAggregate χ β κ a≤
      proposition141NormalizedLargeAggregate χ β κ a+proposition141NormalizedOffLocalAggregate χ β κ a := by
  unfold proposition141NormalizedUnlocalizedLargeAggregate proposition141NormalizedLargeAggregate
    proposition141NormalizedOffLocalAggregate proposition141SourceLargeAggregate
  rw [←mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _≤∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
        ∑j∈range (proposition141DyadicBlockCount D),
          (proposition141SourceLargeBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)+
            proposition141SourceOffLocalBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)) := by
      apply sum_le_sum
      intro D₁ hdiv
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      apply sum_le_sum
      intro j hj
      have hD₁:0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 (by omega)
      have hDD:D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
      have hDR:(1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
      have hR:1≤proposition141DyadicScale D j :=
        (Real.one_le_rpow hDR (by norm_num : (0:ℝ)≤3)).trans (proposition141_dyadic_scale_lower D j)
      exact proposition141_source_unlocalized_large_block_split χ β κ a hD hL hβ hBκ hκ ha hmod hDD hD₁
        (mem_Icc.mp hd).1 (mem_Icc.mp hh).1 hR
    _=_ := by simp only [sum_add_distrib]

/-- Entire actual infinite-l large-conductor majorant at a uniform explicit
rate. This theorem has no tail, localization or averaged-estimate premise. -/
theorem proposition141_uniform_unlocalized_large_aggregate_rate :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141NormalizedUnlocalizedLargeAggregate χ β κ a ≤
        (proposition141LargeAggregateConstant+proposition141OffLocalAggregateConstant)*Bκ*Ba*
          lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
  obtain ⟨N₁,hN₁,hlarge⟩ := proposition141_uniform_large_aggregate_rate
  obtain ⟨N₂,hN₂,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max N₁ (max N₂ ⌈Real.exp 2000⌉₊)
  refine ⟨D₀,hN₁.trans (le_max_left _ _),?_⟩
  intro D χ hDN hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hN1:N₁≤D := (le_max_left _ _).trans hDN
  have hN2:N₂≤D := ((le_max_left _ _).trans (le_max_right _ _)).trans hDN
  have hNe:⌈Real.exp 2000⌉₊≤D := ((le_max_right _ _).trans (le_max_right _ _)).trans hDN
  have hD:1<D := by have := hN₁.trans hN1; omega
  have hDp:0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  have hDR:(1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hL:2000≤lemma23PaperL D := by
    have he:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hloc := hlarge χ hN1 hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hoff := proposition141_actual_offlocal_aggregate_bound χ β κ a hD hL hβ hBκ hBa hκ ha (hmod D hN2)
  have hden : Real.sqrt (D:ℝ)≤(D:ℝ)^100 :=
    ((Real.sqrt_le_iff).mpr ⟨hDp.le,le_self_pow₀ hDR (by norm_num : 2≠0)⟩).trans (le_self_pow₀ hDR (by norm_num : 100≠0))
  have hM := lemma56_prime_mass_nonneg D
  have hC := proposition141_offlocal_aggregate_constant_pos.le
  have hoff' : proposition141NormalizedOffLocalAggregate χ β κ a≤
      proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
    apply hoff.trans
    exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hDp) hden
  apply (proposition141_actual_unlocalized_large_aggregate_split χ β κ a hD hL hβ hBκ hκ ha (hmod D hN2)).trans
  have hh := add_le_add hloc hoff'
  convert hh using 1; ring

end ZhangLS.Spec
