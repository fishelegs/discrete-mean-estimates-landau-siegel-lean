import ZhangLS.Spec.Proposition141SmallLongTailAggregate
import ZhangLS.Spec.Proposition141NormalizedSmallAggregate

/-! # The actual complete small-conductor source majorant

Both D₁ branches and every positive l are included. The principal and χ-induced
removals remain literal, and all prefix and omitted-series bounds are proved.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141NormalizedUnlocalizedSmallAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    ∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
      ∑r∈proposition141SourceSmallModuli D D₁ (D/D₁) d h a,
        ‖a (d*(r*h/(D/D₁)))‖*((D/D₁:ℕ):ℝ)*
          ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
            ∑θ∈proposition141SmallPrimitiveFamily χ h r,‖proposition141Sigma χ θ β κ D₁ d h‖

theorem proposition141_actual_unlocalized_small_aggregate_split {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) {Bκ Ba:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hBκ:0≤Bκ) (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    proposition141NormalizedUnlocalizedSmallAggregate χ β κ a≤
      proposition141NormalizedSmallPrefix χ β κ a+proposition141NormalizedSmallLongTailAggregate χ β κ a := by
  unfold proposition141NormalizedUnlocalizedSmallAggregate proposition141NormalizedSmallPrefix
    proposition141NormalizedSmallLongTailAggregate proposition141SourceSmallAggregate proposition141SourceLongTailBlock
  rw [←mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _≤∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
      ∑r∈proposition141SourceSmallModuli D D₁ (D/D₁) d h a,
        (‖a (d*(r*h/(D/D₁)))‖*((D/D₁:ℕ):ℝ)*
          ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
            ∑θ∈proposition141SmallPrimitiveFamily χ h r,
              ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (Icc 1 ⌊lemma23PaperP D^3⌋₊)‖+
         ‖a (d*(r*h/(D/D₁)))‖*((D/D₁:ℕ):ℝ)*
          ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
            ∑θ∈proposition141SmallPrimitiveFamily χ h r,‖proposition141SigmaLongTail χ θ β κ D₁ d h‖) := by
      apply sum_le_sum
      intro D₁ hdiv
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      apply sum_le_sum
      intro r hr
      have hDpos:0<D := by omega
      have hD₁:0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 hDpos
      have hDD:D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
      have hp := proposition141_source_small_moduli_mem hr
      have hdiv':D/D₁∣h*r := by simpa only [Nat.mul_comm] using hp.2.2.1
      have han:a (d*(h*r/(D/D₁)))≠0 := by simpa only [Nat.mul_comm] using hp.2.2.2.2
      have hs := proposition141_source_outer_support ha hD hmod hDD hD₁
        (mem_Icc.mp hd).1 (mem_Icc.mp hh).1 (by omega : 0<r) hdiv' han
      have hhr:((h*r:ℕ):ℝ)≤lemma23PaperP D :=
        (by exact_mod_cast hs.2.2.2 : ((h*r:ℕ):ℝ)≤⌊lemma23PaperP D⌋₊).trans (Nat.floor_le (Real.exp_pos _).le)
      have hchar (θ:DirichletCharacter ℂ r) : ‖proposition141Sigma χ θ β κ D₁ d h‖≤
          ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (Icc 1 ⌊lemma23PaperP D^3⌋₊)‖+
            ‖proposition141SigmaLongTail χ θ β κ D₁ d h‖ := by
        rw [(proposition141_actual_sigma_prefix χ θ hD hL hβ hBκ hκ hD₁
          (mem_Icc.mp hd).1 (mem_Icc.mp hh).1 hp.1 hhr).2]
        exact norm_add_le _ _
      have hb := sum_le_sum (s:=proposition141SmallPrimitiveFamily χ h r) (fun θ _=>hchar θ)
      rw [sum_add_distrib] at hb
      have hw:0≤‖a (d*(r*h/(D/D₁)))‖*((D/D₁:ℕ):ℝ)*
          ((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹ := by positivity
      have hh' := mul_le_mul_of_nonneg_left hb hw
      convert hh' using 1; ring
    _=_ := by simp only [sum_add_distrib,div_eq_mul_inv,mul_assoc]

/-- Uniform bound for the actual infinite-l small-conductor source
majorant. No averaged estimate, cancellation or long-index tail is assumed. -/
theorem proposition141_uniform_unlocalized_small_aggregate_rate :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141NormalizedUnlocalizedSmallAggregate χ β κ a≤C*Bκ*Ba*lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
  obtain ⟨C,hC,N₁,hN₁,hsmall⟩ := proposition141_uniform_normalized_small_prefix
  obtain ⟨N₂,hN₂,hmod⟩ := proposition141_uniform_support_modulus_bound
  let D₀ := max N₁ (max N₂ ⌈Real.exp 2000⌉₊)
  refine ⟨C+proposition141OffLocalAggregateConstant,add_pos hC proposition141_offlocal_aggregate_constant_pos,
    D₀,hN₁.trans (le_max_left _ _),?_⟩
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
  have hpre := hsmall χ hN1 hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have htail := proposition141_actual_small_long_tail_aggregate_bound χ β κ a hD hL hβ hBκ hBa hκ ha (hmod D hN2)
  have hden:Real.sqrt (D:ℝ)≤(D:ℝ)^100 :=
    ((Real.sqrt_le_iff).mpr ⟨hDp.le,le_self_pow₀ hDR (by norm_num : 2≠0)⟩).trans
      (le_self_pow₀ hDR (by norm_num : 100≠0))
  have hM := lemma56_prime_mass_nonneg D
  have hCoff := proposition141_offlocal_aggregate_constant_pos.le
  have htail' : proposition141NormalizedSmallLongTailAggregate χ β κ a≤
      proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
    apply htail.trans
    exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hDp) hden
  apply (proposition141_actual_unlocalized_small_aggregate_split χ β κ a hD hL hβ hBκ hκ ha (hmod D hN2)).trans
  have hh := add_le_add hpre htail'
  convert hh using 1; ring

end ZhangLS.Spec
