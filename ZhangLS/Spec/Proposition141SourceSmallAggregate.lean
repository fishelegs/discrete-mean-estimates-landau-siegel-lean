import ZhangLS.Spec.Proposition141SourceSmallSum

/-! # The source small-conductor positive sum, including both D₁ branches

All actual a*, D₂ and primitive-character factors survive until the relevant
proved pointwise bound or exact arithmetic budget is applied. Principal r=1
is omitted explicitly; the actual χ-induced exclusion is in the family.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

noncomputable def proposition141SourceSmallAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) (D₁ D₂ X:ℕ)
    (S:ℕ→ℕ→ℕ→Finset ℕ) : ℝ :=
  ∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
    ‖a (d*(r*h/D₂))‖*((D₂:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)))*
      ∑θ∈proposition141SmallPrimitiveFamily χ h r,
        ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖

lemma proposition141_source_small_weight_sum (D D₁ D₂ X:ℕ) (a:ℕ→ℂ) (hX:1≤X) :
    (∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
      (D₂:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) ≤
      (D₂:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ)*(1+Real.log (X:ℝ))^7 := by
  calc
    _≤∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈Icc 1 (D^3),
        (D₂:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
          ((d:ℝ)*((r*h).totient:ℝ)) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _=>by positivity)
    _=(D₂:ℝ)*(∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈Icc 1 (D^3),
        (lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/((d:ℝ)*((h*r).totient:ℝ))) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro h hh
      apply sum_congr rfl
      intro r hr
      rw [Nat.mul_comm h r]
      ring
    _≤_ := by
      have hb := mul_le_mul_of_nonneg_left (proposition71_counted_conductor_weight_sum X (D^3) hX)
        (Nat.cast_nonneg D₂)
      simpa only [mul_assoc] using hb

/-- Actual finite-long source small-conductor aggregate, with D₂ retained
rather than uniformly replacing every complementary divisor by D. -/
theorem proposition141_uniform_source_small_aggregate :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      ∀D₁ D₂ X Y:ℕ,D=D₁*D₂ → 0<D₁ → 1≤X → 1≤Y → ∀S:ℕ→ℕ→ℕ→Finset ℕ,
      (∀d∈Icc 1 X,∀h∈Icc 1 X,∀r∈proposition141SourceSmallModuli D D₁ D₂ d h a,S d h r⊆Icc 1 Y) →
      proposition141SourceSmallAggregate χ β κ a D₁ D₂ X S ≤
        C*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
          (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*
          ((D₂:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ))*(1+Real.log (Y:ℝ))^5*(1+Real.log (X:ℝ))^7 := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_source_small_character_sum
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ D₂ X Y hDD hD₁ hX hY S hS
  have hD : 0<D := by have := hD₀.trans hlarge; omega
  have hD₂ : 0<D₂ := by
    by_contra hn
    have hz:D₂=0 := by omega
    rw [hz,mul_zero] at hDD
    omega
  let K := C*Bκ*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
    (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*(1+Real.log (Y:ℝ))^5
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hlog : 0≤1+Real.log (Y:ℝ) := by have := Real.log_natCast_nonneg Y; linarith
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (d:ℕ) (hd:d∈Icc 1 X) (h:ℕ) (hh:h∈Icc 1 X)
      (r:ℕ) (hr:r∈proposition141SourceSmallModuli D D₁ D₂ d h a) :
      ‖a (d*(r*h/D₂))‖*((D₂:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)))*
        (∑θ∈proposition141SmallPrimitiveFamily χ h r,
          ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖) ≤
      Ba*K*((D₂:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) := by
    have hp := proposition141_source_small_moduli_mem hr
    have hdp : 0<d := (mem_Icc.mp hd).1
    have hhp : 0<h := (mem_Icc.mp hh).1
    have hrp : 0<r := by omega
    letI : NeZero r := ⟨by omega⟩
    have hk : 0<r*h/D₂ := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hrp hhp) hp.2.2.1) hD₂
    have ha' := ha.1 _ (Nat.mul_pos hdp hk)
    let F := proposition141SmallPrimitiveFamily χ h r
    have hsθ (θ:DirichletCharacter ℂ r) (hθ:θ∈F) :
        ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖ ≤
          K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ)) := by
      have hb := hbound χ hlarge hA β hβ Bκ Ba hBκ κ a hκ ha D₁ D₂ d h r
        hDD hD₁ hdp hhp hr θ hθ Y hY (S d h r) (hS d hd h hh r hr)
      convert hb using 1; dsimp [K]; ring
    have hc : (F.card:ℝ)≤(r.totient:ℝ) := by
      exact_mod_cast proposition141_primitive_subfamily_card F (fun θ hθ=>(mem_filter.mp hθ).2.1)
    have hs : (∑θ∈F,‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖)≤
        (r.totient:ℝ)*(K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ))) := by
      apply (sum_le_sum hsθ).trans
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    have hw : 0≤(D₂:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)) := by positivity
    have hws := mul_le_mul_of_nonneg_left hs hw
    have hwpos : 0≤((D₂:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)))*
      ∑θ∈F,‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖ := by positivity
    calc
      _=‖a (d*(r*h/D₂))‖*(((D₂:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)))*
        ∑θ∈F,‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖) := by ring
      _≤Ba*(((D₂:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)))*
        ((r.totient:ℝ)*(K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ))))) :=
        mul_le_mul ha' hws hwpos hBa
      _=_ := by
        rw [proposition141_counted_row_scalar (by exact_mod_cast hdp)
          (by exact_mod_cast hhp) (by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hrp hhp))]
        ring
  unfold proposition141SourceSmallAggregate
  calc
    _≤∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
        Ba*K*((D₂:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
          ((d:ℝ)*((r*h).totient:ℝ))) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum (fun r hr=>hpoint d hd h hh r hr)
    _=Ba*K*(∑d∈Icc 1 X,∑h∈Icc 1 X,∑r∈proposition141SourceSmallModuli D D₁ D₂ d h a,
        (D₂:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
          ((d:ℝ)*((r*h).totient:ℝ))) := by simp only [mul_sum]
    _≤Ba*K*((D₂:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ)*(1+Real.log (X:ℝ))^7) :=
      mul_le_mul_of_nonneg_left (proposition141_source_small_weight_sum D D₁ D₂ X a hX) (by positivity)
    _=_ := by dsimp [K]; ring

end ZhangLS.Spec
