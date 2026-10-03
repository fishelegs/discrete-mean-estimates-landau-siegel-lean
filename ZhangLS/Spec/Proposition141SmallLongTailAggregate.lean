import ZhangLS.Spec.Proposition141SourceLongTailBlock
import ZhangLS.Spec.Proposition141OffLocalAggregate

/-! # All actual small-conductor long-index tails, including both D₁ branches

The exact original source weights and families are retained. The complete
outer budget is P^14 exp(-L^10/2), hence at most D^(-100).
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141NormalizedSmallLongTailAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    ∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
        proposition141SourceLongTailBlock χ β κ a D₁ (D/D₁) d h

/-- Full actual off-local tail, including exterior Gauss normalization and
all divisor/character/outer counts, with a fixed quantitative D^(-100) rate. -/
theorem proposition141_actual_small_long_tail_aggregate_bound {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) {Bκ Ba:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hBκ:0≤Bκ) (hBa:0≤Ba) (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    proposition141NormalizedSmallLongTailAggregate χ β κ a≤
      proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D/(D:ℝ)^100 := by
  have hDpos : 0<D := by omega
  have hDR : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hX : (⌊lemma23PaperP D⌋₊:ℝ)≤lemma23PaperP D := Nat.floor_le hP
  have hDc := proposition141_divisor_card_le_P hDpos hL1
  let K := (2^40*proposition141OffLocalTailConstant)*Bκ*Ba*lemma56PrimeMass D*
    lemma23PaperP D^11*Real.exp (-lemma23PaperL D^10/2)
  have hC := proposition141_offlocal_tail_constant_pos.le
  have hM := lemma56_prime_mass_nonneg D
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (D₁:ℕ) (hdiv:D₁∈D.divisors) (d:ℕ) (hd:d∈Icc 1 ⌊lemma23PaperP D⌋₊)
      (h:ℕ) (hh:h∈Icc 1 ⌊lemma23PaperP D⌋₊) :
      proposition141SourceLongTailBlock χ β κ a D₁ (D/D₁) d h≤K := by
    have hD₁:0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 hDpos
    have hDD:D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
    have hdP:(d:ℝ)≤lemma23PaperP D :=
      (by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ)≤⌊lemma23PaperP D⌋₊).trans hX

    exact proposition141_source_long_tail_block_bound χ β κ a hD hL hβ hBκ hBa hκ ha hmod hDD hD₁
      (mem_Icc.mp hd).1 (mem_Icc.mp hh).1 hdP
  have hinner : (∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
        proposition141SourceLongTailBlock χ β κ a D₁ (D/D₁) d h) ≤
      lemma23PaperP D^3*K := by
    calc
      _≤∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
          K := by
        apply sum_le_sum
        intro D₁ hdiv
        apply sum_le_sum
        intro d hd
        apply sum_le_sum
        intro h hh
        exact hpoint D₁ hdiv d hd h hh
      _=(D.divisors.card:ℝ)*(⌊lemma23PaperP D⌋₊:ℝ)^2*K := by
        simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
        ring
      _≤lemma23PaperP D*lemma23PaperP D^2*K := by gcongr
      _=_ := by ring
  have hweight : ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)≤Real.exp 20 :=
    (div_le_self (norm_nonneg _) (Real.one_le_sqrt.mpr hDR)).trans (proposition141_t0_shift_norm hL hβ)
  unfold proposition141NormalizedSmallLongTailAggregate
  calc
    _≤Real.exp 20*(lemma23PaperP D^3*K) := by
      apply mul_le_mul hweight hinner
      · unfold proposition141SourceLongTailBlock
        exact sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>
          sum_nonneg (fun _ _=>by positivity))))
      · exact Real.exp_nonneg _
    _=proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D*
        (Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^14) := by
      dsimp [K,proposition141OffLocalAggregateConstant]
      ring
    _≤proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D*(1/(D:ℝ)^100) := by
      apply mul_le_mul_of_nonneg_left (proposition141_actual_tail_polynomial_rate hDpos hL 14 (by norm_num))
      have := proposition141_offlocal_aggregate_constant_pos.le
      positivity
    _=_ := by ring

end ZhangLS.Spec
