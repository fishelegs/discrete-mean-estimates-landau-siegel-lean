import ZhangLS.Spec.Proposition141OffLocalBlock
import ZhangLS.Spec.Proposition141DyadicCover
import ZhangLS.Spec.Proposition141TailRates

/-! # Every original outer sum of the literal off-localization tail

The P^15 budget explicitly pays for d,h,r,θ,dyadic blocks and D₁|D. The
actual exponential tail then absorbs that whole budget to D^(-100).
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141NormalizedOffLocalAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    ∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
      ∑j∈range (proposition141DyadicBlockCount D),
        proposition141SourceOffLocalBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)

lemma proposition141_dyadic_count_le_P {D:ℕ} (hL:2000≤lemma23PaperL D) :
    (proposition141DyadicBlockCount D:ℝ)≤lemma23PaperP D := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  let x := lemma23PaperL D^9
  have hx : 8≤x := by
    have hh := le_self_pow₀ hL1 (by norm_num : 9≠0)
    dsimp [x]
    linarith
  have he : x^2/2≤Real.exp x := by
    simpa only [Nat.factorial, Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] using
      Real.pow_div_factorial_le_exp x (by linarith : 0≤x) 2
  apply (proposition141_dyadic_block_count_bound hL1).trans
  change 4*x≤Real.exp x
  apply le_trans _ he
  nlinarith only [hx,mul_nonneg (show 0≤x by linarith) (show 0≤x-8 by linarith)]

lemma proposition141_divisor_card_le_P {D:ℕ} (hD:0<D) (hL:1≤lemma23PaperL D) :
    (D.divisors.card:ℝ)≤lemma23PaperP D := by
  have hsub:D.divisors⊆Icc 1 D := by
    intro d hd
    have hh := (Nat.mem_divisors.mp hd).1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hh hD,Nat.le_of_dvd hD hh⟩
  have hc : D.divisors.card≤D := by simpa using card_le_card hsub
  exact (by exact_mod_cast hc : (D.divisors.card:ℝ)≤D).trans (proposition141_modulus_le_P hD hL)

noncomputable def proposition141OffLocalAggregateConstant : ℝ :=
  Real.exp 20*2^40*proposition141OffLocalTailConstant

lemma proposition141_offlocal_aggregate_constant_pos : 0<proposition141OffLocalAggregateConstant := by
  unfold proposition141OffLocalAggregateConstant
  exact mul_pos (mul_pos (Real.exp_pos _) (by positivity)) proposition141_offlocal_tail_constant_pos

/-- Full actual off-local tail, including exterior Gauss normalization and
all divisor/character/outer counts, with a fixed quantitative D^(-100) rate. -/
theorem proposition141_actual_offlocal_aggregate_bound {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) {Bκ Ba:ℝ}
    (hD:1<D) (hL:2000≤lemma23PaperL D) (hβ:‖β‖<5*lemma44PaperAlpha D)
    (hBκ:0≤Bκ) (hBa:0≤Ba) (hκ:Proposition141KappaBound Bκ κ)
    (ha:Proposition141AdmissibleSequence D Ba a)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    proposition141NormalizedOffLocalAggregate χ β κ a≤
      proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D/(D:ℝ)^100 := by
  have hDpos : 0<D := by omega
  have hDR : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hX : (⌊lemma23PaperP D⌋₊:ℝ)≤lemma23PaperP D := Nat.floor_le hP
  have hJ := proposition141_dyadic_count_le_P hL
  have hDc := proposition141_divisor_card_le_P hDpos hL1
  let K := (2^40*proposition141OffLocalTailConstant)*Bκ*Ba*lemma56PrimeMass D*
    lemma23PaperP D^11*Real.exp (-lemma23PaperL D^10/2)
  have hC := proposition141_offlocal_tail_constant_pos.le
  have hM := lemma56_prime_mass_nonneg D
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (D₁:ℕ) (hdiv:D₁∈D.divisors) (d:ℕ) (hd:d∈Icc 1 ⌊lemma23PaperP D⌋₊)
      (h:ℕ) (hh:h∈Icc 1 ⌊lemma23PaperP D⌋₊) (j:ℕ) :
      proposition141SourceOffLocalBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)≤K := by
    have hD₁:0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 hDpos
    have hDD:D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
    have hdP:(d:ℝ)≤lemma23PaperP D :=
      (by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ)≤⌊lemma23PaperP D⌋₊).trans hX
    have hR:1≤proposition141DyadicScale D j :=
      (Real.one_le_rpow hDR (by norm_num : (0:ℝ)≤3)).trans (proposition141_dyadic_scale_lower D j)
    exact proposition141_source_offlocal_block_bound χ β κ a hD hL hβ hBκ hBa hκ ha hmod hDD hD₁
      (mem_Icc.mp hd).1 (mem_Icc.mp hh).1 hdP hR
  have hinner : (∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
      ∑j∈range (proposition141DyadicBlockCount D),
        proposition141SourceOffLocalBlock χ β κ a D₁ (D/D₁) d h (proposition141DyadicScale D j)) ≤
      lemma23PaperP D^4*K := by
    calc
      _≤∑D₁∈D.divisors,∑d∈Icc 1 ⌊lemma23PaperP D⌋₊,∑h∈Icc 1 ⌊lemma23PaperP D⌋₊,
          ∑j∈range (proposition141DyadicBlockCount D),K := by
        apply sum_le_sum
        intro D₁ hdiv
        apply sum_le_sum
        intro d hd
        apply sum_le_sum
        intro h hh
        exact sum_le_sum (fun j _=>hpoint D₁ hdiv d hd h hh j)
      _=(D.divisors.card:ℝ)*(⌊lemma23PaperP D⌋₊:ℝ)^2*(proposition141DyadicBlockCount D:ℝ)*K := by
        simp only [sum_const,card_range,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
        ring
      _≤lemma23PaperP D*lemma23PaperP D^2*lemma23PaperP D*K := by gcongr
      _=_ := by ring
  have hweight : ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)≤Real.exp 20 :=
    (div_le_self (norm_nonneg _) (Real.one_le_sqrt.mpr hDR)).trans (proposition141_t0_shift_norm hL hβ)
  unfold proposition141NormalizedOffLocalAggregate
  calc
    _≤Real.exp 20*(lemma23PaperP D^4*K) := by
      apply mul_le_mul hweight hinner
      · unfold proposition141SourceOffLocalBlock
        exact sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>
          sum_nonneg (fun _ _=>by positivity)))))
      · exact Real.exp_nonneg _
    _=proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D*
        (Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^15) := by
      dsimp [K,proposition141OffLocalAggregateConstant]
      ring
    _≤proposition141OffLocalAggregateConstant*Bκ*Ba*lemma56PrimeMass D*(1/(D:ℝ)^100) := by
      apply mul_le_mul_of_nonneg_left (proposition141_actual_tail_polynomial_rate hDpos hL 15 (by norm_num))
      have := proposition141_offlocal_aggregate_constant_pos.le
      positivity
    _=_ := by ring

end ZhangLS.Spec
