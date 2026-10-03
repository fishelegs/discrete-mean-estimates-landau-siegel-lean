import ZhangLS.Spec.Proposition141SourceSmallAggregate
import ZhangLS.Spec.Proposition141SmallScalarRate
import ZhangLS.Spec.PolynomialLogDecay

/-! # Both source small-conductor branches after all divisor normalizations

The literal finite prefix is l≤P³. The D₂ weight is summed exactly through
D₂=D/D₁; it is not replaced by an unexplained pointwise divisor bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141NormalizedSmallPrefix {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    ∑D₁∈D.divisors,proposition141SourceSmallAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊
      (fun _ _ _=>Icc 1 ⌊lemma23PaperP D^3⌋₊)

theorem proposition141_uniform_normalized_small_prefix :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141NormalizedSmallPrefix χ β κ a≤C*Bκ*Ba*lemma56PrimeMass D/Real.sqrt (D:ℝ) := by
  obtain ⟨C,hC,N,hN,hagg⟩ := proposition141_uniform_source_small_aggregate
  let C' := 8388608*Real.exp 20*C*polynomialLogHalfConstant 7313
  let D₀ := max N ⌈Real.exp 2000⌉₊
  have hC' : 0<C' := by dsimp [C']; have := polynomialLogHalfConstant_pos 7313; positivity
  refine ⟨C',hC',D₀,hN.trans (le_max_left _ _),?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hND:N≤D := (le_max_left _ _).trans hlarge
  have hD:0<D := by have := hN.trans hND; omega
  have hDp:0<(D:ℝ) := by exact_mod_cast hD
  have hDR:(1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have he:Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hL:2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hL1:1≤lemma23PaperL D := by linarith
  have hL0:0≤lemma23PaperL D := by linarith
  have hX := (proposition141_floor_P_log_seven hL1).1
  have hY := (proposition141_floor_P_cube_log_five hL1).1
  let K := C*Bκ*Ba*lemma56PrimeMass D*lemma23PaperL D^7200*
    (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*((D^3:ℕ):ℝ)^(3/2:ℝ)*
      (1+Real.log (⌊lemma23PaperP D^3⌋₊:ℝ))^5*(1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))^7
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hK:0≤K := by
    dsimp [K]
    have := Real.log_natCast_nonneg ⌊lemma23PaperP D^3⌋₊
    have := Real.log_natCast_nonneg ⌊lemma23PaperP D⌋₊
    positivity
  have hrow (D₁:ℕ) (hdiv:D₁∈D.divisors) :
      proposition141SourceSmallAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊
        (fun _ _ _=>Icc 1 ⌊lemma23PaperP D^3⌋₊)≤K*((lemma34Tau 5 D₁:ℝ)*((D/D₁:ℕ):ℝ)) := by
    have hD₁:0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 hD
    have hDD:D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
    have hb := hagg χ hND hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ (D/D₁)
      ⌊lemma23PaperP D⌋₊ ⌊lemma23PaperP D^3⌋₊ hDD hD₁ hX hY (fun _ _ _=>Icc 1 ⌊lemma23PaperP D^3⌋₊)
      (fun _ _ _ _ _ _=>Subset.rfl)
    convert hb using 1; dsimp [K]; ring
  have hsum : (∑D₁∈D.divisors,proposition141SourceSmallAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊
      (fun _ _ _=>Icc 1 ⌊lemma23PaperP D^3⌋₊)) ≤K*((D:ℝ)*(1+Real.log (D:ℝ))^5) := by
    apply (sum_le_sum hrow).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (proposition141_complementary_divisor_budget (by omega)) hK
  have hnorm : ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)≤Real.exp 20/Real.sqrt (D:ℝ) :=
    div_le_div_of_nonneg_right (proposition141_t0_shift_norm hL hβ) (Real.sqrt_nonneg _)
  have hlogs := proposition141_small_log_budget hL1
  have hscalar := proposition141_small_normalized_scalar hD hL
  have hp : lemma23PaperL D^7313/(D:ℝ)^2≤polynomialLogHalfConstant 7313/Real.sqrt (D:ℝ) := by
    apply (div_le_div_of_nonneg_left (pow_nonneg hL0 _) hDp (le_self_pow₀ hDR (by norm_num : 2≠0))).trans
    exact polynomialLog_div_decay hDR 7313
  unfold proposition141NormalizedSmallPrefix
  calc
    _≤(Real.exp 20/Real.sqrt (D:ℝ))*(K*((D:ℝ)*(1+Real.log (D:ℝ))^5)) := by
      apply mul_le_mul hnorm hsum
      · unfold proposition141SourceSmallAggregate
        exact sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>by positivity))))
      · positivity
    _=(C*Real.exp 20*Bκ*Ba*lemma56PrimeMass D)*
        (lemma23PaperL D^7200*(1+Real.log (⌊lemma23PaperP D^3⌋₊:ℝ))^5*
          (1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))^7*(1+Real.log (D:ℝ))^5)*
        ((lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*((D^3:ℕ):ℝ)^(3/2:ℝ)*(D:ℝ)/Real.sqrt (D:ℝ)) := by dsimp [K]; ring
    _≤(C*Real.exp 20*Bκ*Ba*lemma56PrimeMass D)*(4194304*lemma23PaperL D^7313)*(2/(D:ℝ)^2) := by
      have hleft : 0≤lemma23PaperL D^7200*(1+Real.log (⌊lemma23PaperP D^3⌋₊:ℝ))^5*
          (1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))^7*(1+Real.log (D:ℝ))^5 := by
        have := Real.log_natCast_nonneg ⌊lemma23PaperP D^3⌋₊
        have := Real.log_natCast_nonneg ⌊lemma23PaperP D⌋₊
        have := Real.log_natCast_nonneg D
        positivity
      gcongr
    _=(8388608*Real.exp 20*C*Bκ*Ba*lemma56PrimeMass D)*(lemma23PaperL D^7313/(D:ℝ)^2) := by ring
    _≤(8388608*Real.exp 20*C*Bκ*Ba*lemma56PrimeMass D)*(polynomialLogHalfConstant 7313/Real.sqrt (D:ℝ)) := by
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _=_ := by dsimp [C']; ring

end ZhangLS.Spec
