import ZhangLS.Spec.Proposition141SourceLargeAggregate
import ZhangLS.Spec.Proposition141DivisorWeightedBudget
import ZhangLS.Spec.Proposition141GlobalShift

/-! # Complementary divisors and the exterior Gauss normalization

This is the actual localized large-conductor positive majorant after summing
D₁|D. Its source factors are not discarded before the divisor sum: D₂=D/D₁
is what gives the harmonic divisor budget and the explicit ℒ^3428/D rate.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition141NormalizedLargeAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) : ℝ :=
  ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
    ∑D₁∈D.divisors,proposition141SourceLargeAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊

lemma proposition141_floor_P_log_seven {D:ℕ} (hL:1≤lemma23PaperL D) :
    1≤⌊lemma23PaperP D⌋₊ ∧
      (1+Real.log (⌊lemma23PaperP D⌋₊:ℝ))^7≤128*lemma23PaperL D^63 := by
  have hL9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp (by positivity)
  have hX : 1≤⌊lemma23PaperP D⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hP1)
  refine ⟨hX,?_⟩
  have hXp : 0<(⌊lemma23PaperP D⌋₊:ℝ) := by exact_mod_cast (show 0<⌊lemma23PaperP D⌋₊ by omega)
  have hXP : (⌊lemma23PaperP D⌋₊:ℝ)≤lemma23PaperP D := Nat.floor_le (by positivity)
  have hlog : Real.log (⌊lemma23PaperP D⌋₊:ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using Real.log_le_log hXp hXP
  have hbase : 1+Real.log (⌊lemma23PaperP D⌋₊:ℝ)≤2*lemma23PaperL D^9 := by linarith
  have hbase0 : 0≤1+Real.log (⌊lemma23PaperP D⌋₊:ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤⌊lemma23PaperP D⌋₊)
    linarith
  calc
    _≤(2*lemma23PaperL D^9)^7 := pow_le_pow_left₀ hbase0 hbase 7
    _=_ := by ring

lemma proposition141_exterior_power_identity {D:ℝ} (hD:0<D) (v:ℝ) :
    (Real.sqrt D)⁻¹*(v/D^(3/2:ℝ))=v/D^2 := by
  rw [conductorTotientWeight_three_halves hD.le]
  have hs : Real.sqrt D≠0 := (Real.sqrt_pos.mpr hD).ne'
  have he := Real.sq_sqrt hD.le
  field_simp
  rw [he]; ring

/-- Uniform localized large-conductor majorant with the actual exterior
shift and all complementary-divisor sums. Its rate is explicit; there is no
undefined alpha-one and no averaged hypothesis equal to the conclusion. -/
theorem proposition141_uniform_normalized_large_aggregate :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀Bκ Ba:ℝ,0≤Bκ → 0≤Ba →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
      proposition141NormalizedLargeAggregate χ β κ a ≤
        (16384*Real.exp 20*proposition141LargeMeanConstant)*Bκ*Ba*lemma56PrimeMass D*
          lemma23PaperL D^3428/(D:ℝ) := by
  obtain ⟨N,hN2,hagg⟩ := proposition141_uniform_source_large_aggregate
  let D₀ := max N ⌈Real.exp 2000⌉₊
  refine ⟨D₀,hN2.trans (le_max_left _ _),?_⟩
  intro D χ hlarge hA β hβ Bκ Ba hBκ hBa κ a hκ ha
  have hND : N≤D := (le_max_left _ _).trans hlarge
  have hD : 0<D := by have := hN2.trans hND; omega
  have hDR : 0<(D:ℝ) := by exact_mod_cast hD
  have he : Real.exp 2000≤(D:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hX := proposition141_floor_P_log_seven hL1
  let C := 512*proposition141LargeMeanConstant*Bκ*Ba*lemma56PrimeMass D*lemma23PaperL D^3423
  have hC : 0≤C := by
    dsimp [C]
    have := proposition141_large_mean_constant_pos.le
    have := lemma56_prime_mass_nonneg D
    positivity
  have hrow (D₁:ℕ) (hdiv:D₁∈D.divisors) :
      proposition141SourceLargeAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊ ≤
        C*((lemma34Tau 5 D₁:ℝ)*((D/D₁:ℕ):ℝ)/(D:ℝ)^(3/2:ℝ)) := by
    have hD₁ : 0<D₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 hD
    have hDD : D=D₁*(D/D₁) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdiv).1).symm
    have hb := hagg χ hND hA β hβ Bκ Ba hBκ hBa κ a hκ ha D₁ (D/D₁) hDD hD₁ _ hX.1
    apply hb.trans
    calc
      _≤4*proposition141LargeMeanConstant*Bκ*Ba*(lemma34Tau 5 D₁:ℝ)*lemma56PrimeMass D*
          lemma23PaperL D^3360*(((D/D₁:ℕ):ℝ)/(D:ℝ)^(3/2:ℝ))*(128*lemma23PaperL D^63) := by
        apply mul_le_mul_of_nonneg_left hX.2
        have := proposition141_large_mean_constant_pos.le
        have := lemma56_prime_mass_nonneg D
        positivity
      _=_ := by dsimp [C]; ring
  have hsum : 0≤∑D₁∈D.divisors,proposition141SourceLargeAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊ := by
    unfold proposition141SourceLargeAggregate proposition141SourceLargeBlock
    exact sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>
      sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>by positivity)))))
  have hlog : (1+Real.log (D:ℝ))^5≤32*lemma23PaperL D^5 := by
    have hb : 1+Real.log (D:ℝ)≤2*lemma23PaperL D := by change 1+lemma23PaperL D≤_; linarith
    calc
      _≤(2*lemma23PaperL D)^5 := pow_le_pow_left₀ (by have := Real.log_natCast_nonneg D; positivity) hb 5
      _=_ := by ring
  unfold proposition141NormalizedLargeAggregate
  calc
    _≤(Real.exp 20/Real.sqrt (D:ℝ))*∑D₁∈D.divisors,
        C*((lemma34Tau 5 D₁:ℝ)*((D/D₁:ℕ):ℝ)/(D:ℝ)^(3/2:ℝ)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (proposition141_t0_shift_norm hL hβ) (Real.sqrt_nonneg _)
      · exact sum_le_sum hrow
      · exact hsum
      · positivity
    _=Real.exp 20*C*(∑D₁∈D.divisors,(lemma34Tau 5 D₁:ℝ)*((D/D₁:ℕ):ℝ)/(D:ℝ)^2) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro D₁ hdiv
      have hp := proposition141_exterior_power_identity hDR ((lemma34Tau 5 D₁:ℝ)*((D/D₁:ℕ):ℝ))
      calc
        _=Real.exp 20*C*((Real.sqrt (D:ℝ))⁻¹*((lemma34Tau 5 D₁:ℝ)*((D/D₁:ℕ):ℝ)/(D:ℝ)^(3/2:ℝ))) := by ring
        _=_ := by rw [hp]
    _≤Real.exp 20*C*((1+Real.log (D:ℝ))^5/(D:ℝ)) :=
      mul_le_mul_of_nonneg_left (proposition141_normalized_complementary_divisor_budget hD) (by positivity)
    _≤Real.exp 20*C*((32*lemma23PaperL D^5)/(D:ℝ)) := by gcongr
    _=_ := by dsimp [C]; ring

end ZhangLS.Spec
