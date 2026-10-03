import ZhangLS.Spec.AppendixBDivisorCoefficientB1

/-! Source, strict endpoint, ramification, and finite-shift regressions. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- The original strict small-prime cutoff is retained. -/
theorem appendixB_divisor_regression_Q (D : ℕ) :
    lemma151Q D=∏ q∈(range (D^4)).filter Nat.Prime,q := rfl

/-- Equality at D⁴ is excluded by the genuine prime-divisor argument. -/
theorem appendixB_divisor_regression_fourth_endpoint {D : ℕ} (hD : 1<D) :
    ¬(D^4).Coprime (lemma151Q D) := by
  intro h
  have hh : 1<D^4 := one_lt_pow₀ hD (by decide : (4 : ℕ)≠0)
  have hgt := appendixB_rough_gt_fourth hh h
  omega

/-- The exact (A) in the proof has the source exponent -2022. -/
theorem appendixB_divisor_regression_original_A {D : ℕ} (χ : RealPrimitiveCharacter D) :
    NormalizedAssumptionA χ ↔ realLAtOne χ < (Real.log (D : ℝ))^(-2022 : ℤ) := by
  simp only [NormalizedAssumptionA,AssumptionAWithConstant,one_mul]

/-- The invoked source estimate really is the actual ν square tail at floor(P²). -/
theorem appendixB_divisor_regression_square_source {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ)) :
    (∑ n∈Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
      ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹)≤1260*lemma23PaperL D^(-2011 : ℤ) :=
  lemma31_actual_square_paper_tail_le χ hD hL hA hAbs

/-- No modeled or freely chosen coefficient replaces the actual canonical b. -/
theorem appendixB_divisor_regression_actual_b (D n : ℕ) :
    lemma151BChiPsi D n = ∑ a∈n.divisorsAntidiagonal,
      lemma151First D a.1*lemma151Second D a.2 := rfl

theorem appendixB_divisor_regression_actual_bpsi {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma151BPsi χ n = χ.evalNat n*lemma151BChiPsi D n := rfl

/-- A ramified n₁ is permitted in the literal b coefficient estimate. -/
theorem appendixB_divisor_regression_ramified_n1 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (_hp : p.Prime) (_hpd : p∣D) (n : ℕ) (useCharacter : Bool) :
    ‖lemma151BChiPsi D (p*n)*(if useCharacter then χ.evalNat n else 1)‖≤
      (bCoefficientConstant*(lemma34Tau 2 p : ℝ))*(lemma34Tau 2 n : ℝ) :=
  (appendixB_actual_b_factor_majorants χ p n useCharacter).1

/-- Zero n₁ causes exactly zero arithmetic error for both actual b families. -/
theorem appendixB_divisor_regression_zero_n1 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (S : Finset ℕ) (useCharacter : Bool) :
    lemma151ArithmeticReplacementError χ S
      (fun n => lemma151BChiPsi D (0*n)*(if useCharacter then χ.evalNat n else 1))=0 ∧
    lemma151ArithmeticReplacementError χ S
      (fun n => lemma151BPsi χ (0*n)*(if useCharacter then χ.evalNat n else 1))=0 := by
  simp [lemma151ArithmeticReplacementError,lemma151BPsi,lemma151BChiPsi]

/-- All three actual finite-D shifts remain literal source definitions. -/
theorem appendixB_divisor_regression_beta_shifts (D : ℕ) (c : ℝ) :
    lemma83PaperBeta D c 0=I*((lemma44PaperAlpha D*(1-5*c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) ∧
    lemma83PaperBeta D c 1=I*((2*lemma44PaperAlpha D*(1+c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) ∧
    lemma83PaperBeta D c 2=I*((3*lemma44PaperAlpha D*(1-c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) :=
  ⟨rfl,rfl,rfl⟩

/-- Any finite truncation of the strict source n<P rough sum satisfies the
proved closed floor(P²) support condition. -/
theorem appendixB_divisor_regression_strict_source {D : ℕ}
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (N : ℕ) :
    ∀ n∈(range N).filter (fun (n : ℕ) => 0<n ∧ (n : ℝ)<lemma23PaperP D ∧ n.Coprime (lemma151Q D)),
      0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D) := by
  intro n hn
  have h := (mem_filter.mp hn).2
  have hP1 : 1≤lemma23PaperP D := by
    have hd : (1 : ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
    exact hd.trans (lemma31_D_le_P hD hL)
  refine ⟨h.1,?_,h.2.2⟩
  apply (Nat.le_floor_iff (sq_nonneg (lemma23PaperP D))).mpr
  nlinarith [h.2.1]

end ZhangLS.Spec
