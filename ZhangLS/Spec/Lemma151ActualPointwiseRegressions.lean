import ZhangLS.Spec.Lemma151ActualPointwiseDecay
import ZhangLS.Spec.AppendixBDivisorB1Regressions
import ZhangLS.Spec.PaperErrorScaleBudget

/-! Expanded source, endpoint, coefficient-basis and quantified-rate regressions. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical

theorem actual151_regression_source_basis {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma151BPsi χ n=χ.evalNat n*
      ∑ ab∈n.divisorsAntidiagonal,lemma151First D ab.1*lemma151Second D ab.2 := rfl

theorem actual151_regression_literal_target (c : ℝ) (α₁ : ℕ→ℝ) :
    Lemma151OriginalTarget c α₁ ↔
      ∃ C : ℝ,0<C ∧ ∀ᶠ D : ℕ in atTop,
        ∀ χ : RealPrimitiveCharacter D,NormalizedAssumptionA χ →
        ∀ j : Fin 3,∀ n₁ : ℕ,Lemma151Supported (lemma151Q D) n₁ →
        (n₁ : ℝ)<lemma56PaperT D →
        ‖lemma151ArithmeticSum χ c j (lemma151BChiPsi D) n₁-
          χ.evalNat n₁*(n₁.divisors.card : ℂ)*lemma151MainConstant lemma151PrintedTail (j.val+1)‖≤
          C*α₁ D*n₁.divisors.card := Iff.rfl

theorem actual151_regression_ramified_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) (n₁ : ℕ) (hχ : χ.evalNat n₁=0) :
    lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁=0 := by
  rw [b_repaired_rough_sum χ hD c j n₁,hχ,zero_mul]

theorem actual151_regression_strict_h14 (D n : ℕ)
    (hn : (n : ℝ)=(lemma23PaperP D)^(1/2 : ℝ)) : bH14Coefficient D n=0 :=
  b_actual_H14_endpoint D n hn

theorem actual151_regression_tail_constant (j : ℕ) :
    actual151FirstConstant j=
      lemma151FullKernelConstant 0.504 (3/2) j-lemma151ResidueTail j+
        lemma151Iota2*lemma151FullKernelConstant 0.5 (5/2) j := by
  rw [lemma151_residue_tail_eq_neg_pi_I_bstar]
  unfold actual151FirstConstant appendixBH14TerminalConstant
  ring

theorem actual151_regression_P2 (D : ℕ) :
    lemma151P2 D=lemma23PaperP D^(1/2 : ℝ)*lemma56PaperT D^(-10 : ℤ) := by
  norm_num [lemma151P2]

theorem actual151_regression_product_cutoff (D : ℕ) :
    bProductCutoff D=max (lemma23PaperP D^(499/500 : ℝ))
      (lemma23PaperP D*lemma56PaperT D^(-10 : ℤ)) := by
  convert b_product_cutoff_exact D using 1 <;> norm_num

theorem actual151_regression_floor_endpoint (D : ℕ) :
    roughCollisionDomain D ⌊lemma23PaperP D⌋₊=
      (Icc 1 ⌊lemma23PaperP D⌋₊).filter (fun n => n.Coprime
        (∏ q∈(range (D^4)).filter Nat.Prime,q)) := rfl

theorem actual151_regression_rate (D : ℕ) (hL : 0<lemma23PaperL D) :
    actual151Rate D=Real.log (lemma56PaperT D)/Real.log (lemma23PaperP D) :=
  (paper_logT_div_logP hL).symm

theorem actual151_regression_actual_beta (D : ℕ) (c : ℝ) :
    (lemma83PaperBeta D c 0).re=0 ∧ (lemma83PaperBeta D c 1).re=0 ∧
      (lemma83PaperBeta D c 2).re=0 :=
  ⟨lemma83_beta_re D c 0,lemma83_beta_re D c 1,lemma83_beta_re D c 2⟩

/-- The capstone has one threshold before character, shift and smooth n1. -/
theorem actual151_regression_common_threshold {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,∀ n₁ : ℕ,
      Lemma151Supported (lemma151Q D) n₁ → (n₁ : ℝ)<lemma56PaperT D →
      ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-
        χ.evalNat n₁*(lemma34Tau 2 n₁ : ℂ)*lemma151MainConstant lemma151ResidueTail (j.val+1)‖≤
        ‖χ.evalNat n₁‖*actual151PointwiseError D c*(lemma34Tau 2 n₁ : ℝ) := by
  simpa only [actual151_main_constant_residue] using actual151_repaired_quantitative_character hc

end ZhangLS.Spec
