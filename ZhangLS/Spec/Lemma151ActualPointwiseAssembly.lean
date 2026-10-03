import ZhangLS.Spec.Lemma151ActualPointwiseBudget
import ZhangLS.Spec.Lemma151ActualRoughRectangle

/-! A quantitatively repaired pointwise Lemma 15.1, for the genuine psi-basis B.
The literal Lemma151OriginalTarget is neither redefined nor asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical

/-- Exact collision attachment to the full arithmetic rho convolution. -/
theorem actual151_rho_convolution_collision {D n₁ : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 0<D) (hL : 1≤lemma23PaperL D)
    (c : ℝ) (j : Fin 3) (hn₁ : Lemma151Supported (lemma151Q D) n₁) :
    ‖χ.evalNat n₁*(∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
        lemma151BChiPsi D (n₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n)-
      χ.evalNat n₁*(∑ dd∈n₁.divisorsAntidiagonal,
        actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151First D) dd.1*
        actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151Second D) dd.2)‖≤
      (n₁.divisors.card : ℝ)*roughCollisionUniformBudget D := by
  rw [actual151_rho_rough_rectangle hn₁,←mul_sub,←sum_sub_distrib]
  have hP := b_paperP_one_le D
  exact roughCollision_source_character_divisor_sum χ hD hL
    ((Nat.one_le_floor_iff _).mpr hP) (Nat.floor_le (zero_le_one.trans hP)) n₁ c j

/-- The new source constant uses the actual terminal residue. -/
theorem actual151_main_constant_residue (j : ℕ) :
    actual151MainConstant j=lemma151MainConstant lemma151ResidueTail j := by
  unfold actual151MainConstant actual151FirstConstant actual151SecondConstant
    appendixBH14TerminalConstant lemma151MainConstant
  rw [lemma151_residue_tail_eq_neg_pi_I_bstar]
  ring

/-- Honest repaired target: actual bpsi, actual strict-H14 constant, and a named
fully quantified error. No interpretation of the undefined alpha1 is assigned. -/
def Lemma151RepairedQuantitativeTarget (c : ℝ) : Prop :=
  ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
    NormalizedAssumptionA χ → ∀ j : Fin 3,∀ n₁ : ℕ,
    Lemma151Supported (lemma151Q D) n₁ → (n₁ : ℝ)<lemma56PaperT D →
    ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-
      χ.evalNat n₁*(lemma34Tau 2 n₁ : ℂ)*actual151MainConstant (j.val+1)‖≤
      actual151PointwiseError D c*(lemma34Tau 2 n₁ : ℝ)

/-- Complete pointwise arithmetic assembly, with the threshold chosen before
chi, j and n1. Every input estimate is applied to its actual arithmetic sum. -/
theorem actual151_repaired_quantitative {c : ℝ} (hc : 0<c) :
    Lemma151RepairedQuantitativeTarget c := by
  obtain ⟨N,hN,hprod⟩ := actual151_divisor_products_uniform hc
  obtain ⟨M,hnu⟩ := actual151_rhostar_to_rho_uniform c
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨max N (max M K),hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j n₁ hn₁ hnT
  have hN' : N≤D := (le_max_left _ _).trans hD
  have hMK : max M K≤D := (le_max_right _ _).trans hD
  have hM' : M≤D := (le_max_left _ _).trans hMK
  have hK' : K≤D := (le_max_right _ _).trans hMK
  have hD2 : 2≤D := hN.trans hN'
  have hD1 : 1<D := by omega
  have hD0 : 0<D := by omega
  let R : ℂ := ∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
    lemma151BChiPsi D (n₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n
  let S : ℂ := ∑ dd∈n₁.divisorsAntidiagonal,
    actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151First D) dd.1*
    actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151Second D) dd.2
  have hnub : ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-
      χ.evalNat n₁*R‖≤(n₁.divisors.card : ℝ)*actual151NuError D := by
    rw [actual151_psi_arithmetic_sum_finite χ hD1 c j n₁
      (Nat.pos_of_ne_zero hn₁.1),←mul_sub,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one n₁)).trans
      (hnu D hM' χ hA j n₁)
  have hcoll : ‖χ.evalNat n₁*R-χ.evalNat n₁*S‖≤
      (n₁.divisors.card : ℝ)*roughCollisionUniformBudget D :=
    actual151_rho_convolution_collision χ hD0 (hK D hK') c j hn₁
  have hprod' : ‖χ.evalNat n₁*S-
      χ.evalNat n₁*(n₁.divisors.card : ℂ)*actual151MainConstant (j.val+1)‖≤
      (n₁.divisors.card : ℝ)*actual151ProductError D c := by
    rw [mul_assoc,←mul_sub,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one n₁)).trans
      (hprod D hN' j n₁ hnT)
  rw [lemma34_tau2_eq_divisor_card]
  calc
    _ ≤ ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-χ.evalNat n₁*R‖+
        ‖χ.evalNat n₁*R-χ.evalNat n₁*(n₁.divisors.card : ℂ)*
          actual151MainConstant (j.val+1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-χ.evalNat n₁*R‖+
        (‖χ.evalNat n₁*R-χ.evalNat n₁*S‖+
          ‖χ.evalNat n₁*S-χ.evalNat n₁*(n₁.divisors.card : ℂ)*
            actual151MainConstant (j.val+1)‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ (n₁.divisors.card : ℝ)*actual151NuError D+
        ((n₁.divisors.card : ℝ)*roughCollisionUniformBudget D+
          (n₁.divisors.card : ℝ)*actual151ProductError D c) :=
      add_le_add hnub (add_le_add hcoll hprod')
    _ = _ := by unfold actual151PointwiseError; ring

/-- The external character remains in the full error, so ramified n1 vanish
exactly and downstream absolute sums may retain |chi(n1)varpi(n1)|. -/
theorem actual151_repaired_quantitative_character {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,∀ n₁ : ℕ,
      Lemma151Supported (lemma151Q D) n₁ → (n₁ : ℝ)<lemma56PaperT D →
      ‖lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁-
        χ.evalNat n₁*(lemma34Tau 2 n₁ : ℂ)*actual151MainConstant (j.val+1)‖≤
        ‖χ.evalNat n₁‖*actual151PointwiseError D c*(lemma34Tau 2 n₁ : ℝ) := by
  obtain ⟨N,hN,h⟩ := actual151_repaired_quantitative hc
  refine ⟨N,hN,?_⟩
  intro D hD χ hA j n₁ hn₁ hnT
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (n₁ : ZMod D) with hχ | hχ | hχ
  · have hz : χ.evalNat n₁=0 := hχ
    rw [b_repaired_rough_sum χ (by omega) c j n₁,hz]
    simp
  · have ho : ‖χ.evalNat n₁‖=1 := by rw [show χ.evalNat n₁=1 from hχ,norm_one]
    rw [ho,one_mul]
    exact h D hD χ hA j n₁ hn₁ hnT
  · have ho : ‖χ.evalNat n₁‖=1 := by rw [show χ.evalNat n₁= -1 from hχ,norm_neg,norm_one]
    rw [ho,one_mul]
    exact h D hD χ hA j n₁ hn₁ hnT

end ZhangLS.Spec
