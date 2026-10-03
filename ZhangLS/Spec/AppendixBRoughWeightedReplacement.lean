import ZhangLS.Spec.AppendixBRoughReplacementB2

/-! Uniform weighted B.1+B.2 replacement. The outer n1 divisor weights,
rough product reindexing and strict sqrt(P) complementary tail remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Weighted rough-domain removal on an arbitrary finite subset, before rates. -/
theorem appendixB_weighted_rough_removal {D N : ℕ} (β : ℂ) (S : Finset ℕ)
    (hS : S⊆Icc 1 N) (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W)
    (hw : ∀ n∈S,‖w n‖≤W) :
    ‖(∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),w n*lemma151Rho β n/n)-
      (∑ n∈S,w n*lemma151Rho β n/n)‖≤
      W*(∑ n∈(Icc 1 N).filter (fun n => ¬n.Coprime (lemma151Q D)),appendixBRhoMass β n) := by
  have hsplit := sum_filter_add_sum_filter_not S (fun n => n.Coprime (lemma151Q D))
    (fun n => w n*lemma151Rho β n/n)
  have he : (∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),w n*lemma151Rho β n/n)-
      (∑ n∈S,w n*lemma151Rho β n/n)=
      -(∑ n∈S.filter (fun n => ¬n.Coprime (lemma151Q D)),w n*lemma151Rho β n/n) := by
    rw [←hsplit]; ring
  rw [he,norm_neg]
  calc
    _ ≤ ∑ n∈S.filter (fun n => ¬n.Coprime (lemma151Q D)),‖w n*lemma151Rho β n/n‖ := norm_sum_le _ _
    _ ≤ ∑ n∈S.filter (fun n => ¬n.Coprime (lemma151Q D)),W*appendixBRhoMass β n := by
      apply sum_le_sum
      intro n hn
      rw [norm_div,norm_mul,norm_natCast]
      change ‖w n‖*‖lemma151Rho β n‖/(n : ℝ)≤W*(‖lemma151Rho β n‖/(n : ℝ))
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (hw n (mem_filter.mp hn).1) (by positivity)
    _ = W*(∑ n∈S.filter (fun n => ¬n.Coprime (lemma151Q D)),appendixBRhoMass β n) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hS)
        (fun n _ _ => appendixB_rho_mass_nonneg β n)) hW

noncomputable def appendixBReplacementConstant : ℝ := 189+appendixBRoughRemovalConstant
lemma appendixB_replacement_constant_pos : 0<appendixBReplacementConstant := by
  unfold appendixBReplacementConstant
  linarith [appendixB_rough_removal_constant_pos]

/-- The actual weighted replacement, uniformly in bounded weights on the closed
P interval. It implies the original strict n<P statements by subset restriction. -/
theorem appendixB_weighted_replacement_explicit {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    {β : ℂ} (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D)
    (hN : 1≤N) (hNP : (N : ℝ)≤lemma23PaperP D)
    (S : Finset ℕ) (hS : S⊆Icc 1 N) (w : ℕ→ℂ) (W : ℝ) (hW : 0≤W)
    (hw : ∀ n∈S,‖w n‖≤W) :
    ‖(∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),w n*lemma151RhoStar χ β n/n)-
      (∑ n∈S,w n*lemma151Rho β n/n)‖≤
      appendixBReplacementConstant*W*lemma23PaperL D^(-8 : ℤ) := by
  have hP1 : 1≤lemma23PaperP D := by
    have : (1 : ℝ)≤N := by exact_mod_cast hN
    exact this.trans hNP
  have hcut : N≤lemma31PaperCutoff D := by
    apply (Nat.le_floor_iff (sq_nonneg (lemma23PaperP D))).mpr
    nlinarith only [hNP,hP1]
  let A := ∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),w n*lemma151RhoStar χ β n/n
  let B := ∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),w n*lemma151Rho β n/n
  let C := ∑ n∈S,w n*lemma151Rho β n/n
  have hB1 : ‖A-B‖≤189*W*lemma23PaperL D^(-1995 : ℤ) :=
    appendixB_weighted_B1_explicit χ hD hL hA hAbs hβre _
      (by
        intro n hn
        have hh := mem_Icc.mp (hS (mem_filter.mp hn).1)
        exact ⟨hh.1,hh.2.trans hcut,(mem_filter.mp hn).2⟩)
      w W hW (fun n hn => hw n (mem_filter.mp hn).1)
  have hB2 : ‖B-C‖≤W*(appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ)) :=
    (appendixB_weighted_rough_removal β S hS w W hW hw).trans
      (mul_le_mul_of_nonneg_left (appendixB_original_B2_explicit hL hN hNP hβre hβ) hW)
  have hpow : lemma23PaperL D^(-1995 : ℤ)≤lemma23PaperL D^(-8 : ℤ) :=
    zpow_le_zpow_right₀ hL (by norm_num)
  change ‖A-C‖≤_
  calc
    _ = ‖(A-B)+(B-C)‖ := by congr 1; ring
    _ ≤ ‖A-B‖+‖B-C‖ := norm_add_le _ _
    _ ≤ 189*W*lemma23PaperL D^(-1995 : ℤ)+
        W*(appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ)) := add_le_add hB1 hB2
    _ ≤ 189*W*lemma23PaperL D^(-8 : ℤ)+
        W*(appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hpow (by positivity)) le_rfl
    _ = _ := by unfold appendixBReplacementConstant; ring

/-- Uniform original finite-D j-shifts. The constants do not depend on χ, j,
cutoff, n1, or the external weight; c is fixed before the threshold. -/
theorem appendixB_weighted_replacement_uniform (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ N : ℕ,1≤N →
      (N : ℝ)≤lemma23PaperP D → ∀ S : Finset ℕ,S⊆Icc 1 N →
      ∀ w : ℕ→ℂ, ∀ W : ℝ,0≤W → (∀ n∈S,‖w n‖≤W) →
      ‖(∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),
          w n*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n)-
        (∑ n∈S,w n*lemma151Rho (lemma83PaperBeta D c j) n/n)‖≤
        appendixBReplacementConstant*W*lemma23PaperL D^(-8 : ℤ) := by
  obtain ⟨M,hM,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨K,hK⟩ := lemma31_exponential_absorption_threshold
  refine ⟨max M K,?_⟩
  intro D hD χ hA j N hN hNP S hS w W hW hw
  have hh := hK D ((le_max_right _ _).trans hD)
  exact appendixB_weighted_replacement_explicit χ hh.1 (by linarith [hh.2.1]) hA hh.2.2
    (lemma83_beta_re D c j) (lemma83_paper_beta_norm hh.2.1 hc
      (hsmall D ((le_max_left _ _).trans hD)) j) hN hNP S hS w W hW hw

/-- Concrete kernel weights retain n1 explicitly and cost exactly W=1. -/
theorem appendixB_kernel_replacement_uniform (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ N : ℕ,1≤N →
      (N : ℝ)≤lemma23PaperP D → ∀ S : Finset ℕ,S⊆Icc 1 N →
      ∀ X : ℝ, ∀ γ : ℂ,γ.re=0 → ∀ n₁ : ℕ,
      ‖(∑ n∈S.filter (fun n => n.Coprime (lemma151Q D)),
          lemma151Kernel X γ (n₁*n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n)-
        (∑ n∈S,lemma151Kernel X γ (n₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n)‖≤
        appendixBReplacementConstant*lemma23PaperL D^(-8 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := appendixB_weighted_replacement_uniform c hc
  refine ⟨D₀,?_⟩
  intro D hD χ hA j N hN hNP S hS X γ hγ n₁
  simpa only [mul_one] using hD₀ D hD χ hA j N hN hNP S hS
    (fun n => lemma151Kernel X γ (n₁*n)) 1 (by norm_num)
    (fun n _ => b_kernel_norm_le_one X γ hγ (n₁*n))

end ZhangLS.Spec
