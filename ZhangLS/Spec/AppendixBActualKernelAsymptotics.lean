import ZhangLS.Spec.AppendixBKernelRegressions
import ZhangLS.Spec.AppendixBRoughReplacementRegressions

/-! Actual rough rho-star kernels with the original finite-D shifts.
The P1 kernel here is full and untruncated; it is not the strict H14 kernel.
No rate is assigned to the paper's undefined alpha1. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Classical Topology

noncomputable def appendixBActualRoughKernelSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (X : ℝ) (β γ : ℂ) (n₁ : ℕ) : ℂ :=
  ∑' n : ℕ, if n.Coprime (lemma151Q D) then
    lemma151Kernel X γ (n₁*n)*lemma151RhoStar χ β n/n else 0

noncomputable def appendixBActualRoughError (D : ℕ) (c : ℝ) : ℝ :=
  appendixBReplacementConstant*lemma23PaperL D^(-8 : ℤ)+appendixBOriginalError D c

theorem appendixB_actual_rough_error_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun D : ℕ => appendixBActualRoughError D c) atTop (𝓝 0) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hz := ((tendsto_zpow_atTop_zero (by norm_num : (-8 : ℤ)<0)).comp ht).const_mul
    appendixBReplacementConstant
  simpa only [appendixBActualRoughError,mul_zero,zero_add] using
    hz.add (appendixB_original_error_tendsto_zero hc)

/-- One threshold precedes the actual character, both kernel indices and n1.
All original P2/P3/full-P1 cutoffs and pure imaginary modulation are retained. -/
theorem appendixB_actual_rough_kernels_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j μ : Fin 3, ∀ n₁ : ℕ,
      0<n₁ → (n₁ : ℝ)<lemma56PaperT D →
      ‖appendixBActualRoughKernelSum χ (appendixBOriginalCutoff D μ)
          (lemma83PaperBeta D c j) (appendixBOriginalGamma D μ) n₁-
        lemma151FullKernelConstant (appendixBOriginalExponent μ)
          (appendixBOriginalFrequency μ) (j.val+1)‖≤appendixBActualRoughError D c := by
  obtain ⟨N,hN,hfull⟩ := appendixB_original_printed_constants_uniform hc
  obtain ⟨M,hrough⟩ := appendixB_actual_kernel_rhostar_to_full_uniform c hc
  obtain ⟨K,hcuts⟩ := eventually_atTop.mp appendixB_original_cutoffs_eventually
  refine ⟨max N (max M K),hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j μ n₁ hn hnT
  have hN' : N≤D := (le_max_left _ _).trans hD
  have hMK : max M K≤D := (le_max_right _ _).trans hD
  have hM' : M≤D := (le_max_left _ _).trans hMK
  have hK' : K≤D := (le_max_right _ _).trans hMK
  have hXP := ((hcuts D hK').2 μ).2.2.1
  have hγ : (appendixBOriginalGamma D μ).re=0 := by
    by_cases hμ : μ=1 <;>
      simp [appendixBOriginalGamma,hμ,lemma151Beta6,lemma151Beta7]
  have hr := hrough D hM' χ hA j (appendixBOriginalCutoff D μ) hXP.le
    (appendixBOriginalGamma D μ) hγ n₁ hn
  have hr' : ‖appendixBActualRoughKernelSum χ (appendixBOriginalCutoff D μ)
      (lemma83PaperBeta D c j) (appendixBOriginalGamma D μ) n₁-
      appendixBFullKernelSum (appendixBOriginalCutoff D μ) (lemma83PaperBeta D c j)
        (appendixBOriginalGamma D μ) n₁‖≤
      appendixBReplacementConstant*lemma23PaperL D^(-8 : ℤ) := by
    simpa only [appendixBActualRoughKernelSum,appendixBFullKernelSum] using hr
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hr' (hfull D hN' j μ n₁ hn hnT))

/-- Uniform epsilon form for the actual rough source, with the full P1 scope. -/
theorem appendixB_actual_rough_kernels_little_o {c : ℝ} (hc : 0<c)
    (ε : ℝ) (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j μ : Fin 3, ∀ n₁ : ℕ,
      0<n₁ → (n₁ : ℝ)<lemma56PaperT D →
      ‖appendixBActualRoughKernelSum χ (appendixBOriginalCutoff D μ)
          (lemma83PaperBeta D c j) (appendixBOriginalGamma D μ) n₁-
        lemma151FullKernelConstant (appendixBOriginalExponent μ)
          (appendixBOriginalFrequency μ) (j.val+1)‖<ε := by
  obtain ⟨N,hN,h⟩ := appendixB_actual_rough_kernels_uniform hc
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((appendixB_actual_rough_error_tendsto_zero hc).eventually (gt_mem_nhds hε))
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j μ n₁ hn hnT
  exact (h D ((le_max_left _ _).trans hD) χ hA j μ n₁ hn hnT).trans_lt
    (hM D ((le_max_right _ _).trans hD))

end ZhangLS.Spec
