import ZhangLS.Spec.AppendixBTailFinalAsymptotic
import ZhangLS.Spec.AppendixBTailRegressions

/-! Consequences for the actual strict H14 coefficient. The full P1 sum stays
explicit in the precise interface; the terminal interface uses the separate
verified full-kernel asymptotic. No assertion about the final matrix is made. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex Filter Topology

/-- The finite-D residue is exactly independent of the integer shift. -/
theorem appendixB_tail_residue_exact_shift_independence (D : ℕ) (L z : ℝ)
    {β γ : ℂ} (hβ : β≠0) (hβ1 : 1-β≠0) (hγ : γ≠0) (l₁ l₂ : ℕ) :
    appendixBTailHolomorphicNumerator D L z β γ l₁ 0=
      appendixBTailHolomorphicNumerator D L z β γ l₂ 0 := by
  rw [appendixB_tail_holomorphic_at_zero D L z l₁ hβ hβ1 hγ,
    appendixB_tail_holomorphic_at_zero D L z l₂ hβ hβ1 hγ]

/-- Exact-residue control of true H14 keeps the full finite-D P1 arithmetic
sum intact for any later logarithmic-moment or convolution calculation. -/
theorem appendixB_actual_h14_exact_residue_power :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ β : ℂ, β.re=0 → β≠0 → ‖β‖≤3*lemma44PaperAlpha D →
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖(∑' n : ℕ, bH14Coefficient D (l₁*n)*lemma151Rho β n/n)-
        (appendixBFullKernelSum (lemma151P1 D) β (lemma151Beta6 D) l₁-
          appendixBIntegratedExactTailResidue D β (lemma151Beta6 D))‖≤
        appendixBExactTailErrorConstant*lemma23PaperL D^(-(14 : ℤ)) := by
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_tail_exact_residue_power
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 100)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD β hβre hβ0 hβ l₁ hl hlT
  have hL := hM D ((le_max_right _ _).trans hD)
  have hα := (lemma83_alpha_small hL).1
  have hg := appendixB_original_gamma D (0 : Fin 3) hα
  have hγre : (lemma151Beta6 D).re=0 := by simpa [appendixBOriginalGamma] using hg.1
  have hγ0 : lemma151Beta6 D≠0 := by simpa [appendixBOriginalGamma] using hg.2.1
  have hγ : ‖lemma151Beta6 D‖≤3*lemma44PaperAlpha D := by simpa [appendixBOriginalGamma] using hg.2.2
  have hh := hcap D ((le_max_left _ _).trans hD) β (lemma151Beta6 D)
    hβre hβ0 hβ hγre hγ0 hγ l₁ hl hlT
  rw [appendixB_actual_h14_sum D β hl,sub_sub_sub_cancel_left,norm_sub_rev]
  exact hh

noncomputable def appendixBH14TerminalConstant (j : ℕ) : ℂ :=
  lemma151FullKernelConstant 0.504 (3/2) j+I*Real.pi*j*lemma151BStar

/-- The actual strict H14 terminal constant is full e1-prime plus i*pi*j*b-star.
Its two independently verified error budgets are both shown. -/
theorem appendixB_actual_h14_terminal_quantitative {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖(∑' n : ℕ, bH14Coefficient D (l₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n)-
        appendixBH14TerminalConstant (j.val+1)‖≤
        appendixBOriginalError D c+appendixBSharpTailError D c := by
  obtain ⟨N,hN,hfull⟩ := appendixB_original_printed_constants_uniform hc
  obtain ⟨M,hM,htail⟩ := appendixB_actual_sharp_tail_quantitative hc
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD j l₁ hl hlT
  have hf := hfull D ((le_max_left _ _).trans hD) j (0 : Fin 3) l₁ hl hlT
  have htailD := htail D ((le_max_right _ _).trans hD) j l₁ hl hlT
  change ‖appendixBFullKernelSum (lemma151P1 D) (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
    lemma151FullKernelConstant 0.504 (3/2) (j.val+1)‖≤appendixBOriginalError D c at hf
  rw [appendixB_actual_h14_sum D (lemma83PaperBeta D c j) hl]
  unfold appendixBH14TerminalConstant
  have he : appendixBFullKernelSum (lemma151P1 D) (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
      appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
        (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
      (lemma151FullKernelConstant 0.504 (3/2) (j.val+1)+I*Real.pi*(j.val+1)*lemma151BStar)=
      (appendixBFullKernelSum (lemma151P1 D) (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
        lemma151FullKernelConstant 0.504 (3/2) (j.val+1))-
      (appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
        (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
        (-I*Real.pi*(j.val+1)*lemma151BStar)) := by ring
  push_cast
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hf htailD)

/-- The original H14 rho sum has one epsilon threshold for all three shifts
and every positive l1<T, with the strict source coefficient kept literally. -/
theorem appendixB_actual_h14_terminal_uniform {c : ℝ} (hc : 0<c)
    {ε : ℝ} (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖(∑' n : ℕ, bH14Coefficient D (l₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n)-
        appendixBH14TerminalConstant (j.val+1)‖<ε := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := ((tendsto_pow_neg_atTop (𝕜 := ℝ) (n := 8) (by norm_num)).comp ht).const_mul
    (appendixBTerminalTailErrorConstant c)
  have hsum := (appendixB_original_error_tendsto_zero hc).add hp
  simp only [mul_zero,add_zero] at hsum
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hsum.eventually (gt_mem_nhds hε))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (appendixB_sharp_tail_error_eventual_power c)
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_h14_terminal_quantitative hc
  refine ⟨max N (max M K),hN.trans (le_max_left _ _),?_⟩
  intro D hD j l₁ hl hlT
  have hMK : max M K≤D := (le_max_right _ _).trans hD
  exact ((hcap D ((le_max_left _ _).trans hD) j l₁ hl hlT).trans
    (add_le_add le_rfl (hK D ((le_max_right _ _).trans hMK)))).trans_lt
      (hM D ((le_max_left _ _).trans hMK))

end ZhangLS.Spec
