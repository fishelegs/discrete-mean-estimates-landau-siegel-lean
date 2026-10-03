import ZhangLS.Spec.AppendixBTailGaussianComparison
import ZhangLS.Spec.AppendixBTailSourceUnsmoothing
import ZhangLS.Spec.AppendixBTailTerminalResidue

/-! Actual sharp complementary arithmetic tail: finite strict-step assembly,
genuine infinite Gaussian intermediary, all contour sides, and finite-D residue.
Only the finite sharp slice and continuous exact residue are integrated in z. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace ZhangLS.Spec
open Complex MeasureTheory Filter Set

noncomputable def appendixBSharpTailError (D : ℕ) (c : ℝ) : ℝ :=
  (appendixBTailContourBudget D+2*appendixBSingleUnsmoothingBudget D+
    10*c*Real.pi*lemma23PaperL D/lemma23PaperL D^9+240*Real.pi/lemma23PaperL D^9)/126

/-- Direct comparison of the actual strict-complement arithmetic sum with its
integrated exact finite-D residue. No Gaussian z integral is substituted. -/
theorem appendixB_actual_tail_to_exact_residue_uniform :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ β γ : ℂ,
      β.re=0 → β≠0 → ‖β‖≤3*lemma44PaperAlpha D →
      γ.re=0 → γ≠0 → ‖γ‖≤3*lemma44PaperAlpha D →
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ)) β γ l₁-
        appendixBIntegratedExactTailResidue D β γ‖≤
        (appendixBTailContourBudget D+2*appendixBSingleUnsmoothingBudget D)/126 := by
  obtain ⟨N,hN,hgauss⟩ := appendixB_source_gaussian_slice_quantitative
  obtain ⟨M,hM,hunsmooth⟩ := appendixB_source_unsmoothing_uniform
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD
  obtain ⟨hL,hG⟩ := hgauss D ((le_max_left _ _).trans hD)
  have hU := (hunsmooth D ((le_max_right _ _).trans hD)).2
  have hLp : 0<lemma23PaperL D := by linarith
  refine ⟨hL,?_⟩
  intro β γ hβre hβ0 hβ hγre hγ0 hγ l₁ hl hlT
  let S := appendixBSharpSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊
  let G := fun z : ℝ => appendixBSourceGaussianSlice D (lemma23PaperL D^9) z β γ l₁
  let R := fun z : ℝ => lemma151ExactTailResidue D (lemma23PaperL D^9) z β γ
  let E := appendixBTailContourBudget D+2*appendixBSingleUnsmoothingBudget D
  have hpoint (z : ℝ) (hz : z∈Icc (0.5 : ℝ) 0.504) : ‖S z-R z‖≤E := by
    have hu := hU β γ hβre hβ hγre l₁ hl hlT z hz
    have hg := hG β γ hβre hβ0 hβ hγre hγ0 hγ l₁ hl hlT z hz
    have ht := norm_add_le (S z-G z) (G z-R z)
    rw [sub_add_sub_cancel,norm_sub_rev (S z) (G z)] at ht
    dsimp [E]
    linarith only [ht,hu,hg]
  have hSi : IntervalIntegrable S volume (0.5 : ℝ) 0.504 :=
    appendixB_sharp_source_slice_intervalIntegrable hLp β γ hl _
  have hRc : Continuous R := by
    dsimp [R,lemma151ExactTailResidue,lemma151TailNumerator]
    fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0.5 : ℝ)) (b := (0.504 : ℝ)) (f := fun z => S z-R z) (C := E) (by
      intro z hz
      rw [Set.uIoc_of_le (by norm_num : (0.5 : ℝ)≤0.504)] at hz
      exact hpoint z ⟨hz.1.le,hz.2⟩)
  rw [appendixB_actual_complement_finite_integral hLp β γ hl]
  unfold appendixBIntegratedExactTailResidue
  change ‖(1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504, S z)-
      (1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504, R z)‖≤_
  rw [←mul_sub,←intervalIntegral.integral_sub hSi (hRc.intervalIntegrable _ _),norm_mul]
  norm_num at hi ⊢
  have hh := mul_le_mul_of_nonneg_left hi (show 0≤(125/63 : ℝ) by norm_num)
  exact hh.trans_eq (by dsimp [E]; ring)

/-- Direct original-shift capstone for the true >=sqrt(P) complementary sum,
including equality. The error is explicit and independent of j and l1. -/
theorem appendixB_actual_sharp_tail_quantitative {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
          (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
        (-I*Real.pi*(j.val+1)*lemma151BStar)‖≤appendixBSharpTailError D c := by
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_tail_to_exact_residue_uniform
  obtain ⟨M,hM,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD j l₁ hl hlT
  obtain ⟨hL,hcapD⟩ := hcap D ((le_max_left _ _).trans hD)
  have hs := hsmall D ((le_max_right _ _).trans hD)
  have hLp : 0<lemma23PaperL D := by linarith
  have hα := lemma83_alpha_small (by linarith : 100≤lemma23PaperL D)
  have hβ := lemma83_paper_beta_norm (by linarith : 3≤lemma23PaperL D) hc hs j
  have hβ0 := appendixB_actual_beta_ne_zero hc hLp hs j
  have hg := appendixB_original_gamma D (0 : Fin 3) hα.1
  have hγre : (lemma151Beta6 D).re=0 := by simpa [appendixBOriginalGamma] using hg.1
  have hγ0 : lemma151Beta6 D≠0 := by simpa [appendixBOriginalGamma] using hg.2.1
  have hγ : ‖lemma151Beta6 D‖≤3*lemma44PaperAlpha D := by simpa [appendixBOriginalGamma] using hg.2.2
  have ha := hcapD (lemma83PaperBeta D c j) (lemma151Beta6 D)
    (lemma83_beta_re D c j) hβ0 hβ hγre hγ0 hγ l₁ hl hlT
  have hr := appendixB_integrated_tail_bstar_rate (by linarith : 100≤lemma23PaperL D) hc hs j
  have ht := norm_add_le
    (appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
      (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
      appendixBIntegratedExactTailResidue D (lemma83PaperBeta D c j) (lemma151Beta6 D))
    (appendixBIntegratedExactTailResidue D (lemma83PaperBeta D c j) (lemma151Beta6 D)-
      (-I*Real.pi*(j.val+1)*lemma151BStar))
  rw [sub_add_sub_cancel] at ht
  exact ht.trans ((add_le_add ha hr).trans_eq (by unfold appendixBSharpTailError; ring))

end ZhangLS.Spec
