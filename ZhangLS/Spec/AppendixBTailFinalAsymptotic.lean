import ZhangLS.Spec.AppendixBTailArithmeticComparison
import ZhangLS.Spec.AppendixBTailUnsmoothingDecay

/-! Two separate final interfaces: an L^-14 comparison with the exact finite-D
residue, and an original-shift terminal model with the explicit c L^-8 + L^-9
correction. All thresholds precede the l1 and j quantifiers. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex Filter Topology

noncomputable def appendixBExactTailErrorConstant : ℝ :=
  (8*Real.exp (3*Real.pi)+3)/126

noncomputable def appendixBTerminalTailErrorConstant (c : ℝ) : ℝ :=
  (10*c*Real.pi+240*Real.pi+8*Real.exp (3*Real.pi)+3)/126

lemma appendixB_exact_tail_budget_eventual_power :
    ∀ᶠ D : ℕ in atTop,
      (appendixBTailContourBudget D+2*appendixBSingleUnsmoothingBudget D)/126≤
        appendixBExactTailErrorConstant*lemma23PaperL D^(-(14 : ℤ)) := by
  filter_upwards [appendixB_tail_contour_budget_eventual_power 14,
    appendixB_unsmoothing_budget_eventual_power] with D hB hU
  simp only [zpow_neg,zpow_natCast,zpow_ofNat] at hB hU ⊢
  unfold appendixBExactTailErrorConstant
  linarith only [hB.2,hU]

/-- The actual >=sqrt(P) arithmetic tail retains its entire exact finite-D
residue to L^-14, uniformly for every positive l1<T. -/
theorem appendixB_actual_tail_exact_residue_power :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ β γ : ℂ, β.re=0 → β≠0 → ‖β‖≤3*lemma44PaperAlpha D →
      γ.re=0 → γ≠0 → ‖γ‖≤3*lemma44PaperAlpha D →
      ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ)) β γ l₁-
        appendixBIntegratedExactTailResidue D β γ‖≤
        appendixBExactTailErrorConstant*lemma23PaperL D^(-(14 : ℤ)) := by
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_tail_to_exact_residue_uniform
  obtain ⟨M,hM⟩ := eventually_atTop.mp appendixB_exact_tail_budget_eventual_power
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD β γ hβre hβ0 hβ hγre hγ0 hγ l₁ hl hlT
  exact ((hcap D ((le_max_left _ _).trans hD)).2 β γ hβre hβ0 hβ hγre hγ0 hγ l₁ hl hlT).trans
    (hM D ((le_max_right _ _).trans hD))

lemma appendixB_sharp_tail_error_eventual_detailed (c : ℝ) :
    ∀ᶠ D : ℕ in atTop, appendixBSharpTailError D c≤
      (10*c*Real.pi*lemma23PaperL D^(-(8 : ℤ))+
        240*Real.pi*lemma23PaperL D^(-(9 : ℤ)))/126+
      appendixBExactTailErrorConstant*lemma23PaperL D^(-(14 : ℤ)) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [appendixB_exact_tail_budget_eventual_power,ht.eventually_ge_atTop 1]
    with D hB hL
  have hLp : 0<lemma23PaperL D := lt_of_lt_of_le zero_lt_one hL
  have h8 : lemma23PaperL D/lemma23PaperL D^9=lemma23PaperL D^(-(8 : ℤ)) := by
    simp only [zpow_neg,zpow_natCast,zpow_ofNat]
    field_simp [hLp.ne'] <;> ring
  have h9 : 1/lemma23PaperL D^9=lemma23PaperL D^(-(9 : ℤ)) := by
    simp only [zpow_neg,zpow_natCast,zpow_ofNat,one_div]
  unfold appendixBSharpTailError
  have he : 10*c*Real.pi*lemma23PaperL D/lemma23PaperL D^9=
      10*c*Real.pi*lemma23PaperL D^(-(8 : ℤ)) := by rw [←h8]; ring
  have he' : 240*Real.pi/lemma23PaperL D^9=
      240*Real.pi*lemma23PaperL D^(-(9 : ℤ)) := by rw [←h9]; ring
  rw [he,he']
  simp only [zpow_neg,zpow_natCast,zpow_ofNat] at hB ⊢
  linarith only [hB]

lemma appendixB_sharp_tail_error_eventual_power (c : ℝ) :
    ∀ᶠ D : ℕ in atTop, appendixBSharpTailError D c≤
      appendixBTerminalTailErrorConstant c*lemma23PaperL D^(-(8 : ℤ)) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [appendixB_sharp_tail_error_eventual_detailed c,ht.eventually_ge_atTop 1]
    with D hB hL
  have h9 := mul_le_mul_of_nonneg_left
    (zpow_le_zpow_right₀ hL (by norm_num : -(9 : ℤ)≤ -8))
    (show 0≤240*Real.pi by positivity [Real.pi_pos])
  have h14 := mul_le_mul_of_nonneg_left
    (zpow_le_zpow_right₀ hL (by norm_num : -(14 : ℤ)≤ -8))
    (show 0≤appendixBExactTailErrorConstant by unfold appendixBExactTailErrorConstant; positivity)
  unfold appendixBTerminalTailErrorConstant appendixBExactTailErrorConstant at *
  nlinarith only [hB,h9,h14]

/-- The separate finite-D correction is exposed before weakening the three
powers to a single O_c(L^-8) bound. -/
theorem appendixB_actual_tail_terminal_detailed {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
          (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
        (-I*Real.pi*(j.val+1)*lemma151BStar)‖≤
      (10*c*Real.pi*lemma23PaperL D^(-(8 : ℤ))+
        240*Real.pi*lemma23PaperL D^(-(9 : ℤ)))/126+
      appendixBExactTailErrorConstant*lemma23PaperL D^(-(14 : ℤ)) := by
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_sharp_tail_quantitative hc
  obtain ⟨M,hM⟩ := eventually_atTop.mp (appendixB_sharp_tail_error_eventual_detailed c)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD j l₁ hl hlT
  exact (hcap D ((le_max_left _ _).trans hD) j l₁ hl hlT).trans
    (hM D ((le_max_right _ _).trans hD))

/-- Original beta_j and beta6, with a quantitative error at the proved
O_c(L^-8) rate and all support boundaries unchanged. -/
theorem appendixB_actual_tail_terminal_power {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
          (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
        (-I*Real.pi*(j.val+1)*lemma151BStar)‖≤
        appendixBTerminalTailErrorConstant c*lemma23PaperL D^(-(8 : ℤ)) := by
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_sharp_tail_quantitative hc
  obtain ⟨M,hM⟩ := eventually_atTop.mp (appendixB_sharp_tail_error_eventual_power c)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD j l₁ hl hlT
  exact (hcap D ((le_max_left _ _).trans hD) j l₁ hl hlT).trans
    (hM D ((le_max_right _ _).trans hD))

/-- A single genuine epsilon threshold works for all j and every positive l1<T. -/
theorem appendixB_actual_tail_terminal_uniform {c : ℝ} (hc : 0<c)
    {ε : ℝ} (hε : 0<ε) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ))
          (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
        (-I*Real.pi*(j.val+1)*lemma151BStar)‖<ε := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := ((tendsto_pow_neg_atTop (𝕜 := ℝ) (n := 8) (by norm_num)).comp ht).const_mul
    (appendixBTerminalTailErrorConstant c)
  simp only [mul_zero] at hp
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds hε))
  obtain ⟨N,hN,hcap⟩ := appendixB_actual_tail_terminal_power hc
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro D hD j l₁ hl hlT
  exact (hcap D ((le_max_left _ _).trans hD) j l₁ hl hlT).trans_lt
    (hM D ((le_max_right _ _).trans hD))

end ZhangLS.Spec
