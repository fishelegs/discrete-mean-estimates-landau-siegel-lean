import ZhangLS.Spec.Lemma153DownstreamNormalization
/-! The local residue version of the main expression needed after15.3.
Sharp cutoff, N(Q) restriction and contour shift remain separate obligations. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def lemma153NormalizedCenterErrorConstant : ℝ :=
  lemma152ProductBound*lemma153PaperCenterConstant+
    lemma152ErrorConstant*lemma153UnramifiedProductBound
noncomputable def lemma153NormalizedResidueErrorConstant : ℝ :=
  lemma152ProductBound*lemma153PaperResidueErrorConstant+
    (16*Real.exp 1)^2*lemma153NormalizedCenterErrorConstant*Real.pi

lemma lemma153_normalized_center_error_constant_pos : 0<lemma153NormalizedCenterErrorConstant := by
  unfold lemma153NormalizedCenterErrorConstant
  have := lemma152_product_bound_pos
  have := lemma153_paper_center_constant_pos
  have := lemma152_error_constant_pos
  have := lemma153_unramified_product_bound_pos
  positivity

lemma lemma153_normalized_residue_error_constant_pos : 0<lemma153NormalizedResidueErrorConstant := by
  unfold lemma153NormalizedResidueErrorConstant
  have := lemma152_product_bound_pos
  have := lemma153_paper_residue_error_constant_pos
  have := lemma153_normalized_center_error_constant_pos
  positivity

/-- Actual M₁ times the actual repaired residue has exactly the required main
term a·φ(D)/D, with an absolute O(L^-3) error. The theorem does not identify
this residue with the sharp n<T sum or its N(Q)-restricted counterpart. -/
theorem lemma153_paper_normalized_actual_residue {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c) 1 1 (1-lemma83PaperBeta D c j)*
          lemma153ActualResidue χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)-
        (lemma171MainTerm χ:ℂ)*((Nat.totient D:ℂ)/(D:ℂ))‖≤
          lemma153NormalizedResidueErrorConstant*lemma23PaperL D^(-3:ℤ) := by
  obtain ⟨D₁,hD1,hres⟩ := lemma153_paper_actual_residue_estimate hc
  obtain ⟨D₂,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₃,hD3,hcenter⟩ := lemma153_paper_repaired_center_estimate hc
  refine ⟨max D₁ (max D₂ D₃),hD1.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j
  have hD1' : D₁≤D := (le_max_left _ _).trans hD
  have hD2' : D₂≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hD3' : D₃≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hDthree : 3≤D := hD1.trans hD1'
  have hD' : 1<D := by omega
  have hDne : D≠0 := by omega
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD2')).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  let β := lemma152PaperBeta D c
  let γ := lemma83PaperBeta D c j
  let M := lemma153GeneralMEulerProduct χ β 1 1 (1-γ)
  let U := lemma153EulerProduct χ β γ 1
  let M₀ := lemma152MainTerm χ
  let U₀ := lemma153MainTerm χ
  let R := lemma153ActualResidue χ β γ
  let d := LDerivAtOne χ
  have hR : ‖R-U*d^2‖≤lemma153PaperResidueErrorConstant*lemma23PaperL D^(-3:ℤ) := hres D hD1' χ hA j
  have hM : ‖M‖≤lemma152ProductBound := lemma153_general_M_normalization_uniform_bound χ β
    (lemma152_beta_re D c) γ (lemma83_beta_re D c j)
  have hU₀ : ‖U₀‖≤lemma153UnramifiedProductBound := lemma153_main_U_uniform_bound hDne χ
  have hUdist : ‖U-U₀‖≤lemma153PaperCenterConstant*lemma44PaperAlpha D := hcenter D hD3' χ j
  have hγnorm := lemma153_paper_beta_norm_le hL hc (hsmall D hD2') j
  have hMdist : ‖M-M₀‖≤lemma152ErrorConstant*lemma44PaperAlpha D := by
    dsimp [M,M₀]
    rw [lemma153_general_m_baseline]
    exact lemma152_paper_estimate χ hc hL (hsmall D hD2') (1-γ) (by
      simp only [sub_sub_cancel_left,norm_neg]
      dsimp [γ]
      linarith only [hγnorm,ha])
  have hprod : ‖M*U-M₀*U₀‖≤lemma153NormalizedCenterErrorConstant*lemma44PaperAlpha D := by
    rw [show M*U-M₀*U₀=M*(U-U₀)+(M-M₀)*U₀ by ring]
    calc
      _ ≤ ‖M*(U-U₀)‖+‖(M-M₀)*U₀‖ := norm_add_le _ _
      _ ≤ lemma152ProductBound*(lemma153PaperCenterConstant*lemma44PaperAlpha D)+
        (lemma152ErrorConstant*lemma44PaperAlpha D)*lemma153UnramifiedProductBound := by
        simp only [norm_mul]
        have := lemma152_product_bound_pos
        have := lemma153_paper_center_constant_pos
        have := lemma152_error_constant_pos
        have := lemma153_unramified_product_bound_pos
        gcongr
      _ = _ := by unfold lemma153NormalizedCenterErrorConstant; ring
  have hprodderiv : ‖d^2*(M*U-M₀*U₀)‖≤
      ((16*Real.exp 1)^2*lemma153NormalizedCenterErrorConstant*Real.pi)*lemma23PaperL D^(-5:ℤ) :=
    paper_actual_LDeriv_error_budget χ hD' (by linarith) hprod
  have hscale : lemma23PaperL D^(-5:ℤ)≤lemma23PaperL D^(-3:ℤ) := by
    rw [←Real.rpow_intCast,←Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hmain : M₀*U₀*d^2=(lemma171MainTerm χ:ℂ)*((Nat.totient D:ℂ)/(D:ℂ)) :=
    lemma153_zero_MU_LDeriv_main_term χ hD'
  change ‖M*R-(lemma171MainTerm χ:ℂ)*((Nat.totient D:ℂ)/(D:ℂ))‖≤_
  rw [←hmain,show M*R-M₀*U₀*d^2=M*(R-U*d^2)+d^2*(M*U-M₀*U₀) by ring]
  calc
    _ ≤ ‖M*(R-U*d^2)‖+‖d^2*(M*U-M₀*U₀)‖ := norm_add_le _ _
    _ ≤ lemma152ProductBound*(lemma153PaperResidueErrorConstant*lemma23PaperL D^(-3:ℤ))+
      ((16*Real.exp 1)^2*lemma153NormalizedCenterErrorConstant*Real.pi)*lemma23PaperL D^(-5:ℤ) := by
      apply add_le_add _ hprodderiv
      rw [norm_mul]
      exact mul_le_mul hM hR (norm_nonneg _) lemma152_product_bound_pos.le
    _ ≤ lemma152ProductBound*(lemma153PaperResidueErrorConstant*lemma23PaperL D^(-3:ℤ))+
      ((16*Real.exp 1)^2*lemma153NormalizedCenterErrorConstant*Real.pi)*lemma23PaperL D^(-3:ℤ) := by
      have := lemma153_normalized_center_error_constant_pos
      gcongr
    _ = _ := by unfold lemma153NormalizedResidueErrorConstant; ring

end ZhangLS.Spec
