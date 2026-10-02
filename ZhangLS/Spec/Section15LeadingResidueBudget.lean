import ZhangLS.Spec.Section15ResidueCertification
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology
set_option maxHeartbeats 2000000

noncomputable def section15LeadingProductConstant (c : ℝ) : ℝ :=
  510*section15FactorConstant+lemma153GeometricErrorConstant c*Real.pi

lemma section15_leading_product_constant_pos {c : ℝ} (hc : 0<c) :
    0<section15LeadingProductConstant c := by
  unfold section15LeadingProductConstant
  have hC := section15_factor_constant_bounds.1
  have hG := lemma153_geometric_error_constant_pos hc
  positivity

lemma section15_alpha_logT_le_L6 {D : ℕ} (hL : 1≤lemma23PaperL D) :
    lemma44PaperAlpha D*Real.log (lemma56PaperT D)≤Real.pi*lemma23PaperL D^(-6:ℤ) := by
  calc
    _ = Real.pi*(Real.log (lemma56PaperT D)/Real.log (lemma23PaperP D)) := by unfold lemma44PaperAlpha; ring
    _ ≤ Real.pi*lemma23PaperL D^(-7:ℤ) := mul_le_mul_of_nonneg_left (paper_boundary_scale_le_L7 hL) Real.pi_pos.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hL (by norm_num)) Real.pi_pos.le

/-- The source's three actual products have leading values (1,2,1) with
O(L^-6) for fixed c-prime, proved rather than obtained by relabeling printed O(L^-1). -/
theorem section15_actual_r_product_leading_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hδ : ‖lemma54PaperDeltaMellin D 1-1‖≤(lemma54Constant*Real.pi)*lemma23PaperL D^(-6:ℤ))
    (hbudget : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2) (j : Fin 3) :
    ‖section15ActualRStar χ (lemma83PaperBeta D c)*
      section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
        lemma153LeadingWeight j‖≤section15LeadingProductConstant c*lemma23PaperL D^(-6:ℤ) := by
  have hL : 3≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith only [this]
  have hr := section15_actual_r_product_error χ hDN hA hc hsmall hδ hbudget j
  have hg := lemma153_actual_geometric_weight_bound hL hc hsmall j
  have hG : 0≤lemma153GeometricErrorConstant c := (lemma153_geometric_error_constant_pos hc).le
  have hg' : ‖lemma153GeometricWeight D c j-lemma153LeadingWeight j‖≤
      (lemma153GeometricErrorConstant c*Real.pi)*lemma23PaperL D^(-6:ℤ) := by
    apply hg.trans
    have hh := mul_le_mul_of_nonneg_left (section15_alpha_logT_le_L6 (by linarith : 1≤lemma23PaperL D)) hG
    simpa only [mul_assoc] using hh
  calc
    _ ≤ ‖section15ActualRStar χ (lemma83PaperBeta D c)*
      section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
        lemma153GeometricWeight D c j‖+
      ‖lemma153GeometricWeight D c j-lemma153LeadingWeight j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (510*section15FactorConstant)*lemma23PaperL D^(-6:ℤ)+
      (lemma153GeometricErrorConstant c*Real.pi)*lemma23PaperL D^(-6:ℤ) := add_le_add hr hg'
    _ = _ := by unfold section15LeadingProductConstant; ring

/-- Final local compatibility capstone: multiplying the actual three residue
products by the actual a preserves the original leading (1,2,1) combination
with an error tending to zero. This asserts no Mellin shift, unsmoothing,
N(Q) deletion, prime average, or outer D/φ(D) consumer theorem. -/
theorem section15_actual_weighted_leading_residue_budget {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖(lemma171MainTerm χ:ℂ)*(section15ActualRStar χ (lemma83PaperBeta D c)*
        section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
          lemma153LeadingWeight j)‖≤
        (lemma32RegularProductBound (3/4)*(16*Real.exp 1)^2*section15LeadingProductConstant c)*
          lemma23PaperL D^(-2:ℤ) := by
  obtain ⟨D₁,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₂,hδ⟩ := section15_actual_delta_error_threshold
  obtain ⟨D₃,hbudget⟩ := section15_budget_threshold
  refine ⟨max 3 (max lemma57ExplicitModulusThreshold (max D₁ (max D₂ D₃))),le_max_left _ _,?_⟩
  intro D hD χ hA j
  have hDN : lemma57ExplicitModulusThreshold≤D := by omega
  have hD1 : D₁≤D := by omega
  have hD2 : D₂≤D := by omega
  have hD3 : D₃≤D := by omega
  have hb : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2 := (hbudget D hD3).trans (by norm_num)
  exact section15_actual_a_L6_budget χ (lemma57_one_lt_of_explicit_threshold hDN)
    (by linarith [(hδ D hD2).1])
    (section15_actual_r_product_leading_error χ hDN hA hc (hshift D hD1) (hδ D hD2).2 hb j)

end ZhangLS.Spec
