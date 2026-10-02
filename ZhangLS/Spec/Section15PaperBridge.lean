import ZhangLS.Spec.Section15ResidueProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma section15_actual_shift_data {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) :
    (∀ j, lemma83PaperBeta D c j≠0) ∧ Function.Injective (lemma83PaperBeta D c) := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hb (j : Fin 3) : lemma83PaperBeta D c j≠0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0<lemma44PaperAlpha D/2)
      (section15_actual_beta_norm_lower hL hc hsmall j))
  have hb1 : lemma52PaperBetaOne D c≠0 := hb 0
  have hb2 : lemma52PaperBetaTwo D c≠0 := hb 1
  have hδ : 0≤c*lemma44PaperAlpha D*lemma23PaperL D := by positivity
  have h7 : (1:ℂ)+7*((c*lemma44PaperAlpha D*lemma23PaperL D:ℝ):ℂ)≠0 := by
    have : 0<1+7*(c*lemma44PaperAlpha D*lemma23PaperL D) := by linarith
    exact_mod_cast this.ne'
  have hf := lemma153_actual_beta_factorization D c
  have hgap : lemma52PaperBetaTwo D c-lemma52PaperBetaOne D c =
      I*(lemma44PaperAlpha D:ℂ)*(1+7*((c*lemma44PaperAlpha D*lemma23PaperL D:ℝ):ℂ)) := by
    rw [hf.1,hf.2.1]; ring
  have h10 : lemma52PaperBetaTwo D c≠lemma52PaperBetaOne D c := by
    apply sub_ne_zero.mp
    rw [hgap]
    exact mul_ne_zero (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')) h7
  have h20 : lemma52PaperBetaThree D c≠lemma52PaperBetaOne D c := by
    apply sub_ne_zero.mp
    rw [lemma153_beta_gap_one]
    exact hb2
  have h21 : lemma52PaperBetaThree D c≠lemma52PaperBetaTwo D c := by
    apply sub_ne_zero.mp
    rw [lemma153_beta_gap_two]
    exact hb1
  refine ⟨hb,?_⟩
  intro i j he
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (h10 he.symm)
  · exact False.elim (h20 he.symm)
  · exact False.elim (h10 he)
  · rfl
  · exact False.elim (h21 he.symm)
  · exact False.elim (h20 he)
  · exact False.elim (h21 he)
  · rfl

lemma section15_actual_denominators_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hbudget : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2) (j : Fin 3) :
    LDerivAtOne χ≠0 ∧ dirichletLFunction χ (1-lemma83PaperBeta D c j)≠0 ∧
      zetaPoleRemoved (1-lemma83PaperBeta D c j)≠0 := by
  have hL : 3≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith
  have hq : 0≤lemma23PaperL D^(-6:ℤ) := by positivity
  have hC := section15_factor_constant_bounds
  have hCl : section15LRelativeConstant≤section15FactorConstant := by linarith [section15_l_relative_constant_pos]
  have hCz : 15*Real.pi≤section15FactorConstant := by linarith [Real.pi_pos]
  have hl := (section15_actual_beta_L_relative_error χ hDN hA hc hsmall j).2
  have hz := (section15_actual_zeta_factor_errors hL hc hsmall j 0).2
  have hk : section15LFactor χ (-lemma83PaperBeta D c j)≠0 :=
    section15_ne_zero_of_near_one hl (lt_of_le_of_lt ((mul_le_mul_of_nonneg_right hCl hq).trans hbudget) (by norm_num))
  have hz' : zetaPoleRemoved (1-lemma83PaperBeta D c j)≠0 :=
    section15_ne_zero_of_near_one hz (lt_of_le_of_lt ((mul_le_mul_of_nonneg_right hCz hq).trans hbudget) (by norm_num))
  refine ⟨norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (section15_derivative_lower χ hDN hA)),?_,hz'⟩
  have hh := (div_ne_zero_iff.mp hk).1
  simpa only [section15LFactor,←sub_eq_add_neg] using hh

lemma section15_actual_geometric_eq (D : ℕ) (c : ℝ) (j : Fin 3) :
    section15Geometric (lemma83PaperBeta D c) (lemma61PaperP4 D) j=lemma153GeometricWeight D c j := by
  rfl

lemma section15_actual_geometric_norm {D : ℕ} {c : ℝ}
    (hD : 1<D) (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖lemma153GeometricWeight D c j‖≤2 := by
  have hr := (lemma153_actual_shift_ratio_bounds hL hc hsmall j).1
  have hp : ‖(lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma83PaperBeta D c j)‖=1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lemma61_P4_pos hD)]
    have h3 := lemma83_beta_re D c 2
    change (lemma52PaperBetaThree D c).re=0 at h3
    simp [Complex.sub_re,h3,lemma83_beta_re]
  simpa only [lemma153GeometricWeight,norm_mul,hp,mul_one] using hr

/-- The actual r₁*r₁ⱼ, not just its geometric model, is within absolute
O(L^-6) of Gⱼ. -/
theorem section15_actual_r_product_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hδ : ‖lemma54PaperDeltaMellin D 1-1‖≤(lemma54Constant*Real.pi)*lemma23PaperL D^(-6:ℤ))
    (hbudget : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2) (j : Fin 3) :
    ‖section15ActualRStar χ (lemma83PaperBeta D c)*
      section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
        lemma153GeometricWeight D c j‖≤(510*section15FactorConstant)*lemma23PaperL D^(-6:ℤ) := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 3≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith
  have hdata := section15_actual_shift_data hL hc hsmall
  have hn := section15_actual_denominators_nonzero χ hDN hA hc hsmall hbudget j
  have he := section15_exact_residue_product χ hD (lemma83PaperBeta D c) (lemma83_beta_re D c)
    (lemma61_P4_pos hD) j hdata.1 hdata.2 hn.2.2 hn.2.1 hn.1
  rw [section15_actual_geometric_eq] at he
  rw [he,show lemma153GeometricWeight D c j*section15Correction χ (lemma83PaperBeta D c) j-
    lemma153GeometricWeight D c j = lemma153GeometricWeight D c j*(section15Correction χ (lemma83PaperBeta D c) j-1) by ring,norm_mul]
  have hgn := section15_actual_geometric_norm hD hL hc hsmall j
  have herr := section15_actual_correction_error χ hDN hA hc hsmall hδ hbudget j
  calc
    _ ≤ 2*((255*section15FactorConstant)*lemma23PaperL D^(-6:ℤ)) :=
      mul_le_mul hgn herr (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Multiplication by the genuine a costs at most L^4, leaving O(L^-2). -/
lemma section15_actual_a_L6_budget {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2≤lemma23PaperL D) {C : ℝ} {e : ℂ}
    (he : ‖e‖≤C*lemma23PaperL D^(-6:ℤ)) :
    ‖(lemma171MainTerm χ:ℂ)*e‖≤
      (lemma32RegularProductBound (3/4)*(16*Real.exp 1)^2*C)*lemma23PaperL D^(-2:ℤ) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hd : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD hL (by simp; positivity)
  have hcorr : ‖lemma171AnalyticCorrection D 1‖≤lemma32RegularProductBound (3/4) :=
    lemma171_correction_sector_bound D (3/4) (by norm_num) 1 (by norm_num) (by simp)
  have hreg := lemma32_regular_product_bound_pos (3/4)
  rw [lemma171_main_term_complex χ hD,norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ (lemma32RegularProductBound (3/4)*(16*Real.exp 1*lemma23PaperL D^2)^2)*
      (C*lemma23PaperL D^(-6:ℤ)) := by gcongr
    _ = _ := by simp only [zpow_neg,zpow_ofNat]; field_simp

lemma section15_budget_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D →
      section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/1024 := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun D : ℕ => section15FactorConstant*lemma23PaperL D^(-6:ℤ)) atTop (𝓝 0) := by
    simpa using (tendsto_zpow_atTop_zero (by norm_num : (-6:ℤ)<0)).comp ht |>.const_mul section15FactorConstant
  exact eventually_atTop.mp (hz.eventually_le_const (by norm_num : (0:ℝ)<1/1024))

/-- Uniform original-shift analytic residue bridge. The constant is absolute,
chosen before c′; all dependence on the fixed c′ is in the modulus threshold. -/
theorem section15_actual_weighted_r_product_bridge {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖(lemma171MainTerm χ:ℂ)*(section15ActualRStar χ (lemma83PaperBeta D c)*
        section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
          lemma153GeometricWeight D c j)‖≤
        (lemma32RegularProductBound (3/4)*(16*Real.exp 1)^2*(510*section15FactorConstant))*
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
    (section15_actual_r_product_error χ hDN hA hc (hshift D hD1) (hδ D hD2).2 hb j)

end ZhangLS.Spec
