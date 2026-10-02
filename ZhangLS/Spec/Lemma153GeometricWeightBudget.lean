import ZhangLS.Spec.Lemma153ActualShiftRatio
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

/-- Exactly the β-ratio and P₄ phase present in the printed leading residue
formula4382 after multiplying by β₁β₂L′(1). This is not defined as the
full analytic r₁* r₁ⱼ product. -/
noncomputable def lemma153GeometricWeight (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  lemma153ShiftRatio D c j *
    (lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma83PaperBeta D c j)

noncomputable def lemma153GeometricErrorConstant (c : ℝ) : ℝ :=
  12*c+2*lemma153PhaseErrorConstant c

lemma lemma153_geometric_error_constant_pos {c : ℝ} (hc : 0<c) :
    0<lemma153GeometricErrorConstant c := by
  unfold lemma153GeometricErrorConstant lemma153PhaseErrorConstant
  positivity

lemma lemma153_phase_sign_norm (j : Fin 3) : ‖lemma153PhaseSign j‖=1 := by
  unfold lemma153PhaseSign
  split_ifs <;> simp

lemma lemma153_weight_sign_identity (j : Fin 3) :
    lemma153LeadingSignedWeight j*lemma153PhaseSign j=lemma153LeadingWeight j := by
  unfold lemma153LeadingSignedWeight lemma153PhaseSign lemma153LeadingWeight
  split_ifs <;> norm_num

lemma lemma153_actual_geometric_weight_bound {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖lemma153GeometricWeight D c j-lemma153LeadingWeight j‖≤
      lemma153GeometricErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D) := by
  have hr := lemma153_actual_shift_ratio_bounds hL hc hsmall j
  have hp := lemma153_actual_P4_phase_bound hL hc hsmall j
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hLt : lemma23PaperL D≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤lemma23PaperL D)
      (by norm_num : (1:ℝ)≤11/10)
  have ht : 0≤Real.log (lemma56PaperT D) := by linarith only [hLt,hL]
  have hC : 0≤lemma153PhaseErrorConstant c := by unfold lemma153PhaseErrorConstant; positivity
  unfold lemma153GeometricWeight
  rw [←lemma153_weight_sign_identity j]
  rw [show lemma153ShiftRatio D c j*(lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma83PaperBeta D c j)-
      lemma153LeadingSignedWeight j*lemma153PhaseSign j =
      lemma153ShiftRatio D c j*((lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma83PaperBeta D c j)-lemma153PhaseSign j)+
      (lemma153ShiftRatio D c j-lemma153LeadingSignedWeight j)*lemma153PhaseSign j by ring]
  calc
    _ ≤ ‖lemma153ShiftRatio D c j*((lemma61PaperP4 D:ℂ)^(lemma52PaperBetaThree D c-lemma83PaperBeta D c j)-lemma153PhaseSign j)‖+
      ‖(lemma153ShiftRatio D c j-lemma153LeadingSignedWeight j)*lemma153PhaseSign j‖ := norm_add_le _ _
    _ ≤ 2*(lemma153PhaseErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D))+
      12*c*lemma44PaperAlpha D*lemma23PaperL D := by
      rw [norm_mul,norm_mul,lemma153_phase_sign_norm,mul_one]
      apply add_le_add _ hr.2
      exact mul_le_mul hr.1 hp (norm_nonneg _) (by norm_num)
    _ ≤ 2*(lemma153PhaseErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D))+
      12*c*lemma44PaperAlpha D*Real.log (lemma56PaperT D) := by gcongr
    _ = _ := by unfold lemma153GeometricErrorConstant; ring

/-- Multiplication by the actual a does not destroy the true β/P₄ phase
error. A separate analytic-residue-to-geometric-weight bridge is still needed. -/
theorem lemma153_actual_a_geometric_weight_budget {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) {c : ℝ} (hc : 0<c) (hL : 3≤lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖(lemma171MainTerm χ:ℂ)*(lemma153GeometricWeight D c j-lemma153LeadingWeight j)‖≤
      (lemma32RegularProductBound (3/4)*(16*Real.exp 1)^2*
        (lemma153GeometricErrorConstant c*Real.pi))*lemma23PaperL D^(-3:ℤ) := by
  have he := lemma153_actual_geometric_weight_bound hL hc hsmall j
  have he' : ‖lemma153GeometricWeight D c j-lemma153LeadingWeight j‖≤
      (lemma153GeometricErrorConstant c*Real.pi)*
        (Real.log (lemma56PaperT D)/Real.log (lemma23PaperP D)) := by
    calc
      _ ≤ lemma153GeometricErrorConstant c*lemma44PaperAlpha D*Real.log (lemma56PaperT D) := he
      _ = _ := by unfold lemma44PaperAlpha; ring
  have hb := paper_actual_LDeriv_boundary_budget χ hD (by linarith)
    (show 0≤lemma153GeometricErrorConstant c*Real.pi by
      exact mul_nonneg (lemma153_geometric_error_constant_pos hc).le Real.pi_pos.le) he'
  have hcorr : ‖lemma171AnalyticCorrection D 1‖≤lemma32RegularProductBound (3/4) :=
    lemma171_correction_sector_bound D (3/4) (by norm_num) 1 (by norm_num) (by simp)
  rw [lemma171_main_term_complex χ hD,mul_assoc,norm_mul]
  calc
    _ ≤ lemma32RegularProductBound (3/4)*
      (((16*Real.exp 1)^2*(lemma153GeometricErrorConstant c*Real.pi))*lemma23PaperL D^(-3:ℤ)) :=
      mul_le_mul hcorr hb (norm_nonneg _) (lemma32_regular_product_bound_pos _).le
    _ = _ := by ring

end ZhangLS.Spec
