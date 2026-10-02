import ZhangLS.Spec.Lemma153GeometricWeightBudget
import ZhangLS.Spec.Lemma58
import ZhangLS.Spec.Lemma54
import ZhangLS.Spec.Lemma83

/-! Quantitative factors in the true residue product at source (15.16).
The original assumption (A), actual L-functions, Mellin transform, and
Gaussian factor are retained. No eventual contradiction to (A) is used. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma section15_zeta_regular_error {z : ℂ} (hz : ‖z-1‖ ≤ 1/4) :
    ‖zetaPoleRemoved z-1‖ ≤ 5*‖z-1‖ := by
  have hre := Complex.abs_re_le_norm (z-1)
  simp only [Complex.sub_re,Complex.one_re] at hre
  have hr : 3/4 ≤ z.re := by have hh := (abs_le.mp (hre.trans hz)).1; linarith
  have hp : 0<z.re := by linarith
  have hn : ‖z‖ ≤ 2 := by
    have ht := norm_add_le (z-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at ht
    linarith
  have hm : ‖mellin zetaFractionalPart (-z)‖ ≤ 2 := by
    apply (norm_mellin_zetaFractionalPart_le hp).trans
    apply (div_le_iff₀ hp).mpr
    linarith
  rw [zetaPoleRemoved_eq_regularizedAbel_of_pos_re hp]
  rw [show z-z*(z-1)*mellin zetaFractionalPart (-z)-1 =
    (z-1)-z*(z-1)*mellin zetaFractionalPart (-z) by ring]
  calc
    _ ≤ ‖z-1‖+‖z*(z-1)*mellin zetaFractionalPart (-z)‖ := norm_sub_le _ _
    _ = ‖z-1‖+‖z‖*‖z-1‖*‖mellin zetaFractionalPart (-z)‖ := by rw [norm_mul,norm_mul]
    _ ≤ ‖z-1‖+2*‖z-1‖*2 := by gcongr
    _ = _ := by ring

lemma section15_ne_zero_of_near_one {z : ℂ} {e : ℝ}
    (h : ‖z-1‖≤e) (he : e<1) : z≠0 := by
  intro hz
  simp [hz] at h
  linarith

lemma section15_inverse_error {z : ℂ} {e : ℝ}
    (h : ‖z-1‖≤e) (he : e≤1/2) : ‖z⁻¹-1‖≤2*e := by
  have hn : 1/2≤‖z‖ := by
    have ht := norm_add_le (z-1) (1:ℂ)
    have ht' := norm_sub_le (1:ℂ) z
    have hh : 1≤‖z-1‖+‖z‖ := by
      calc
        _ = ‖(z-1)-z‖ := by simp
        _ ≤ ‖z-1‖+‖z‖ := norm_sub_le _ _
    linarith
  have hz : z≠0 := norm_pos_iff.mp (by linarith)
  have he0 : 0≤e := (norm_nonneg _).trans h
  rw [show z⁻¹-1=-(z-1)/z by field_simp; ring,norm_div,norm_neg]
  apply (div_le_iff₀ (by linarith : 0<‖z‖)).mpr
  nlinarith

lemma section15_derivative_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ) :
    (1:ℝ)/16≤‖LDerivAtOne χ‖ := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hd := lemma57_one_sixteenth_at_explicit_threshold χ hDN hA
  have hs := lemma57Scale_ge_one hD
  have hd' : (1:ℝ)/16≤realLDerivAtOne χ := by nlinarith only [hd,hs]
  rw [LDerivAtOne_eq_realLDerivAtOne χ hD,Complex.norm_real,Real.norm_eq_abs]
  exact hd'.trans (le_abs_self _)

/-- The genuine relative Taylor factor. Its value is not set equal to one. -/
noncomputable def section15LFactor {D : ℕ} (χ : RealPrimitiveCharacter D) (z : ℂ) : ℂ :=
  dirichletLFunction χ (1+z)/(LDerivAtOne χ*z)

noncomputable def section15LRelativeConstant : ℝ := 32*lemma58ErrorConstant/Real.pi

lemma section15_l_relative_constant_pos : 0<section15LRelativeConstant := by
  unfold section15LRelativeConstant
  exact div_pos (mul_pos (by norm_num) lemma58_error_constant_pos) Real.pi_pos

lemma section15_actual_L_relative_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {z : ℂ} (hlo : lemma44PaperAlpha D/2≤‖z‖) (hhi : ‖z‖≤10*lemma44PaperAlpha D) :
    ‖section15LFactor χ z-1‖ ≤ section15LRelativeConstant*lemma23PaperL D^(-6:ℤ) := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2000≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have ha := (lemma44_alpha_pos_le_one (by linarith : 3≤lemma23PaperL D)).1
  have hd := section15_derivative_lower χ hDN hA
  have hdz : LDerivAtOne χ*z≠0 := by
    apply mul_ne_zero
    · exact norm_pos_iff.mp (by linarith)
    · exact norm_pos_iff.mp (by linarith)
  have hden : Real.pi/32*lemma23PaperL D^(-9:ℤ) ≤ ‖LDerivAtOne χ*z‖ := by
    rw [norm_mul]
    have hh := mul_le_mul hd hlo (by positivity : 0≤lemma44PaperAlpha D/2) (norm_nonneg _)
    convert hh using 1
    rw [lemma58_alpha_eq_log_power]
    dsimp [lemma23PaperL]; ring
  have ht := lemma58_actual_full_disk_linear_error χ hD hL hA
    (s := 1+z) (by simpa using hhi)
  have ht' : ‖dirichletLFunction χ (1+z)-LDerivAtOne χ*z‖ ≤
      lemma58ErrorConstant*lemma23PaperL D^(-15:ℤ) := by simpa using ht
  unfold section15LFactor
  rw [div_sub_one hdz,norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hdz)).mpr
  calc
    _ ≤ lemma58ErrorConstant*lemma23PaperL D^(-15:ℤ) := ht'
    _ = (section15LRelativeConstant*lemma23PaperL D^(-6:ℤ))*
      (Real.pi/32*lemma23PaperL D^(-9:ℤ)) := by
      unfold section15LRelativeConstant
      rw [show (32*lemma58ErrorConstant/Real.pi*lemma23PaperL D^(-6:ℤ))*
        (Real.pi/32*lemma23PaperL D^(-9:ℤ)) =
        lemma58ErrorConstant*(lemma23PaperL D^(-6:ℤ)*lemma23PaperL D^(-9:ℤ)) by field_simp]
      rw [←zpow_add₀ hLp.ne']
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity [section15_l_relative_constant_pos])

lemma section15_actual_beta_norm_lower {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    lemma44PaperAlpha D/2≤‖lemma83PaperBeta D c j‖ := by
  let δ := c*lemma44PaperAlpha D*lemma23PaperL D
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hs : δ≤1/10 := hsmall
  have hf := lemma153_actual_beta_factorization D c
  fin_cases j
  · change lemma44PaperAlpha D/2≤‖lemma52PaperBetaOne D c‖
    rw [hf.1]
    change _≤‖I*(lemma44PaperAlpha D:ℂ)*(1-5*(δ:ℂ))‖
    have he : (1:ℂ)-5*(δ:ℂ)=((1-5*δ:ℝ):ℂ) := by push_cast; rfl
    rw [he,norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ha,abs_of_nonneg (by linarith)]
    nlinarith
  · change lemma44PaperAlpha D/2≤‖lemma52PaperBetaTwo D c‖
    rw [hf.2.1]
    change _≤‖I*(lemma44PaperAlpha D:ℂ)*(2*(1+(δ:ℂ)))‖
    have he : (2:ℂ)*(1+(δ:ℂ))=((2*(1+δ):ℝ):ℂ) := by push_cast; rfl
    rw [he,norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ha,abs_of_nonneg (by linarith)]
    nlinarith
  · change lemma44PaperAlpha D/2≤‖lemma52PaperBetaThree D c‖
    rw [hf.2.2]
    change _≤‖I*(lemma44PaperAlpha D:ℂ)*(3*(1-(δ:ℂ)))‖
    have he : (3:ℂ)*(1-(δ:ℂ))=((3*(1-δ):ℝ):ℂ) := by push_cast; rfl
    rw [he,norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ha,abs_of_nonneg (by linarith)]
    nlinarith

lemma section15_actual_beta_L_relative_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) :
    ‖section15LFactor χ (lemma83PaperBeta D c j)-1‖≤section15LRelativeConstant*lemma23PaperL D^(-6:ℤ) ∧
    ‖section15LFactor χ (-lemma83PaperBeta D c j)-1‖≤section15LRelativeConstant*lemma23PaperL D^(-6:ℤ) := by
  have hL : 3≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith
  have hlo := section15_actual_beta_norm_lower hL hc hsmall j
  have hhi := lemma83_paper_beta_norm hL hc hsmall j
  have ha := (lemma44_alpha_pos_le_one hL).1
  constructor
  · exact section15_actual_L_relative_error χ hDN hA hlo (by linarith)
  · exact section15_actual_L_relative_error χ hDN hA (by simpa using hlo) (by simpa using (show ‖lemma83PaperBeta D c j‖≤10*lemma44PaperAlpha D by linarith))

end ZhangLS.Spec
