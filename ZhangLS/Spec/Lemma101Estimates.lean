import ZhangLS.Spec.Lemma101Ranges

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma101_second_difference_norm (a b c : ℂ) :
    ‖a-2*b+c‖≤‖a‖+2*‖b‖+‖c‖ := by
  calc
    _ ≤ ‖a-2*b‖+‖c‖ := norm_add_le _ _
    _ ≤ (‖a‖+‖2*b‖)+‖c‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by rw [norm_mul,norm_ofNat]

lemma lemma101_two_errors {a b : ℂ} {E : ℝ} (ha : ‖a‖≤E) (hb : ‖b‖≤E) :
    ‖a-2*b‖≤E+2*E := by
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_ofNat]
  exact add_le_add ha (mul_le_mul_of_nonneg_left hb (by norm_num))

lemma lemma101_log_second_difference {D : ℕ} {y : ℝ} (hy : 0<y) :
    Real.log (lemma101Cutoff D y (63/125)) -
      2*Real.log (lemma101Cutoff D y (251/500)) +
      Real.log (lemma101Cutoff D y (1/2)) = 0 := by
  rw [lemma101_log_cutoff hy,lemma101_log_cutoff hy,lemma101_log_cutoff hy]
  ring

lemma lemma101_log_lower_combination {D : ℕ} {y : ℝ} (hy : 0<y) :
    Real.log (lemma101Cutoff D y (63/125)) -
      2*Real.log (lemma101Cutoff D y (251/500)) =
      Real.log (y/lemma23PaperP D^(1/2:ℝ)) := by
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  rw [lemma101_log_cutoff hy,lemma101_log_cutoff hy,
    Real.log_div hy.ne' (Real.rpow_pos_of_pos hP _).ne', Real.log_rpow hP]
  ring

lemma lemma101_uniform_sum_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {y : ℝ} (hy : 1≤y) :
    ‖lemma101Sum χ c j y‖≤(2000*lemma101WeightedBoundConstant)*lemma23PaperL D^(-7:ℤ) := by
  have hyp : 0<y := zero_lt_one.trans_le hy
  have hLp : 0<lemma23PaperL D := by linarith
  have hb (a : ℝ) (ha : a<1) :
      ‖lemma82WeightedPolynomial χ (lemma101Cutoff D y a) (1-lemma82PaperBeta D c j)‖≤
      lemma101WeightedBoundConstant*lemma23PaperL D^2 :=
    lemma101_weighted_uniform_bound χ hD hL hA hc hsmall j
      (lemma101_cutoff_pos D hyp a) (lemma101_cutoff_lt_P hD hy ha)
  rw [lemma101_sum_exact_bridge χ hD c j hyp,norm_mul,lemma101_prefactor_norm hLp]
  apply (mul_le_mul_of_nonneg_left
    ((lemma101_second_difference_norm _ _ _).trans
      (add_le_add (add_le_add (hb _ (by norm_num))
        (mul_le_mul_of_nonneg_left (hb _ (by norm_num)) (by norm_num)))
        (hb _ (by norm_num)))) (by positivity : 0≤500/lemma23PaperL D^9)).trans_eq
  rw [zpow_neg,zpow_ofNat]
  field_simp
  ring

noncomputable def lemma101InteriorConstant : ℝ := 1500*(32+lemma82LocalErrorConstant)

lemma lemma101_interior_constant_pos : 0<lemma101InteriorConstant := by
  unfold lemma101InteriorConstant
  positivity [lemma82_local_error_constant_pos]

lemma lemma101_weighted_interior_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : (D:ℝ)/lemma56PaperT D≤2*lemma23PaperL D^(-6:ℤ))
    (j : Fin 3) {x : ℝ} (hx : lemma56PaperT D≤x) (hxp : x<lemma23PaperP D) :
    ‖lemma82WeightedPolynomial χ x (1-lemma82PaperBeta D c j)-
      LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log x:ℂ))‖≤
      (32+lemma82LocalErrorConstant)*lemma23PaperL D^(-6:ℤ) := by
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  have hx1 : 1≤x := (lemma101_T_gt_one hD).le.trans hx
  apply (lemma101_weighted_linear_error χ hD hL hA hc hsmall j hx1 hxp).trans
  have hdx : (D:ℝ)/x≤(D:ℝ)/lemma56PaperT D :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg D) hTp hx
  have hh := mul_le_mul_of_nonneg_left (hdx.trans htail) (by norm_num : (0:ℝ)≤16)
  rw [mul_div_assoc]
  nlinarith

lemma lemma101_lower_main_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) {y : ℝ} (hy : 0<y) :
    (500/(Real.log (lemma23PaperP D):ℂ)) *
      (LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log (lemma101Cutoff D y (63/125)):ℂ)) -
      2*(LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log (lemma101Cutoff D y (251/500)):ℂ)))) =
      lemma101MainLower χ c j y := by
  have he := lemma101_log_lower_combination (D := D) hy
  have heC : (Real.log (lemma101Cutoff D y (63/125)):ℂ)-
      2*(Real.log (lemma101Cutoff D y (251/500)):ℂ) =
      (Real.log (y/lemma23PaperP D^(1/2:ℝ)):ℂ) := by exact_mod_cast he
  unfold lemma101MainLower
  rw [← heC]
  ring

lemma lemma101_lower_estimate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : (D:ℝ)/lemma56PaperT D≤2*lemma23PaperL D^(-6:ℤ))
    (j : Fin 3) {y : ℝ} (hylo : lemma23PaperP D^(1/2:ℝ)<y)
    (hyhi : y≤lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D) :
    ‖lemma101Sum χ c j y-lemma101MainLower χ c j y‖≤
      lemma101InteriorConstant*lemma23PaperL D^(-15:ℤ) := by
  have hy1 : 1≤y := (lemma101_half_power_gt_one hD).le.trans hylo.le
  have hyp : 0<y := zero_lt_one.trans_le hy1
  have hLp : 0<lemma23PaperL D := by linarith
  have hxmid := lemma101_cutoff_ge_T hyp hyhi
  have hxhi : lemma56PaperT D≤lemma101Cutoff D y (63/125) :=
    hxmid.trans (lemma101_cutoff_mono hD hyp (by norm_num : (251/500:ℝ)≤63/125))
  have hzero := lemma101_weighted_zero_of_le_one χ (lemma101_cutoff_pos D hyp (1/2))
    (lemma101_cutoff_le_one hyp hylo.le) (1-lemma82PaperBeta D c j)
  have h₁ := lemma101_weighted_interior_error χ hD hL hA hc hsmall htail j hxhi
    (lemma101_cutoff_lt_P hD hy1 (by norm_num : (63/125:ℝ)<1))
  have h₂ := lemma101_weighted_interior_error χ hD hL hA hc hsmall htail j hxmid
    (lemma101_cutoff_lt_P hD hy1 (by norm_num : (251/500:ℝ)<1))
  rw [lemma101_sum_exact_bridge χ hD c j hyp,hzero,add_zero,
    ← lemma101_lower_main_identity χ hD c j hyp,← mul_sub,norm_mul,
    lemma101_prefactor_norm hLp]
  have halg (a b A B : ℂ) : (a-2*b)-(A-2*B)=(a-A)-2*(b-B) := by ring
  rw [halg]
  have hh := lemma101_two_errors h₁ h₂
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤500/lemma23PaperL D^9)).trans_eq
  unfold lemma101InteriorConstant
  rw [zpow_neg,zpow_neg,zpow_ofNat,zpow_ofNat]
  field_simp
  ring

lemma lemma101_upper_estimate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : (D:ℝ)/lemma56PaperT D≤2*lemma23PaperL D^(-6:ℤ))
    (j : Fin 3) {y : ℝ} (hylo : lemma23PaperP D^(251/500:ℝ)<y)
    (hyhi : y≤lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D) :
    ‖lemma101Sum χ c j y-lemma101MainUpper χ c j y‖≤
      lemma101InteriorConstant*lemma23PaperL D^(-15:ℤ) := by
  have hyhalf := (lemma101_half_power_le_power hD (by norm_num : (1/2:ℝ)≤251/500)).trans hylo.le
  have hy1 : 1≤y := (lemma101_half_power_gt_one hD).le.trans hyhalf
  have hyp : 0<y := zero_lt_one.trans_le hy1
  have hLp : 0<lemma23PaperL D := by linarith
  have hzero₁ := lemma101_weighted_zero_of_le_one χ (lemma101_cutoff_pos D hyp (1/2))
    (lemma101_cutoff_le_one hyp hyhalf) (1-lemma82PaperBeta D c j)
  have hzero₂ := lemma101_weighted_zero_of_le_one χ (lemma101_cutoff_pos D hyp (251/500))
    (lemma101_cutoff_le_one hyp hylo.le) (1-lemma82PaperBeta D c j)
  have hh := lemma101_weighted_interior_error χ hD hL hA hc hsmall htail j
    (lemma101_cutoff_ge_T hyp hyhi)
    (lemma101_cutoff_lt_P hD hy1 (by norm_num : (63/125:ℝ)<1))
  have he : lemma101MainUpper χ c j y = (500/(Real.log (lemma23PaperP D):ℂ))*
      (LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log (lemma101Cutoff D y (63/125)):ℂ))) := by
    unfold lemma101MainUpper lemma101Cutoff
    ring
  rw [lemma101_sum_exact_bridge χ hD c j hyp,hzero₁,hzero₂,mul_zero,sub_zero,add_zero,
    he,← mul_sub,norm_mul,lemma101_prefactor_norm hLp]
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤500/lemma23PaperL D^9)).trans
  have heq : (500/lemma23PaperL D^9)*((32+lemma82LocalErrorConstant)*lemma23PaperL D^(-6:ℤ)) =
      (500*(32+lemma82LocalErrorConstant))*lemma23PaperL D^(-15:ℤ) := by
    rw [zpow_neg,zpow_neg,zpow_ofNat,zpow_ofNat]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold lemma101InteriorConstant
  nlinarith [lemma82_local_error_constant_pos]

end ZhangLS.Spec
