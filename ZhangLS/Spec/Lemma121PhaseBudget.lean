import ZhangLS.Spec.Lemma121ExactHigh

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex
open scoped Real

lemma lemma121_smoothing_beta_six_norm {D : ℕ} (ha : 0≤lemma44PaperAlpha D) :
    ‖lemma82SmoothingBeta D 6‖=(3/2:ℝ)*lemma44PaperAlpha D := by
  simp [lemma82SmoothingBeta,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
  ring

lemma lemma121_shift_difference_norm {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖lemma82SmoothingBeta D 6-lemma82PaperBeta D c j‖≤(3/2:ℝ)*lemma44PaperAlpha D := by
  have hb := lemma52_offset_bounds hL hc hsmall
  have hgen (t : ℝ) (ht0 : 0≤t) (ht1 : t≤3*lemma44PaperAlpha D) :
      ‖3*I*(lemma44PaperAlpha D:ℂ)/2-I*(t:ℂ)‖≤(3/2:ℝ)*lemma44PaperAlpha D := by
    have he : 3*I*(lemma44PaperAlpha D:ℂ)/2-I*(t:ℂ)=
        I*(((3/2:ℝ)*lemma44PaperAlpha D-t:ℝ):ℂ) := by push_cast; ring
    rw [he,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  unfold lemma82SmoothingBeta lemma82PaperBeta
  simp only [ite_true]
  split_ifs
  · exact hgen _ hb.1.1 hb.1.2
  · exact hgen _ hb.2.1.1 hb.2.1.2
  · exact hgen _ hb.2.2.1 hb.2.2.2

/-- A rigorous replacement phase budget. The value 101/125000 is 0.000808,
so 10^-3 leaves room for the vanishing analytic error. -/
lemma lemma121_actual_phase_budget {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {d : ℝ} (hdlo : lemma121PDoublePrimeOne D<d) (hdhi : d<lemma121P2 D) :
    ‖lemma121Phase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
        (Real.log (d/lemma121PDoublePrimeOne D))-
      lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
        (Real.log (d/lemma121PDoublePrimeOne D))‖≤(101:ℝ)/125000 := by
  let h := Real.log (d/lemma121PDoublePrimeOne D)
  have hg := lemma121_endpoint_geometry hD hL
  have hr := lemma121_high_range_geometry hD hL hdlo hdhi
  have hLp : 0<lemma23PaperL D := by linarith
  have hdp : 0<d := hg.1.trans hdlo
  have hnonneg : 0≤h := Real.log_nonneg ((one_le_div hg.1).mpr hdlo.le)
  have hdB : d≤lemma121PDoublePrimeTwo D := by
    have hh := (le_div_iff₀ hdp).mp hr.2.1
    simpa using hh
  have hlog : h≤(1/250:ℝ)*lemma23PaperL D^9 := by
    rw [← hg.2.2.2.2.2.1]
    exact Real.log_le_log (div_pos hdp hg.1) (div_le_div_of_nonneg_right hdB hg.1.le)
  have ha : 0<lemma44PaperAlpha D := by
    rw [lemma58_alpha_eq_log_power]
    positivity
  have halpha : lemma44PaperAlpha D*h≤Real.pi/250 := by
    apply (mul_le_mul_of_nonneg_left hlog ha.le).trans_eq
    rw [lemma58_alpha_eq_log_power]
    change Real.pi*lemma23PaperL D^(-9:ℤ)*((1/250:ℝ)*lemma23PaperL D^9)=Real.pi/250
    rw [zpow_neg,zpow_ofNat]
    field_simp
  have hb : ‖lemma82SmoothingBeta D 6*(h:ℂ)‖≤(1:ℝ)/50 := by
    rw [norm_mul,lemma121_smoothing_beta_six_norm ha.le,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
    nlinarith [Real.pi_lt_d2]
  have hdif : ‖(lemma82SmoothingBeta D 6-lemma82PaperBeta D c j)*(h:ℂ)‖≤(1:ℝ)/50 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
    have hh := mul_le_mul_of_nonneg_right
      (lemma121_shift_difference_norm (by linarith : 3≤lemma23PaperL D) hc hsmall j) hnonneg
    nlinarith [Real.pi_lt_d2]
  have he := lemma121_phase_linearization_bound (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j) h
    (hb.trans (by norm_num))
  apply he.trans
  calc
    _ ≤ ((1:ℝ)/50)^2*(1+1/50)+(1/50)*(1/50) := by gcongr
    _ = _ := by norm_num

end ZhangLS.Spec
