import ZhangLS.Spec.Lemma82OriginalBridge
import ZhangLS.Spec.Lemma58

namespace ZhangLS.Spec
open Complex Finset
open scoped Real
set_option maxHeartbeats 1000000

noncomputable def lemma82LocalErrorConstant : ℝ :=
  lemma58ErrorConstant + 128 * Real.exp 1 * (10 * Real.pi)

lemma lemma82_local_error_constant_pos : 0 < lemma82LocalErrorConstant := by
  unfold lemma82LocalErrorConstant
  positivity [lemma58_error_constant_pos]

lemma lemma82_beta_norm {D : ℕ} {c : ℝ} (hL : 3 ≤ lemma23PaperL D)
    (hc : 0 < c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) (j : Fin 3) :
    ‖lemma82PaperBeta D c j‖ ≤ 3*lemma44PaperAlpha D := by
  have hb := lemma52_offset_bounds hL hc hsmall
  unfold lemma82PaperBeta
  split_ifs
  · simpa only [lemma52PaperBetaOne,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hb.1.1] using hb.1.2
  · simpa only [lemma52PaperBetaTwo,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hb.2.1.1] using hb.2.1.2
  · simpa only [lemma52PaperBetaThree,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hb.2.2.1] using hb.2.2.2

lemma lemma82_smoothing_beta_norm (D μ : ℕ) (ha : 0 ≤ lemma44PaperAlpha D) :
    ‖lemma82SmoothingBeta D μ‖ ≤ 3*lemma44PaperAlpha D := by
  unfold lemma82SmoothingBeta
  split_ifs <;> simp only [norm_div, norm_mul, norm_ofNat, norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] <;> linarith

lemma lemma82_shift_in_disk {D : ℕ} {c : ℝ} (hL : 2000 ≤ lemma23PaperL D)
    (hc : 0 < c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (μ : ℕ) :
    ‖(1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j)-1‖ ≤ 10*lemma44PaperAlpha D ∧
    ‖1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j‖ ≤ 2 := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have ha : 0 < lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity
  have hs : ‖(1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j)-1‖ ≤
      10*lemma44PaperAlpha D := by
    rw [show (1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j)-1 =
      lemma82SmoothingBeta D μ-lemma82PaperBeta D c j by ring]
    apply (norm_sub_le _ _).trans
    linarith [lemma82_smoothing_beta_norm D μ ha.le,
      lemma82_beta_norm (by linarith : 3 ≤ lemma23PaperL D) hc hsmall j]
  refine ⟨hs,?_⟩
  have hr : 10*lemma44PaperAlpha D ≤ 1/(4*lemma23PaperL D) := lemma58_original_radius_in_taylor_disk hL
  have hbound : 1/(4*lemma23PaperL D) ≤ (1:ℝ) := by
    apply (div_le_one (by positivity : 0 < 4*lemma23PaperL D)).mpr
    linarith
  have hh := norm_add_le ((1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j)-1) (1:ℂ)
  rw [sub_add_cancel, norm_one] at hh
  linarith

/-- Actual Taylor control for the exact two-term residue expression. -/
lemma lemma82_local_analytic_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {x : ℝ} (hx : 1 ≤ x) (hxp : x < lemma23PaperP D) {s : ℂ}
    (hs : ‖s-1‖ ≤ 10*lemma44PaperAlpha D) :
    ‖(Real.log x : ℂ) * dirichletLFunction χ s + deriv (dirichletLFunction χ) s -
      LDerivAtOne χ * (1 + (s-1)*(Real.log x : ℂ))‖ ≤
      lemma82LocalErrorConstant * lemma23PaperL D^(-6:ℤ) := by
  let L := lemma23PaperL D
  have hLp : 0 < L := by dsimp [L]; linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlx' : Real.log x ≤ L^9 := by
    have hh := Real.log_lt_log (lt_of_lt_of_le zero_lt_one hx) hxp
    simpa [lemma23PaperP,L] using hh.le
  have hv := lemma58_actual_full_disk_linear_error χ hD hL hA hs
  have hd := lemma55_actual_first_derivative_variation χ hD (by change 2 ≤ lemma23PaperL D; linarith)
    (hs.trans (lemma58_original_radius_in_taylor_disk hL))
  have hsp : ‖s-1‖ ≤ (10*Real.pi)*L^(-9:ℤ) := by
    simpa [lemma58_alpha_eq_log_power,L,lemma23PaperL,mul_assoc] using hs
  have hpow1 : L^9 * L^(-15:ℤ) = L^(-6:ℤ) := by
    rw [← zpow_natCast L 9, ← zpow_add₀ hLp.ne']
    norm_num
  have hpow2 : L^3 * L^(-9:ℤ) = L^(-6:ℤ) := by
    rw [← zpow_natCast L 3, ← zpow_add₀ hLp.ne']
    norm_num
  have hd' : ‖deriv (dirichletLFunction χ) s - LDerivAtOne χ‖ ≤
      (128*Real.exp 1*(10*Real.pi))*L^(-6:ℤ) := by
    apply hd.trans
    calc
      (128*Real.exp 1*L^3)*‖s-1‖ ≤ (128*Real.exp 1*L^3)*((10*Real.pi)*L^(-9:ℤ)) :=
        mul_le_mul_of_nonneg_left hsp (by positivity)
      _ = _ := by rw [show (128*Real.exp 1*L^3)*((10*Real.pi)*L^(-9:ℤ)) =
        (128*Real.exp 1*(10*Real.pi))*(L^3*L^(-9:ℤ)) by ring, hpow2]
  have hv' : Real.log x * ‖dirichletLFunction χ s-LDerivAtOne χ*(s-1)‖ ≤
      lemma58ErrorConstant*L^(-6:ℤ) := by
    calc
      _ ≤ L^9*(lemma58ErrorConstant*L^(-15:ℤ)) :=
        mul_le_mul hlx' hv (norm_nonneg _) (by positivity [lemma58_error_constant_pos])
      _ = _ := by rw [show L^9*(lemma58ErrorConstant*L^(-15:ℤ)) =
        lemma58ErrorConstant*(L^9*L^(-15:ℤ)) by ring,hpow1]
  rw [show (Real.log x : ℂ)*dirichletLFunction χ s + deriv (dirichletLFunction χ) s -
    LDerivAtOne χ*(1+(s-1)*(Real.log x : ℂ)) =
    (Real.log x : ℂ)*(dirichletLFunction χ s-LDerivAtOne χ*(s-1)) +
      (deriv (dirichletLFunction χ) s-LDerivAtOne χ) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlx]
  apply (add_le_add hv' hd').trans_eq
  unfold lemma82LocalErrorConstant
  ring

end ZhangLS.Spec
