import ZhangLS.Spec.Proposition71PrincipalScaleBudget
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma proposition71_principal_height_inverse (D : ℕ) :
    (proposition71ZetaAuxHeight D)⁻¹=Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  rw [proposition71ZetaAuxHeight,←Real.exp_neg]
  rfl

lemma proposition71_principal_height_inverse_square {D : ℕ} (hL : 0≤lemma23PaperL D) :
    (proposition71ZetaAuxHeight D^2)⁻¹≤Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  have hH : 0<proposition71ZetaAuxHeight D := proposition71_zeta_aux_height_pos D
  have hH1 : 1≤proposition71ZetaAuxHeight D := Real.one_le_exp (Real.rpow_nonneg hL _)
  have hpow : proposition71ZetaAuxHeight D≤proposition71ZetaAuxHeight D^2 := by nlinarith
  have hh := one_div_le_one_div_of_le hH hpow
  simpa only [one_div,proposition71_principal_height_inverse] using hh

lemma proposition71_principal_left_budget {D : ℕ} (hL : 0<lemma23PaperL D)
    {q A : ℝ} (hq : 0<q) (hA : 0≤A) (hqlo : lemma56PaperT D^2≤q) (k : ℕ) :
    A*q^(1-1/lemma23PaperL D)*lemma23PaperL D^k*proposition71ZetaAuxHeight D≤
      A*q*lemma23PaperL D^k*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  have hh := mul_le_mul_of_nonneg_left (proposition71_principal_scale_left hL hq hqlo)
    (show 0≤A*lemma23PaperL D^k by positivity)
  convert hh using 1 <;> ring

lemma proposition71_principal_horizontal_budget {D : ℕ} (hL : 0<lemma23PaperL D)
    {q A : ℝ} (hq : 0<q) (hA : 0≤A) (hqhi : q≤lemma23PaperP D^10) (k : ℕ) :
    A*q^(1+lemma44PaperAlpha D)*lemma23PaperL D^k/(proposition71ZetaAuxHeight D)^2≤
      Real.exp (10*Real.pi)*A*q*lemma23PaperL D^k*
        Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  rw [div_eq_mul_inv]
  have hqpow := proposition71_principal_scale_right hL hq hqhi
  have hH := proposition71_principal_height_inverse_square hL.le
  calc
    _≤A*(q*Real.exp (10*Real.pi))*lemma23PaperL D^k*
      Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by gcongr
    _=_ := by ring

lemma proposition71_principal_tail_budget {D : ℕ} (hL : 1≤lemma23PaperL D)
    {q A : ℝ} (hq : 0<q) (hA : 0≤A) (hqhi : q≤lemma23PaperP D^10) {k l : ℕ} (hkl : k≤l) :
    A*q^(1+lemma44PaperAlpha D)*lemma23PaperL D^k/proposition71ZetaAuxHeight D≤
      Real.exp (10*Real.pi)*A*q*lemma23PaperL D^l*
        Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  rw [div_eq_mul_inv,proposition71_principal_height_inverse]
  have hqpow := proposition71_principal_scale_right (by linarith) hq hqhi
  have hpow := pow_le_pow_right₀ hL hkl
  calc
    _≤A*(q*Real.exp (10*Real.pi))*lemma23PaperL D^l*
      Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by gcongr
    _=_ := by ring

end ZhangLS.Spec
