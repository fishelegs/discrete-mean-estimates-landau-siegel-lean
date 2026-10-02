import ZhangLS.Spec.Lemma84ContourErrorBudget
set_option autoImplicit false
namespace ZhangLS.Spec
open Real
set_option maxHeartbeats 1500000

noncomputable def lemma84UScalarConstant (K : ℕ) : ℝ :=
  lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*21^K

lemma lemma84_u_scalar_constant_pos (K : ℕ) : 0 < lemma84UScalarConstant K := by
  unfold lemma84UScalarConstant
  positivity [lemma84_u_growth_constant_pos]

lemma lemma84_u_scale_polynomial {D : ℕ} (hL : 1 ≤ lemma23PaperL D) (K : ℕ) :
    lemma84UContourScale D K ≤ lemma84UScalarConstant K*lemma23PaperL D^K := by
  have hh := mul_le_mul_of_nonneg_left (lemma84_polylog_to_polynomial _ hL K)
    (show 0 ≤ lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2) by positivity [lemma84_u_growth_constant_pos])
  simpa only [lemma84UContourScale,lemma84UScalarConstant,mul_assoc] using hh

lemma lemma84_six_alpha_right_scale {D : ℕ} (hL : 100 ≤ lemma23PaperL D) :
    (1+(6*lemma44PaperAlpha D)⁻¹)^3 ≤ 8*lemma23PaperL D^27 := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hα := (lemma83_alpha_small hL).1
  have hαid : lemma44PaperAlpha D = Real.pi/lemma23PaperL D^9 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
  have hb : (6*lemma44PaperAlpha D)⁻¹ ≤ lemma23PaperL D^9 := by
    calc
      _ ≤ (lemma44PaperAlpha D)⁻¹ := inv_anti₀ hα (by linarith only [hα])
      _ = lemma23PaperL D^9/Real.pi := by rw [hαid,inv_div]
      _ ≤ lemma23PaperL D^9 := div_le_self (pow_nonneg hLp.le _) (by linarith [Real.two_le_pi])
  have hbase : 1+(6*lemma44PaperAlpha D)⁻¹ ≤ 2*lemma23PaperL D^9 := by
    have hh := one_le_pow₀ hL1 (n := 9)
    linarith only [hb,hh]
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(6*lemma44PaperAlpha D)⁻¹) hbase 3
  exact hh.trans_eq (by ring)

lemma lemma84_modulus_inverse_exponential {D : ℕ} (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) :
    (D:ℝ)⁻¹ ≤ Real.exp (-(lemma23PaperL D^(1/10:ℝ))) ∧
      ((D:ℝ)^2)⁻¹ ≤ Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
  have hDpos : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD.le
  have hp : lemma23PaperL D^(1/10:ℝ) ≤ lemma23PaperL D := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/10:ℝ) ≤ 1)
  have he : (D:ℝ)⁻¹ = Real.exp (-lemma23PaperL D) := by
    rw [Real.exp_neg,lemma23PaperL,Real.exp_log hDpos]
  have hi : (D:ℝ)⁻¹ ≤ Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
    rw [he]
    exact Real.exp_le_exp.mpr (neg_le_neg hp)
  refine ⟨hi,?_⟩
  apply le_trans _ hi
  exact inv_anti₀ hDpos (by nlinarith only [hD1])

lemma lemma84_total_boundary_scalar_budget (L d C U B E V W : ℝ) (K : ℕ)
    (hL : 1 ≤ L) (hd : 0 < d) (hC : 0 ≤ C) (hU : 0 ≤ U) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hUp : U ≤ B*L^K) (hd1 : d⁻¹ ≤ E) (hd2 : (d^2)⁻¹ ≤ E)
    (hV : 0 ≤ V) (hV2 : V ≤ 2) (hW : 0 ≤ W) (hW8 : W ≤ 8*L^27) :
    (C*L^28*U)*Real.pi*L*E + 8*(C*L^28*U)*Real.exp (6*Real.pi)*V/d^2 +
      8*W*U*Real.exp (6*Real.pi)/d ≤
        ((C*Real.pi+16*C*Real.exp (6*Real.pi)+64*Real.exp (6*Real.pi))*B)*L^(K+29)*E := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hleft : (C*L^28*U)*Real.pi*L*E ≤ C*Real.pi*B*L^(K+29)*E := by
    have hh := mul_le_mul_of_nonneg_right hUp (show 0 ≤ C*L^28*Real.pi*L*E by positivity)
    rw [pow_add]
    nlinarith only [hh]
  have hp28 : L^(K+28) ≤ L^(K+29) := pow_le_pow_right₀ hL (by omega)
  have hp27 : L^(K+27) ≤ L^(K+29) := pow_le_pow_right₀ hL (by omega)
  have hhor : 8*(C*L^28*U)*Real.exp (6*Real.pi)*V/d^2 ≤
      16*C*Real.exp (6*Real.pi)*B*L^(K+29)*E := by
    calc
      _ ≤ 8*(C*L^28*(B*L^K))*Real.exp (6*Real.pi)*2*(d^2)⁻¹ := by
        rw [div_eq_mul_inv]
        gcongr
      _ ≤ 8*(C*L^28*(B*L^K))*Real.exp (6*Real.pi)*2*E := by gcongr
      _ = 16*C*Real.exp (6*Real.pi)*B*L^(K+28)*E := by rw [pow_add]; ring
      _ ≤ _ := by gcongr
  have hright : 8*W*U*Real.exp (6*Real.pi)/d ≤
      64*Real.exp (6*Real.pi)*B*L^(K+29)*E := by
    calc
      _ ≤ 8*(8*L^27)*(B*L^K)*Real.exp (6*Real.pi)*d⁻¹ := by
        rw [div_eq_mul_inv]
        gcongr
      _ ≤ 8*(8*L^27)*(B*L^K)*Real.exp (6*Real.pi)*E := by gcongr
      _ = 64*Real.exp (6*Real.pi)*B*L^(K+27)*E := by rw [pow_add]; ring
      _ ≤ _ := by gcongr
  nlinarith only [hleft,hhor,hright]

end ZhangLS.Spec
