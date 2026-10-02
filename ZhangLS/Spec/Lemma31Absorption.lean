import ZhangLS.Spec.Lemma31LinearTail
import ZhangLS.Spec.Lemma23GoodSet
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma lemma31_inverse_sqrt_eq_exp {D : ℕ} (hD : 0 < D) :
    (Real.sqrt (D : ℝ))⁻¹ = Real.exp (-(1/2 : ℝ)*lemma23PaperL D) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : Real.sqrt (D : ℝ) = Real.exp ((1/2 : ℝ)*lemma23PaperL D) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hd]
    congr 1
    simp only [lemma23PaperL]
    ring
  rw [hs,← Real.exp_neg]
  congr 1
  ring

lemma lemma31_exponential_absorption_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      1 < D ∧ 3 ≤ lemma23PaperL D ∧
        (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf : Tendsto (fun D : ℕ => lemma23PaperL D^2013 *
      Real.exp (-(1/2 : ℝ)*lemma23PaperL D)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat,Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2013 : ℝ) (1/2) (by norm_num)).comp ht
  have he : ∀ᶠ D : ℕ in atTop, 1 < D ∧ 3 ≤ lemma23PaperL D ∧
      (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ) := by
    filter_upwards [hf.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      ht.eventually (eventually_ge_atTop 3),eventually_ge_atTop (2 : ℕ)] with D hsmall hL hD
    refine ⟨by omega,hL,?_⟩
    have hl0 : 0 < lemma23PaperL D := by linarith
    rw [lemma31_inverse_sqrt_eq_exp (by omega)]
    simp only [zpow_neg,zpow_ofNat]
    rw [← one_mul ((lemma23PaperL D^2013)⁻¹)]
    apply (le_mul_inv_iff₀ (pow_pos hl0 2013)).mpr
    simpa only [mul_comm] using hsmall.le
  exact eventually_atTop.mp he

end ZhangLS.Spec
