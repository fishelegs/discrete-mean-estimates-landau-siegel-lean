import ZhangLS.Spec.Lemma54MellinSecondMoment

/-! # The small-x second moment has one explicit polynomial budget on the full strip -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma54SecondDerivativeConstant : ℝ :=
  16 * Real.pi ^ 2 * Real.sqrt Real.pi * Real.exp 2

theorem lemma54_second_derivative_constant_pos : 0 < lemma54SecondDerivativeConstant := by
  unfold lemma54SecondDerivativeConstant
  positivity

theorem lemma54_scale_ge_200 {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    200 ≤ lemma53PaperScale D := by
  have hp : lemma23PaperL D ≤ lemma23PaperL D ^ 400 :=
    by simpa only [pow_one] using
      pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show (1 : ℕ) ≤ 400 by norm_num)
  unfold lemma53PaperScale
  linarith

theorem lemma54_small_endpoint_polynomial {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    1 ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) ∧
      lemma51PaperT0 D ^ (51 / 50 : ℝ) ≤ lemma23PaperL D ^ 530 := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have ht : 1 ≤ lemma51PaperT0 D := by
    unfold lemma51PaperT0
    exact one_le_pow₀ hL1
  refine ⟨Real.one_le_rpow ht (by norm_num), ?_⟩
  unfold lemma51PaperT0
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ lemma23PaperL D)]
  rw [← Real.rpow_natCast (lemma23PaperL D) 530]
  exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)

theorem lemma54_strip_weight_le_cubic_cap {x T σ : ℝ} (hx : 0 < x)
    (hxT : x ≤ T) (hT : 1 ≤ T) (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    x ^ (σ + 1) ≤ T ^ 3 := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx.le hx1 (by linarith)).trans (one_le_pow₀ hT)
  · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
    have hh := Real.rpow_le_rpow_of_exponent_le hx1' (show σ + 1 ≤ (3 : ℝ) by linarith)
    rw [Real.rpow_ofNat] at hh
    exact hh.trans (pow_le_pow_left₀ hx.le hxT 3)

theorem lemma54_actual_second_deriv_uniform_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x) :
    ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤ lemma54SecondDerivativeConstant := by
  apply (lemma54_actual_second_deriv_norm_bound hD (lemma54_scale_ge_one hL) hx).trans
  exact div_le_self lemma54_second_derivative_constant_pos.le (lemma54_scale_ge_one hL)

theorem lemma54_actual_small_second_moment_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    (∫ x : ℝ in Ioc 0 (lemma51PaperT0 D ^ (51 / 50 : ℝ)),
      x ^ (σ + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖) ≤
        lemma54SecondDerivativeConstant * lemma23PaperL D ^ 2120 := by
  let T := lemma51PaperT0 D ^ (51 / 50 : ℝ)
  have ht := lemma54_small_endpoint_polynomial hL
  have hi := (lemma54_actual_second_moment_integrable hD hL (by linarith : 0 < σ)).mono_set
    (show Ioc 0 T ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hc : IntegrableOn (fun _ : ℝ => T ^ 3 * lemma54SecondDerivativeConstant) (Ioc 0 T) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hm := integral_mono_ae hi hc (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hw := lemma54_strip_weight_le_cubic_cap hx.1 hx.2 ht.1 hσ hσ2
    exact mul_le_mul hw (lemma54_actual_second_deriv_uniform_bound hD hL hx.1)
      (norm_nonneg _) (pow_nonneg (by linarith : 0 ≤ T) 3))
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith : 0 ≤ T), sub_zero,
    smul_eq_mul] at hm
  have hpow : T ^ 4 ≤ lemma23PaperL D ^ 2120 := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ T) ht.2 4
    simpa only [← pow_mul, show 530 * 4 = 2120 by norm_num] using hh
  have hh := mul_le_mul_of_nonneg_left hpow lemma54_second_derivative_constant_pos.le
  dsimp only [T] at hm hh
  nlinarith only [hm, hh]

end ZhangLS.Spec
