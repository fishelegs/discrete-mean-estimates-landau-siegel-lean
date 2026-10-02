import ZhangLS.Spec.Lemma54NearZeroMellin

/-! # The small-range exterior integral of the actual Delta -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma54_disk_weight_le_x {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {s : ℂ} (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) {x : ℝ} (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ (s - 1)‖ ≤ x := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x), sub_re, one_re]
  have hh := Real.rpow_le_rpow_of_exponent_le hx
    (show s.re - 1 ≤ (1 : ℝ) by have h := (lemma54_disk_closed_strip hL hs).2; linarith)
  simpa only [Real.rpow_one] using hh

theorem lemma54_actual_small_exterior_mellin_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) {S : Set ℝ}
    (hS : MeasurableSet S)
    (hST : S ⊆ Ioc 1 (lemma51PaperT0 D ^ (51 / 50 : ℝ)))
    (hSW : S ⊆ (lemma54PaperWindow D)ᶜ) :
    ‖∫ x : ℝ in S, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      (288 + lemma53SmallErrorConstant) * lemma23PaperL D ^ 1838 *
        Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let T := lemma51PaperT0 D ^ (51 / 50 : ℝ)
  let E := Real.exp (-(lemma23PaperL D ^ 10) / 2)
  have ht := lemma54_small_endpoint_polynomial hL
  have hT1 : 1 ≤ T := ht.1
  have hT0 : 0 ≤ T := by linarith
  have hCs : 0 ≤ lemma53SmallErrorConstant := by unfold lemma53SmallErrorConstant; positivity
  have hC : 0 ≤ lemma53SmallErrorConstant * T * E := by dsimp [E]; positivity
  have hgi : IntegrableOn (fun x : ℝ => 2 * ((1 + x ^ 2) * lemma54PaperGaussian D x)) S :=
    ((lemma54_gaussian_quadratic_integrable (lemma53_scale_pos hD) _).const_mul 2).integrableOn
  have hciT : IntegrableOn (fun _ : ℝ => lemma53SmallErrorConstant * T * E) (Ioc 1 T) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hci := hciT.mono_set hST
  have hi : IntegrableOn (fun x : ℝ => 2 * ((1 + x ^ 2) * lemma54PaperGaussian D x) +
      lemma53SmallErrorConstant * T * E) S := hgi.add hci
  have hconst : (∫ x : ℝ in S, lemma53SmallErrorConstant * T * E) ≤
      lemma53SmallErrorConstant * T ^ 2 * E := by
    have hh : (∫ x : ℝ in S, lemma53SmallErrorConstant * T * E) ≤
        (∫ x : ℝ in Ioc 1 T, lemma53SmallErrorConstant * T * E) :=
      setIntegral_mono_set hciT (Eventually.of_forall fun _ => hC) (Eventually.of_forall hST)
    have heval : (∫ x : ℝ in Ioc 1 T, lemma53SmallErrorConstant * T * E) =
        (T - 1) * (lemma53SmallErrorConstant * T * E) := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hT1, smul_eq_mul]
    rw [heval] at hh
    have hp : 0 ≤ lemma53SmallErrorConstant * T * E := hC
    nlinarith only [hh, hp]
  have hg := lemma54_actual_gaussian_exterior_quadratic_mass hL hS
    (fun x hx => lemma54_window_compl_gap D (hSW hx))
  have hnorm : ‖∫ x : ℝ in S, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      288 * lemma23PaperL D ^ 1838 * E + lemma53SmallErrorConstant * T ^ 2 * E := by
    calc
      _ ≤ ∫ x : ℝ in S, 2 * ((1 + x ^ 2) * lemma54PaperGaussian D x) +
          lemma53SmallErrorConstant * T * E := by
        apply norm_integral_le_of_norm_le hi
        filter_upwards [ae_restrict_mem hS] with x hx
        have hxT := hST hx
        have hx1 : 1 ≤ x := hxT.1.le
        have hw := lemma54_disk_weight_le_x hL hs hx1
        have hwQ : ‖(x : ℂ) ^ (s - 1)‖ ≤ 1 + x ^ 2 := hw.trans (by nlinarith [sq_nonneg (x - 1)])
        have hwt : ‖(x : ℂ) ^ (s - 1)‖ ≤ T := hw.trans hxT.2
        have hd := lemma54_actual_delta_small_gaussian_bound hD hL (by linarith : 0 < x) hxT.2
        have hg0 : 0 ≤ lemma54PaperGaussian D x := (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
        rw [norm_mul]
        calc
          _ ≤ ‖(x : ℂ) ^ (s - 1)‖ * (2 * lemma54PaperGaussian D x + lemma53SmallErrorConstant * E) :=
            mul_le_mul_of_nonneg_left hd (norm_nonneg _)
          _ = ‖(x : ℂ) ^ (s - 1)‖ * (2 * lemma54PaperGaussian D x) +
              ‖(x : ℂ) ^ (s - 1)‖ * (lemma53SmallErrorConstant * E) := mul_add _ _ _
          _ ≤ (1 + x ^ 2) * (2 * lemma54PaperGaussian D x) + T * (lemma53SmallErrorConstant * E) :=
            add_le_add (mul_le_mul_of_nonneg_right hwQ (by positivity))
              (mul_le_mul_of_nonneg_right hwt (by dsimp [E]; positivity))
          _ = _ := by ring
      _ = 2 * (∫ x : ℝ in S, (1 + x ^ 2) * lemma54PaperGaussian D x) +
          (∫ x : ℝ in S, lemma53SmallErrorConstant * T * E) := by
        rw [integral_add hgi hci, integral_const_mul]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 2)
        dsimp [E] at *
        nlinarith only [hh, hconst]
  have hp : T ^ 2 ≤ lemma23PaperL D ^ 1838 := by
    calc
      _ ≤ (lemma23PaperL D ^ 530) ^ 2 := pow_le_pow_left₀ hT0 ht.2 2
      _ = lemma23PaperL D ^ 1060 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCs)
    (Real.exp_pos (-(lemma23PaperL D ^ 10) / 2)).le
  dsimp [E] at *
  nlinarith only [hnorm, hh]

end ZhangLS.Spec
