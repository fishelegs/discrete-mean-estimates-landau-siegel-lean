import ZhangLS.Spec.Lemma54LargeTailDamping

/-! # Integrating both original actual large-x tails on the full disk -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma54LargeExteriorConstant : ℝ :=
  (2 + Real.exp 1) * (200 * Real.sqrt Real.pi * Real.exp 1) +
    (Real.sqrt Real.pi * Real.exp 2) * 10082 * 256

theorem lemma54_large_exterior_constant_pos : 0 < lemma54LargeExteriorConstant := by
  unfold lemma54LargeExteriorConstant
  positivity

theorem lemma54_actual_large_exterior_mellin_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖∫ x : ℝ in Ioi (lemma51PaperT0 D ^ (51 / 50 : ℝ)),
      (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      lemma54LargeExteriorConstant * lemma23PaperL D ^ 3200 *
        Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let B := lemma53PaperScale D
  let T := lemma51PaperT0 D ^ (51 / 50 : ℝ)
  let E := Real.exp (-(lemma23PaperL D ^ 10) / 2)
  let A := 2 + Real.exp 1
  let C := Real.sqrt Real.pi * Real.exp 2
  let F : ℝ → ℝ := fun x => (A * E) * ((1 + x ^ 3) * Real.exp (-(((B / 2) * Real.log x / 100) ^ 2)))
  let G : ℝ → ℝ := fun x => (C * E) * ((1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / (2 * B)))
  have hB2000 : 2000 ≤ B := hL.trans (lemma54_scale_ge_log hL)
  have hB0 : 0 < B := by linarith
  have hBhalf : 200 ≤ B / 2 := by linarith
  have hT1 : 1 ≤ T := (lemma54_small_endpoint_polynomial hL).1
  have hsub : Ioi T ⊆ Ioi (0 : ℝ) := fun x hx => by
    change T < x at hx
    change 0 < x
    linarith
  have hFi0 : IntegrableOn F (Ioi 0) :=
    (lemma54_log_cubic_tail_integrable (by positivity : 0 < B / 2)).const_mul (A * E)
  have hGi0 : IntegrableOn G (Ioi 0) :=
    (lemma54_half_power_cubic_tail_integrable (by positivity : 0 < 2 * B)).const_mul (C * E)
  have hnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ F x + G x := by
    intro x hx
    have hx0 : 0 < x := hx
    dsimp [F, G, A, C, E]
    positivity
  have hnorm : ‖∫ x : ℝ in Ioi T, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      ∫ x : ℝ in Ioi 0, F x + G x := by
    calc
      _ ≤ ∫ x : ℝ in Ioi T, F x + G x := by
        apply norm_integral_le_of_norm_le ((hFi0.add hGi0).mono_set hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxT : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x := hx
        have hx1 := (lemma53_large_range_parameters hL hxT).1.le
        have hw := lemma54_disk_weight_le_x hL hs hx1
        have hx3 : x ≤ x ^ 3 := by
          simpa only [pow_one] using pow_le_pow_right₀ hx1 (show (1 : ℕ) ≤ 3 by norm_num)
        have hwQ : ‖(x : ℂ) ^ (s - 1)‖ ≤ 1 + x ^ 3 := by linarith
        have hd := lemma53_large_range_estimate hD hL (by linarith : 0 < x) hxT
        have hlog := lemma54_large_log_tail_split hL hxT
        have hhalf := lemma54_large_half_power_tail_split hL hxT
        have hQ : 0 ≤ 1 + x ^ 3 := by positivity
        rw [norm_mul]
        calc
          _ ≤ (1 + x ^ 3) * ((2 + Real.exp 1) *
              Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) +
                (Real.sqrt Real.pi * Real.exp 2) * Real.exp (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D)) :=
            mul_le_mul hwQ hd (norm_nonneg _) hQ
          _ ≤ (1 + x ^ 3) * ((2 + Real.exp 1) *
              (E * Real.exp (-(((B / 2) * Real.log x / 100) ^ 2))) +
                (Real.sqrt Real.pi * Real.exp 2) * (E * Real.exp (-(x ^ (1 / 2 : ℝ)) / (2 * B)))) := by
            apply mul_le_mul_of_nonneg_left _ hQ
            exact add_le_add (mul_le_mul_of_nonneg_left hlog (by positivity))
              (mul_le_mul_of_nonneg_left hhalf (by positivity))
          _ = _ := by dsimp [F, G, A, C]; ring
      _ ≤ _ := by
        apply setIntegral_mono_set (hFi0.add hGi0)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hnonneg x hx
        · exact Eventually.of_forall hsub
  have hlog := lemma54_log_cubic_tail_integral_bound hBhalf
  have hhalf := lemma54_half_power_cubic_tail_integral_bound (by linarith : 1 ≤ 2 * B)
  have hpow : (2 * B) ^ 8 = 256 * lemma23PaperL D ^ 3200 := by
    dsimp [B, lemma53PaperScale]
    ring
  have hLpow : 1 ≤ lemma23PaperL D ^ 3200 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hA : 0 ≤ A * E := by dsimp [A, E]; positivity
  have hC : 0 ≤ C * E := by dsimp [C, E]; positivity
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, F x + G x := hnorm
    _ = (A * E) * (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-(((B / 2) * Real.log x / 100) ^ 2))) +
        (C * E) * (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / (2 * B))) := by
      rw [integral_add hFi0 hGi0]
      dsimp [F, G]
      rw [integral_const_mul, integral_const_mul]
    _ ≤ (A * E) * (200 * Real.sqrt Real.pi * Real.exp 1) + (C * E) * (10082 * (2 * B) ^ 8) :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hA) (mul_le_mul_of_nonneg_left hhalf hC)
    _ ≤ _ := by
      rw [hpow]
      have hh := mul_le_mul_of_nonneg_right hLpow
        (show 0 ≤ (A * E) * (200 * Real.sqrt Real.pi * Real.exp 1) by positivity)
      dsimp [lemma54LargeExteriorConstant, A, C, E] at *
      nlinarith only [hh]

end ZhangLS.Spec
