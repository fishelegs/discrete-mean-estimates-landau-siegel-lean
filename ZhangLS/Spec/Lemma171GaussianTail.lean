import ZhangLS.Spec.Lemma171Target
import ZhangLS.Spec.Lemma44SmoothedTail
import ZhangLS.Spec.Lemma56

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma lemma171_harmonic_coefficient_le_nat {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma171Coefficient χ n / (n : ℝ) ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply (div_le_iff₀ hn0).mpr
  have hnu : ‖lemma23NuArithmeticFunction χ n‖ ≤ (n : ℝ) :=
    (lemma23NuArithmeticFunction_norm_le_card_divisors χ n).trans
      (by exact_mod_cast Nat.card_divisors_le_self n)
  simpa only [lemma171Coefficient, pow_two] using pow_le_pow_left₀ (norm_nonneg _) hnu 2

lemma lemma171_gaussian_weight_le_one {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    zhangGaussianWeight D x ≤ 1 := by
  have h := zhangGaussianWeight_nonneg hD (inv_pos.mpr hx)
  rw [lemma44_gaussian_weight_inv] at h
  linarith

lemma lemma171_log_T_le {D : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    Real.log (lemma56PaperT D) ≤ lemma23PaperL D ^ 9 := by
  rw [lemma56PaperT,Real.log_exp]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL
    (by norm_num : (11 / 10 : ℝ) ≤ (9 : ℕ))

lemma lemma171_gaussian_tail_weight {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {n : ℕ}
    (hn : ⌊lemma23PaperP D ^ 2⌋₊ < n) :
    zhangGaussianWeight D (lemma56PaperT D / n) ≤
      Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹ := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnr : lemma23PaperP D ^ 2 < (n : ℝ) := (Nat.floor_lt (by positivity)).mp hn
  have hlogn : 2 * L ^ 9 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (pow_pos (Real.exp_pos _) 2 : 0 < lemma23PaperP D ^ 2) hnr.le
    simpa [Real.log_pow, lemma23PaperP, Real.log_exp, L] using h
  have hlogT : Real.log (lemma56PaperT D) ≤ (9 / 5 : ℝ) * L ^ 9 := by
    have ht := lemma171_log_T_le (D := D) hL1
    have hp : 0 ≤ L ^ 9 := by positivity
    linarith only [ht,hp]
  have hc : 60 ≤ L ^ 15 := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 4
    have h415 : L ^ 4 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by norm_num)
    norm_num at h4
    linarith only [h4,h415]
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have hy : L ^ 24 / 10 + 3 * Real.log (n : ℝ) ≤
      -zhangGaussianEndpoint D (lemma56PaperT D / n) := by
    rw [zhangGaussianEndpoint,Real.log_div hT.ne' hnp.ne']
    change L ^ 24 / 10 + 3 * Real.log (n : ℝ) ≤
      -(L ^ 15 * (Real.log (lemma56PaperT D) - Real.log (n : ℝ)))
    have hp := mul_nonneg (by linarith only [hc] : 0 ≤ L ^ 15 - 3)
      (sub_nonneg.mpr hlogn)
    have hq := mul_nonneg (by linarith only [hc] : 0 ≤ L ^ 15 / 10 - 6)
      (show 0 ≤ L ^ 9 by positivity)
    have hr := mul_le_mul_of_nonneg_left hlogT (show 0 ≤ L ^ 15 by positivity)
    have heq : L ^ 15 * L ^ 9 = L ^ 24 := by ring
    nlinarith only [hp,hq,hr,heq]
  have h24 := lemma44_L24_dominates_linear hL
  have hlognpos : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hn)
  calc
    _ ≤ Real.exp (zhangGaussianEndpoint D (lemma56PaperT D / n)) :=
      lemma44_gaussian_weight_le_exp_endpoint (by nlinarith only [hy,h24,hL,hlognpos])
    _ ≤ Real.exp (-(L ^ 24) / 10 - 3 * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith only [hy])
    _ = _ := by
      rw [Real.exp_sub]
      have h3 : Real.exp (3 * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
        simpa [Real.exp_log hnp] using Real.exp_nat_mul (Real.log (n : ℝ)) 3
      rw [h3]
      ring

lemma lemma171_gaussian_short_weight_error {D : ℕ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D)
    (hT : 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D))
    {n : ℕ} (hn : n ∈ Finset.Icc 1 (D ^ 4)) :
    |zhangGaussianWeight D (lemma56PaperT D / n) - 1| ≤
      Real.exp (-(lemma23PaperL D ^ 16)) := by
  let L := lemma23PaperL D
  let x := lemma56PaperT D / (n : ℝ)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hx : 0 < x := div_pos (Real.exp_pos _) hnp
  have hlogn : Real.log (n : ℝ) ≤ 4 * L := by
    calc
      _ ≤ Real.log ((D : ℝ) ^ 4) :=
        Real.log_le_log hnp (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
      _ = _ := by rw [Real.log_pow]; rfl
  have he : L ^ 16 ≤ zhangGaussianEndpoint D x := by
    rw [zhangGaussianEndpoint,show x = lemma56PaperT D / (n : ℝ) from rfl,
      Real.log_div (show lemma56PaperT D ≠ 0 from (Real.exp_pos _).ne') hnp.ne']
    change L ^ 16 ≤ L ^ 15 * (Real.log (lemma56PaperT D) - Real.log (n : ℝ))
    calc
      _ = L ^ 15 * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hT,hlogn]) (by positivity)
  have h16 : 1 ≤ L ^ 16 := one_le_pow₀ (by linarith)
  have hinv : -zhangGaussianEndpoint D x⁻¹ = zhangGaussianEndpoint D x := by
    simp [zhangGaussianEndpoint,Real.log_inv,mul_neg]
  have ht := lemma44_gaussian_weight_le_exp_endpoint (x := x⁻¹)
    (by rw [hinv]; exact h16.trans he)
  have hg := zhangGaussianWeight_nonneg hD (inv_pos.mpr hx)
  rw [lemma44_gaussian_weight_inv] at hg ht
  rw [abs_of_nonpos (by linarith : zhangGaussianWeight D (lemma56PaperT D / n) - 1 ≤ 0)]
  calc
    _ ≤ Real.exp (zhangGaussianEndpoint D x⁻¹) := by linarith only [ht]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hinv,he])

lemma lemma171_smoothing_scale_threshold :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      3 ≤ lemma23PaperL D ∧ 5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr : Tendsto (fun D : ℕ => lemma23PaperL D ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp ht
  have he : ∀ᶠ D : ℕ in atTop, 3 ≤ lemma23PaperL D ∧
      5 * lemma23PaperL D ≤ Real.log (lemma56PaperT D) := by
    filter_upwards [ht.eventually (eventually_ge_atTop 3),hr.eventually (eventually_ge_atTop 5)] with D hL hR
    refine ⟨hL,?_⟩
    have hL0 : 0 < lemma23PaperL D := by linarith
    rw [lemma56PaperT,Real.log_exp,show (11 / 10 : ℝ) = 1 / 10 + 1 by norm_num,
      Real.rpow_add hL0,Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hR hL0.le
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp he
  exact ⟨max 2 D₀,le_max_left _ _,fun D hD => hD₀ D ((le_max_right _ _).trans hD)⟩

end ZhangLS.Spec
