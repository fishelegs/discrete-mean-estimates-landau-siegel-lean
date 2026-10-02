import ZhangLS.Spec.Lemma56PerronRightTruncation

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_horizontal_point_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H M σ t : ℝ} (hB : 0 < B) (hx : 1 ≤ x)
    (hH : 0 < H) (hM : 0 ≤ M) (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (ht : H ≤ |t|)
    (τ : ℝ) (hLD : ‖logDeriv (DirichletCharacter.LFunction θ)
      ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤ M) :
    ‖lemma56PerronArithmeticIntegrand θ B x τ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
  have hxp : 0 < x := by linarith only [hx]
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hn : H ≤ ‖z‖ := ht.trans (by simpa [z] using Complex.abs_im_le_norm z)
  have hxpow : x ^ σ ≤ x ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hx hσ2
  have hsqσ : σ ^ 2 ≤ 4 := by nlinarith only [hσ0, hσ2]
  have hsqt : H ^ 2 ≤ t ^ 2 := by
    have h := pow_le_pow_left₀ hH.le ht 2
    simpa using h
  have hex : Real.exp ((σ ^ 2 - t ^ 2) / (4 * B ^ 2)) ≤
      Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) := by
    apply Real.exp_le_exp.mpr
    rw [show 1 / B ^ 2 - H ^ 2 / (4 * B ^ 2) = (4 - H ^ 2) / (4 * B ^ 2) by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [hsqσ, hsqt]
  change ‖-(logDeriv (DirichletCharacter.LFunction θ)
    ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)) * lemma56PerronKernel B σ x t‖ ≤ _
  rw [norm_mul, norm_neg, lemma56_perron_kernel_norm hxp]
  calc
    _ ≤ M * (x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H) := by
      apply mul_le_mul hLD _ (by positivity) hM
      apply div_le_div₀ (by positivity) _ hH hn
      exact mul_le_mul hxpow hex (Real.exp_nonneg _) (sq_nonneg x)
    _ = _ := by ring

lemma lemma56_perron_horizontal_integral_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x H M a t : ℝ} (hB : 0 < B) (hx : 1 ≤ x)
    (hH : 0 < H) (hM : 0 ≤ M) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (ht : H ≤ |t|)
    (τ : ℝ) (hLD : ∀ σ : ℝ, a ≤ σ → σ ≤ 2 →
      ‖logDeriv (DirichletCharacter.LFunction θ)
        ((σ : ℂ) + (t : ℂ) * I - (τ : ℂ) * I)‖ ≤ M) :
    ‖∫ σ : ℝ in a..2, lemma56PerronArithmeticIntegrand θ B x τ
      ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => lemma56PerronArithmeticIntegrand θ B x τ ((σ : ℂ) + (t : ℂ) * I))
    (a := a) (b := 2) (C := M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H)
    (fun σ hσ => by
      have hh : σ ∈ Set.Ioc a 2 := by simpa only [Set.uIoc_of_le ha2] using hσ
      exact lemma56_perron_horizontal_point_bound θ hB hx hH hM
        (ha0.trans hh.1.le) hh.2 ht τ (hLD σ hh.1.le hh.2))
  apply hbound.trans
  rw [abs_of_nonneg (by linarith only [ha2])]
  have hl : 2 - a ≤ 2 := by linarith only [ha0]
  convert mul_le_mul_of_nonneg_left hl
    (by positivity : 0 ≤ M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H) using 1 <;> ring

end ZhangLS.Spec
