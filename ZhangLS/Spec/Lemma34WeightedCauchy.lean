import ZhangLS.Spec.Lemma34ShortMean
set_option autoImplicit false
namespace ZhangLS.Spec
open MeasureTheory
set_option maxHeartbeats 2000000

lemma lemma34_weighted_integral_cauchy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f w : α → ℝ) (hw : Integrable w μ)
    (hfw : Integrable (fun x => f x*w x) μ)
    (hf2w : Integrable (fun x => f x^2*w x) μ)
    (hn : 0 ≤ᵐ[μ] w) (hW : 0 < ∫ x, w x ∂μ) :
    (∫ x, f x*w x ∂μ)^2 ≤ (∫ x, w x ∂μ) * (∫ x, f x^2*w x ∂μ) := by
  let a := (∫ x, f x*w x ∂μ) / (∫ x, w x ∂μ)
  have he : (fun x => (f x-a)^2*w x) =
      (fun x => (f x^2*w x - (2*a)*(f x*w x)) + a^2*w x) := by
    funext x
    ring
  have hi : Integrable (fun x => (f x-a)^2*w x) μ := by
    rw [he]
    exact (hf2w.sub (hfw.const_mul (2*a))).add (hw.const_mul (a^2))
  have hp : 0 ≤ ∫ x, (f x-a)^2*w x ∂μ :=
    integral_nonneg_of_ae (hn.mono (fun x hx => mul_nonneg (sq_nonneg _) hx))
  have hv : (∫ x, (f x-a)^2*w x ∂μ) =
      (∫ x, f x^2*w x ∂μ) - 2*a*(∫ x, f x*w x ∂μ) + a^2*(∫ x, w x ∂μ) := by
    have hAdd := integral_add (hf2w.sub (hfw.const_mul (2*a))) (hw.const_mul (a^2))
    have hSub := integral_sub hf2w (hfw.const_mul (2*a))
    simp only [Pi.sub_apply,integral_const_mul] at hAdd hSub
    rw [he]
    calc
      _ = (∫ x, f x^2*w x - (2*a)*(f x*w x) ∂μ) + a^2*(∫ x, w x ∂μ) := hAdd
      _ = _ := by rw [hSub]
  have ha : (∫ x, f x^2*w x ∂μ) - 2*a*(∫ x, f x*w x ∂μ) + a^2*(∫ x, w x ∂μ) =
      (∫ x, f x^2*w x ∂μ) - (∫ x, f x*w x ∂μ)^2/(∫ x, w x ∂μ) := by
    dsimp [a]
    field_simp [ne_of_gt hW]
    ring
  rw [hv,ha] at hp
  have hd : (∫ x, f x*w x ∂μ)^2/(∫ x, w x ∂μ) ≤ (∫ x, f x^2*w x ∂μ) := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hW).mp hd

end ZhangLS.Spec
