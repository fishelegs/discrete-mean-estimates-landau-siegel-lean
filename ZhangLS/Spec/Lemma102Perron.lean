import ZhangLS.Spec.Lemma102Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
set_option maxHeartbeats 2000000

/-- Genuine unshifted logarithmic Perron identity for the actual ξ series. -/
lemma lemma102_actual_xi_perron {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r)
    {b x : ℝ} (hb : 0<b) (hx : 0<x) :
    lemma102LogSum χ c j d r x = (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ,
      lemma83XiDirichletSeries χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ))) *
        ((x:ℂ)^((b:ℂ)+I*(t:ℂ))/((b:ℂ)+I*(t:ℂ))^2)) := by
  have hsum := (lemma84_actual_dirichlet_bridge χ c j d r hd hr (b:ℂ) (by simpa using hb)).1
  have hsum' : LSeriesSummable (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r)
      ((1+b:ℝ):ℂ) := by simpa using hsum
  have hi := lemma84_log_perron_series_identity
    (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r)
    hb (0:ℂ) (by simp) hx hsum'
  rw [lemma84_perron_tsum_eq_strict_sum _ _ hx] at hi
  simpa only [lemma102LogSum,add_zero,neg_zero,Complex.cpow_zero,mul_one] using hi.symm

lemma lemma102_actual_xi_perron_factored {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0<d) (hr : 0<r)
    {b x : ℝ} (hb : 0<b) (hx : 0<x) :
    lemma102LogSum χ c j d r x = (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ,
      lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
        (lemma83PaperBeta D c (j+2)) 0
        (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))) := by
  rw [lemma102_actual_xi_perron χ c j d r hd hr hb hx]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hseries := (lemma84_actual_dirichlet_bridge χ c j d r hd hr ((b:ℂ)+I*(t:ℂ))
    (by simpa using hb)).2
  rw [hseries]
  unfold lemma84AnalyticCircleIntegrand
  simp only [add_zero]
  ring

end ZhangLS.Spec
