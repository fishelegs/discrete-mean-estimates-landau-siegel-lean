import ZhangLS.Spec.Lemma84LogPerronTerms
import ZhangLS.Spec.Lemma84DirichletBridge
import ZhangLS.Spec.Lemma84CircleApproximation
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma84_mellin_term_tsum (a : ℕ → ℂ) (c : ℝ) (m : ℂ) (x t : ℝ) :
    (∑' n : ℕ, lemma84MellinTerm a c m x n t) =
      LSeries a (1+((c:ℂ)+I*(t:ℂ))) *
        ((x:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2) := by
  unfold lemma84MellinTerm
  rw [tsum_mul_right]
  rfl

/-- Exact logarithmic Perron formula for an actual absolutely convergent
Dirichlet series. Neither the formula nor its interchange is a hypothesis. -/
lemma lemma84_log_perron_series_identity (a : ℕ → ℂ) {c : ℝ} (hc : 0 < c)
    (m : ℂ) (hm : m.re = 0) {x : ℝ} (hx : 0 < x)
    (ha : LSeriesSummable a ((1+c:ℝ):ℂ)) :
    (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ, LSeries a (1+((c:ℂ)+I*(t:ℂ))) *
      ((x:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2)) =
        ∑' n : ℕ, lemma84PerronTerm a m x n := by
  have hi := integral_tsum_of_summable_integral_norm
    (fun n => lemma84_mellin_term_integrable a hc m hm hx n)
    (lemma84_mellin_integral_norm_summable a c m hm hx ha)
  simp_rw [← lemma84_mellin_term_tsum a c m x]
  rw [← hi,← tsum_mul_left]
  simp_rw [lemma84_mellin_term_integral a hc m hm hx]

lemma lemma84_perron_tsum_eq_strict_sum (a : ℕ → ℂ) (m : ℂ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, lemma84PerronTerm a m x n) =
      ∑ n ∈ lemma84StrictCutoff x,
        a n/(n:ℂ)*((x/(n:ℝ):ℝ):ℂ)^(-m)*(Real.log (x/(n:ℝ)):ℂ) := by
  have hs : (∑' n : ℕ, lemma84PerronTerm a m x n) =
      ∑ n ∈ lemma84StrictCutoff x, lemma84PerronTerm a m x n := by
    apply tsum_eq_sum
    intro n hn
    by_cases hn0 : n=0
    · simp [lemma84PerronTerm,hn0]
    · have hnx : ¬(n:ℝ)<x := by
        intro hh
        exact hn ((lemma84_mem_strictCutoff hx.le n).mpr ⟨Nat.pos_of_ne_zero hn0,hh⟩)
      simp [lemma84PerronTerm,hn0,hnx]
  rw [hs]
  apply Finset.sum_congr rfl
  intro n hn
  have hh := (lemma84_mem_strictCutoff hx.le n).mp hn
  simp [lemma84PerronTerm,hh.1.ne',hh.2]

/-- The original ξ sum is exactly its actual logarithmic Perron integral,
with the Section 7 coefficients and n<x cutoff unchanged. -/
lemma lemma84_actual_xi_perron {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    lemma84XiSum χ c j μ d r x = (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ,
      lemma83XiDirichletSeries χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ))) *
        ((x:ℂ)^((b:ℂ)+I*(t:ℂ))/((b:ℂ)+I*(t:ℂ)+lemma84SmoothingBeta D μ)^2)) := by
  have hsum := (lemma84_actual_dirichlet_bridge χ c j d r hd hr (b:ℂ) (by simpa using hb)).1
  have hsum' : LSeriesSummable (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r)
      ((1+b:ℝ):ℂ) := by simpa using hsum
  have hi := lemma84_log_perron_series_identity
    (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r)
    hb (lemma84SmoothingBeta D μ) (lemma84_smoothing_beta_re D μ) hx hsum'
  rw [lemma84_perron_tsum_eq_strict_sum _ _ hx] at hi
  exact hi.symm

/-- The actual convergent ξ series is replaced by its proved 8.3 factorization
on the initial line. This is the genuine source integral (8.9). -/
lemma lemma84_actual_xi_perron_factored {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    lemma84XiSum χ c j μ d r x = (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ,
      lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
        (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
        (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))) := by
  rw [lemma84_actual_xi_perron χ c j μ d r hd hr hb hx]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hseries := (lemma84_actual_dirichlet_bridge χ c j d r hd hr ((b:ℂ)+I*(t:ℂ))
    (by simpa using hb)).2
  rw [hseries]
  unfold lemma84AnalyticCircleIntegrand
  ring

end ZhangLS.Spec
