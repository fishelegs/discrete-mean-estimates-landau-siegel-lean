import ZhangLS.Spec.ActualGramOriginalScaling
import ZhangLS.Spec.ActualGramSmoothingBounds

/-! A moving boundary integral estimate that pays its exact width. The
pointwise envelopes are supplied by ActualGramSmoothingBounds for the genuine
K1/K2 kernels; this module never promotes their boundary bounds to interior
precision. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical Interval

/-- The boundary interval has length at most delta, even when it crosses the
fixed profile endpoint b. Equality at the transition is paid on the boundary
side; the interior estimate is used only strictly beyond it. -/
theorem actualGram_moving_layer_integral_bound (e : ℝ → ℂ) {t b δ E₀ E₁ : ℝ}
    (htb : t≤b) (hδ : 0≤δ) (hE₀ : 0≤E₀) (hE₁ : 0≤E₁)
    (hi : IntervalIntegrable e volume t b)
    (hboundary : ∀ v ∈ Icc t b, v≤t+δ → ‖e v‖≤E₀)
    (hinterior : ∀ v ∈ Icc t b, t+δ<v → ‖e v‖≤E₁) :
    ‖∫ v in t..b, e v‖ ≤ E₀*δ+E₁*(b-t) := by
  let s : ℝ := min (t+δ) b
  have hts : t≤s := le_min (by linarith) htb
  have hsb : s≤b := min_le_right _ _
  have hsδ : s≤t+δ := min_le_left _ _
  have hil : IntervalIntegrable e volume t s := hi.mono_set (by
    simp only [Set.uIcc_of_le htb,Set.uIcc_of_le hts]
    exact Set.Icc_subset_Icc le_rfl hsb)
  have hir : IntervalIntegrable e volume s b := hi.mono_set (by
    simp only [Set.uIcc_of_le htb,Set.uIcc_of_le hsb]
    exact Set.Icc_subset_Icc hts le_rfl)
  have hl : ‖∫ v in t..s, e v‖≤E₀*(s-t) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s) (C := E₀) (f := e) (by
      intro v hv
      have hv' : v ∈ Ioc t s := by simpa only [Set.uIoc_of_le hts] using hv
      exact hboundary v ⟨hv'.1.le,hv'.2.trans hsb⟩ (hv'.2.trans hsδ))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using h
  have hr : ‖∫ v in s..b, e v‖≤E₁*(b-s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := b) (C := E₁) (f := e) (by
      intro v hv
      have hv' : v ∈ Ioc s b := by simpa only [Set.uIoc_of_le hsb] using hv
      have htrans : t+δ<v := by
        by_cases h : t+δ≤b
        · simpa only [s,min_eq_left h] using hv'.1
        · have hs : s=b := min_eq_right (lt_of_not_ge h).le
          rw [hs] at hv'
          exact (not_lt_of_ge hv'.2 hv'.1).elim
      exact hinterior v ⟨hts.trans hv'.1.le,hv'.2⟩ htrans)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hsb)] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hir]
  apply (norm_add_le _ _).trans
  apply (add_le_add hl hr).trans
  exact add_le_add (mul_le_mul_of_nonneg_left (by linarith : s-t≤δ) hE₀)
    (mul_le_mul_of_nonneg_left (by linarith : b-s≤b-t) hE₁)

/-- The explicit B^-1 inherited from the original logarithmic kernel remains
outside the whole error, including the moving boundary contribution. -/
theorem actualGram_scaled_moving_layer_bound (e : ℝ → ℂ) {t b δ E₀ E₁ B : ℝ}
    (htb : t≤b) (hδ : 0≤δ) (hE₀ : 0≤E₀) (hE₁ : 0≤E₁) (hB : 0<B)
    (hi : IntervalIntegrable e volume t b)
    (hboundary : ∀ v ∈ Icc t b, v≤t+δ → ‖e v‖≤E₀)
    (hinterior : ∀ v ∈ Icc t b, t+δ<v → ‖e v‖≤E₁) :
    ‖(B : ℂ)⁻¹*(∫ v in t..b, e v)‖ ≤ (E₀*δ+E₁*(b-t))/B := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
  have h := mul_le_mul_of_nonneg_left
    (actualGram_moving_layer_integral_bound e htb hδ hE₀ hE₁ hi hboundary hinterior)
    (inv_nonneg.mpr hB.le)
  exact h.trans_eq (by ring)

/-- Continuity of the actual finite real-x smoothed sum follows from the
clipped-ramp identity, including each integer cutoff crossing. -/
lemma actualGram_log_smoothed_continuousOn (D : ℕ) (coeff : ℕ → ℂ) (gamma : ℂ)
    {B q a b : ℝ} (hB : 0<B) (hq : 0<q)
    (hcut : ∀ v ∈ Icc a b, Real.exp (B*v)/q≤lemma81Cutoff D) :
    ContinuousOn (fun v => actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q)) (Icc a b) := by
  have hc : Continuous (fun v : ℝ => (B : ℂ)*
      ∑ m ∈ lemma81PolynomialIndices D, coeff m*
        actualGramClippedRamp ((B : ℂ)*gamma) (Real.log (q*(m : ℝ))/B) v) := by
    unfold actualGramClippedRamp
    fun_prop
  apply hc.continuousOn.congr
  intro v hv
  have he := congrArg (fun z : ℂ => (B : ℂ)*z)
    (actualGram_clipped_sum_eq_smoothed D coeff gamma hB hq v (hcut v hv))
  have hBC : (B : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  simpa only [← mul_assoc,mul_inv_cancel₀ hBC,one_mul] using he.symm

end ZhangLS.Spec
