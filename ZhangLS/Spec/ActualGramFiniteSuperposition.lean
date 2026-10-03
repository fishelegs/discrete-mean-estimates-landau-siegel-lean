import ZhangLS.Spec.ActualGramRamp
import Mathlib.Tactic.FunProp

/-! Exact finite profile superposition on one fixed compact interval.
The clipping at each moving endpoint is explicit and no infinite-series
Fubini statement is used. This is the calculus side of the actual K1/K2
attachment; the separate arithmetic kernel bridge must still be supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset
open scoped Classical Interval

noncomputable def actualGramClippedRamp (ell : ℂ) (t v : ℝ) : ℂ :=
  ((max (v-t) 0 : ℝ) : ℂ)*Complex.exp (ell*(v-t : ℝ))

lemma actualGram_clipped_ramp_of_le (ell : ℂ) {t v : ℝ} (h : t≤v) :
    actualGramClippedRamp ell t v=(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)) := by
  simp [actualGramClippedRamp,max_eq_left (sub_nonneg.mpr h)]

lemma actualGram_clipped_ramp_of_ge (ell : ℂ) {t v : ℝ} (h : v≤t) :
    actualGramClippedRamp ell t v=0 := by
  simp [actualGramClippedRamp,max_eq_right (sub_nonpos.mpr h)]

lemma actualGram_clipped_ramp_continuous (ell : ℂ) (t : ℝ) :
    Continuous (actualGramClippedRamp ell t) := by
  unfold actualGramClippedRamp
  fun_prop

lemma actualGram_ramp_density_continuous (ell : ℂ) (f f' f'' : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') : Continuous (actualGramRampDensity ell f f' f'') := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hc' : Continuous f' := continuous_iff_continuousAt.mpr (fun x => (hf' x).continuousAt)
  unfold actualGramRampDensity
  fun_prop

/-- Exact ramp on a fixed interval for every moving t, including the whole
lower cancellation tail and the range beyond the terminal endpoint. -/
theorem actualGram_fixed_interval_ramp (ell : ℂ) (f f' f'' : ℝ → ℂ) {a b : ℝ}
    (hab : a≤b) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    (hzleft : ∀ v≤a, actualGramRampDensity ell f f' f'' v=0)
    (hzright : ∀ v, b≤v → f v=0) (hfpb : f' b=0) (t : ℝ) :
    (∫ v in a..b, actualGramRampDensity ell f f' f'' v*actualGramClippedRamp ell t v) = f t := by
  let h := actualGramRampDensity ell f f' f''
  have hcont : Continuous h := actualGram_ramp_density_continuous ell f f' f'' hf hf' hf''
  have hraw : Continuous (fun v : ℝ => h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ))) := by fun_prop
  have hclip : Continuous (fun v : ℝ => h v*actualGramClippedRamp ell t v) :=
    hcont.mul (actualGram_clipped_ramp_continuous ell t)
  have hmain := actualGram_ramp_identity ell f f' f'' t b (fun v _ => hf v)
    (fun v _ => hf' v) (hraw.intervalIntegrable t b) (hzright b le_rfl) hfpb
  change (∫ v in a..b, h v*actualGramClippedRamp ell t v)=f t
  by_cases htb : b≤t
  · rw [hzright t htb]
    calc
      _ = ∫ _v in a..b, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hvb : v≤b := (by simpa only [Set.uIcc_of_le hab] using hv : v ∈ Set.Icc a b).2
        simp [actualGram_clipped_ramp_of_ge ell (hvb.trans htb)]
      _ = 0 := by simp
  have htb' : t≤b := (lt_of_not_ge htb).le
  by_cases hta : t≤a
  · have hlow : (∫ v in t..a, h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)))=0 := by
      calc
        _ = ∫ _v in t..a, (0 : ℂ) := by
          apply intervalIntegral.integral_congr
          intro v hv
          dsimp only
          have hva : v≤a := (by simpa only [Set.uIcc_of_le hta] using hv : v ∈ Set.Icc t a).2
          simp [h,hzleft v hva]
        _ = 0 := by simp
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (a := t) (b := a) (c := b) (hraw.intervalIntegrable t a) (hraw.intervalIntegrable a b)
    rw [hlow,zero_add] at hadd
    calc
      _ = ∫ v in a..b, h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hav : a≤v := (by simpa only [Set.uIcc_of_le hab] using hv : v ∈ Set.Icc a b).1
        rw [actualGram_clipped_ramp_of_le ell (hta.trans hav)]
        ring
      _ = ∫ v in t..b, h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)) := hadd
      _ = f t := hmain
  have hat : a≤t := (lt_of_not_ge hta).le
  have hlow : (∫ v in a..t, h v*actualGramClippedRamp ell t v)=0 := by
    calc
      _ = ∫ _v in a..t, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hvt : v≤t := (by simpa only [Set.uIcc_of_le hat] using hv : v ∈ Set.Icc a t).2
        simp [actualGram_clipped_ramp_of_ge ell hvt]
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := a) (b := t) (c := b) (hclip.intervalIntegrable a t) (hclip.intervalIntegrable t b)
  rw [hlow,zero_add] at hadd
  rw [← hadd]
  calc
    _ = ∫ v in t..b, h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      have htv : t≤v := (by simpa only [Set.uIcc_of_le htb'] using hv : v ∈ Set.Icc t b).1
      rw [actualGram_clipped_ramp_of_le ell htv]
      ring
    _ = f t := hmain

/-- One exact finite-sum interchange. Coefficients, endpoints, and the index
set can be the literal arithmetic data for a fixed D,d,r. -/
theorem actualGram_finite_ramp_superposition {ι : Type*} (S : Finset ι)
    (coeff : ι → ℂ) (endpoint : ι → ℝ) (ell : ℂ) (f f' f'' : ℝ → ℂ)
    {a b : ℝ} (hab : a≤b) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')
    (hzleft : ∀ v≤a, actualGramRampDensity ell f f' f'' v=0)
    (hzright : ∀ v, b≤v → f v=0) (hfpb : f' b=0) :
    (∑ n ∈ S, coeff n*f (endpoint n)) =
      ∫ v in a..b, actualGramRampDensity ell f f' f'' v*
        ∑ n ∈ S, coeff n*actualGramClippedRamp ell (endpoint n) v := by
  let h := actualGramRampDensity ell f f' f''
  have hcont : Continuous h := actualGram_ramp_density_continuous ell f f' f'' hf hf' hf''
  have hi (n : ι) : IntervalIntegrable (fun v : ℝ => coeff n*(h v*actualGramClippedRamp ell (endpoint n) v))
      volume a b :=
    (continuous_const.mul (hcont.mul (actualGram_clipped_ramp_continuous ell (endpoint n)))).intervalIntegrable a b
  calc
    _ = ∑ n ∈ S, coeff n*(∫ v in a..b, h v*actualGramClippedRamp ell (endpoint n) v) := by
      apply sum_congr rfl
      intro n hn
      rw [actualGram_fixed_interval_ramp ell f f' f'' hab hf hf' hf'' hzleft hzright hfpb]
    _ = ∑ n ∈ S, ∫ v in a..b, coeff n*(h v*actualGramClippedRamp ell (endpoint n) v) := by
      apply sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ v in a..b, ∑ n ∈ S, coeff n*(h v*actualGramClippedRamp ell (endpoint n) v) :=
      (intervalIntegral.integral_finsetSum (fun n _ => hi n)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      change (∑ n ∈ S, coeff n*(h v*actualGramClippedRamp ell (endpoint n) v)) =
        h v*(∑ n ∈ S, coeff n*actualGramClippedRamp ell (endpoint n) v)
      rw [mul_sum]
      apply sum_congr rfl
      intros; ring

end ZhangLS.Spec
