import ZhangLS.Spec.ActualGramLogKernelBridge

/-! Exact superposition starting at log(q)/B. Every positive arithmetic index
has its individual endpoint to the right of that point. This avoids any
false assumption that the profile density vanishes below a moving endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Finset
open scoped Classical Interval

lemma actualGram_ramp_above_left_endpoint (ell : ℂ) (f f' f'' : ℝ → ℂ)
    {a b t : ℝ} (hab : a≤b) (hat : a≤t)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (hzright : ∀ v, b≤v → f v=0) (hfpb : f' b=0) :
    (∫ v in a..b, actualGramRampDensity ell f f' f'' v*actualGramClippedRamp ell t v)=f t := by
  let h := actualGramRampDensity ell f f' f''
  have hc : Continuous h := actualGram_ramp_density_continuous ell f f' f'' hf hf' hf''
  have hclip : Continuous (fun v => h v*actualGramClippedRamp ell t v) :=
    hc.mul (actualGram_clipped_ramp_continuous ell t)
  change (∫ v in a..b, h v*actualGramClippedRamp ell t v)=f t
  by_cases hbt : b≤t
  · rw [hzright t hbt]
    calc
      _ = ∫ _v in a..b, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hvb : v≤b := (by simpa only [Set.uIcc_of_le hab] using hv : v ∈ Set.Icc a b).2
        simp [actualGram_clipped_ramp_of_ge ell (hvb.trans hbt)]
      _ = 0 := by simp
  have htb : t≤b := (lt_of_not_ge hbt).le
  have hzero : (∫ v in a..t, h v*actualGramClippedRamp ell t v)=0 := by
    calc
      _ = ∫ _v in a..t, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hvt : v≤t := (by simpa only [Set.uIcc_of_le hat] using hv : v ∈ Set.Icc a t).2
        simp [actualGram_clipped_ramp_of_ge ell hvt]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := a) (b := t) (c := b) (hclip.intervalIntegrable a t) (hclip.intervalIntegrable t b)
  rw [hzero,zero_add] at hsplit
  rw [← hsplit]
  have hraw : Continuous (fun v : ℝ => h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ))) := by fun_prop
  calc
    _ = ∫ v in t..b, h v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      have htv : t≤v := (by simpa only [Set.uIcc_of_le htb] using hv : v ∈ Set.Icc t b).1
      rw [actualGram_clipped_ramp_of_le ell htv]
      ring
    _ = f t := actualGram_ramp_identity ell f f' f'' t b (fun v _ => hf v)
      (fun v _ => hf' v) (hraw.intervalIntegrable t b) (hzright b le_rfl) hfpb

/-- Exact actual finite superposition beginning at the product endpoint.
No left-density vanishing condition at that moving point is assumed. -/
theorem actualGram_log_superposition_from_product (D : ℕ) (coeff : ℕ → ℂ) (gamma : ℂ)
    (f f' f'' : ℝ → ℂ) {b B q : ℝ} (hB : 0<B) (hq : 0<q)
    (hqb : Real.log q/B≤b)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (hzright : ∀ v, b≤v → f v=0) (hfpb : f' b=0)
    (hcut : ∀ v ∈ Set.Icc (Real.log q/B) b, Real.exp (B*v)/q≤lemma81Cutoff D) :
    (∑ m ∈ lemma81PolynomialIndices D, coeff m*f (Real.log (q*(m : ℝ))/B)) =
      (B : ℂ)⁻¹*(∫ v in (Real.log q/B)..b,
        actualGramRampDensity ((B : ℂ)*gamma) f f' f'' v*
          actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q)) := by
  let a : ℝ := Real.log q/B
  have hab : a≤b := hqb
  let ell : ℂ := (B : ℂ)*gamma
  let h := actualGramRampDensity ell f f' f''
  have hc : Continuous h := actualGram_ramp_density_continuous ell f f' f'' hf hf' hf''
  have hendpoint (m : ℕ) (hm : m ∈ lemma81PolynomialIndices D) : a≤Real.log (q*(m : ℝ))/B := by
    have hm0 := ((proposition71_mem_indices D m).mp hm).1
    have hm1 : (1 : ℝ)≤m := by exact_mod_cast hm0
    apply div_le_div_of_nonneg_right _ hB.le
    apply Real.log_le_log hq
    nlinarith
  have hramp (m : ℕ) (hm : m ∈ lemma81PolynomialIndices D) :
      (∫ v in a..b, h v*actualGramClippedRamp ell (Real.log (q*(m : ℝ))/B) v) =
        f (Real.log (q*(m : ℝ))/B) :=
    actualGram_ramp_above_left_endpoint ell f f' f'' hqb (hendpoint m hm)
      hf hf' hf'' hzright hfpb
  have hi (m : ℕ) : IntervalIntegrable (fun v : ℝ => coeff m*
      (h v*actualGramClippedRamp ell (Real.log (q*(m : ℝ))/B) v)) volume a b :=
    (continuous_const.mul (hc.mul (actualGram_clipped_ramp_continuous ell _))).intervalIntegrable a b
  calc
    _ = ∑ m ∈ lemma81PolynomialIndices D, ∫ v in a..b, coeff m*
        (h v*actualGramClippedRamp ell (Real.log (q*(m : ℝ))/B) v) := by
      apply sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_const_mul,hramp m hm]
    _ = ∫ v in a..b, ∑ m ∈ lemma81PolynomialIndices D, coeff m*
        (h v*actualGramClippedRamp ell (Real.log (q*(m : ℝ))/B) v) :=
      (intervalIntegral.integral_finsetSum (fun m _ => hi m)).symm
    _ = ∫ v in a..b, (B : ℂ)⁻¹*(h v*actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      have hv' : v ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hv
      have he : (∑ m ∈ lemma81PolynomialIndices D, coeff m*
          (h v*actualGramClippedRamp ell (Real.log (q*(m : ℝ))/B) v)) =
          h v*(∑ m ∈ lemma81PolynomialIndices D, coeff m*
            actualGramClippedRamp ell (Real.log (q*(m : ℝ))/B) v) := by
        rw [mul_sum]
        apply sum_congr rfl
        intros; ring
      rw [he,actualGram_clipped_sum_eq_smoothed D coeff gamma hB hq v (hcut v hv')]
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end ZhangLS.Spec
