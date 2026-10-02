import ZhangLS.Spec.Lemma57FullSmoothedSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Global positivity of Zhang's Gaussian weight

Step 15 only needed the easy range `x ≥ 1`, where the Gaussian endpoint is
nonnegative.  The full smoothed series also samples `0 < x < 1`, so we now prove
the genuine cumulative-Gaussian fact that Zhang's weight is nonnegative on every
positive argument.

For a negative endpoint `a`, symmetry of `exp (-t^2)` changes the loss
`∫_a^0 exp (-t^2)` into `∫_0^{-a} exp (-t^2)`.  This finite interval is contained
in the positive half-line, whose integral is exactly `sqrt pi / 2`.
-/

namespace ZhangLS.Spec

open Set MeasureTheory
open scoped Interval

private noncomputable def gaussianKernel (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2))

private theorem gaussianKernel_nonneg (t : ℝ) :
    0 ≤ gaussianKernel t := by
  exact (Real.exp_pos _).le

private theorem gaussianKernel_integrable :
    Integrable gaussianKernel := by
  simpa [gaussianKernel] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1))

/-- The positive half-line carries exactly half of the Gaussian mass. -/
private theorem gaussianKernel_integral_Ioi :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), gaussianKernel t = Real.sqrt Real.pi / 2 := by
  simpa [gaussianKernel] using (integral_gaussian_Ioi (1 : ℝ))

/-- A finite Gaussian interval starting at zero is bounded by the full positive
half-line Gaussian mass. -/
private theorem gaussianKernel_interval_le_half {b : ℝ} (hb : 0 ≤ b) :
    ∫ t : ℝ in (0 : ℝ)..b, gaussianKernel t ≤ Real.sqrt Real.pi / 2 := by
  rw [intervalIntegral.integral_of_le hb]
  calc
    (∫ t : ℝ in Set.Ioc (0 : ℝ) b, gaussianKernel t)
        ≤ ∫ t : ℝ in Set.Ioi (0 : ℝ), gaussianKernel t := by
          apply setIntegral_mono_set gaussianKernel_integrable.integrableOn
          · exact Filter.Eventually.of_forall gaussianKernel_nonneg
          · exact Set.Ioc_subset_Ioi_self.eventuallyLE
    _ = Real.sqrt Real.pi / 2 := gaussianKernel_integral_Ioi

/-- By evenness, a Gaussian interval to the left of zero has the same mass as
its reflected interval to the right. -/
private theorem gaussianKernel_interval_neg_symm {a : ℝ} (ha : a ≤ 0) :
    ∫ t : ℝ in a..(0 : ℝ), gaussianKernel t =
      ∫ t : ℝ in (0 : ℝ)..(-a), gaussianKernel t := by
  have h := intervalIntegral.integral_comp_neg
    (f := gaussianKernel) (a := (0 : ℝ)) (b := -a)
  simpa [gaussianKernel] using h.symm

/-- Splitting the positive Gaussian half-line at an arbitrary real point.  This
form is convenient for turning the finite-integral definition of Zhang's weight
into an actual Gaussian tail. -/
private theorem gaussianKernel_interval_add_tail (y : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..y, gaussianKernel t) +
        (∫ t : ℝ in Set.Ioi y, gaussianKernel t) = Real.sqrt Real.pi / 2 := by
  have h0 :
      Filter.Tendsto (fun b : ℝ => ∫ t : ℝ in (0 : ℝ)..b, gaussianKernel t)
        Filter.atTop (nhds (∫ t : ℝ in Set.Ioi (0 : ℝ), gaussianKernel t)) :=
    intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      gaussianKernel_integrable.integrableOn Filter.tendsto_id
  have hy :
      Filter.Tendsto (fun b : ℝ => ∫ t : ℝ in y..b, gaussianKernel t)
        Filter.atTop (nhds (∫ t : ℝ in Set.Ioi y, gaussianKernel t)) :=
    intervalIntegral_tendsto_integral_Ioi y
      gaussianKernel_integrable.integrableOn Filter.tendsto_id
  have hsplit :
      (fun b : ℝ => ∫ t : ℝ in (0 : ℝ)..b, gaussianKernel t) =
        (fun b : ℝ =>
          (∫ t : ℝ in (0 : ℝ)..y, gaussianKernel t) +
            ∫ t : ℝ in y..b, gaussianKernel t) := by
    funext b
    exact (intervalIntegral.integral_add_adjacent_intervals
      gaussianKernel_integrable.intervalIntegrable
      gaussianKernel_integrable.intervalIntegrable).symm
  rw [hsplit] at h0
  have hsum :
      Filter.Tendsto
        (fun b : ℝ =>
          (∫ t : ℝ in (0 : ℝ)..y, gaussianKernel t) +
            ∫ t : ℝ in y..b, gaussianKernel t)
        Filter.atTop
        (nhds ((∫ t : ℝ in (0 : ℝ)..y, gaussianKernel t) +
          ∫ t : ℝ in Set.Ioi y, gaussianKernel t)) :=
    tendsto_const_nhds.add hy
  have hlimit := tendsto_nhds_unique h0 hsum
  rw [gaussianKernel_integral_Ioi] at hlimit
  exact hlimit.symm

/-- For a nonpositive endpoint, Zhang's finite normalization is exactly the
normalized positive Gaussian tail beginning at the reflected endpoint. -/
theorem zhangGaussianWeight_eq_tail_of_endpoint_nonpos
    {D : ℕ} {x : ℝ} (ha : zhangGaussianEndpoint D x ≤ 0) :
    zhangGaussianWeight D x =
      (Real.sqrt Real.pi)⁻¹ *
        ∫ t : ℝ in Set.Ioi (-zhangGaussianEndpoint D x), Real.exp (-(t ^ 2)) := by
  let a := zhangGaussianEndpoint D x
  have hsymm :
      ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t =
        -(∫ t : ℝ in a..(0 : ℝ), gaussianKernel t) := by
    simpa using intervalIntegral.integral_symm (f := gaussianKernel) a (0 : ℝ)
  have hreflect :
      ∫ t : ℝ in a..(0 : ℝ), gaussianKernel t =
        ∫ t : ℝ in (0 : ℝ)..(-a), gaussianKernel t :=
    gaussianKernel_interval_neg_symm (by simpa [a] using ha)
  have hmass := gaussianKernel_interval_add_tail (-a)
  have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hkernel :
      (∫ t : ℝ in (0 : ℝ)..zhangGaussianEndpoint D x,
        Real.exp (-(t ^ 2))) =
        ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t := by
    simp [a, gaussianKernel]
  unfold zhangGaussianWeight
  rw [hkernel]
  rw [hsymm, hreflect]
  have htail :
      ∫ t : ℝ in Set.Ioi (-a), gaussianKernel t =
        Real.sqrt Real.pi / 2 - ∫ t : ℝ in (0 : ℝ)..(-a), gaussianKernel t := by
    linarith
  have hrhs :
      (∫ t : ℝ in Set.Ioi (-zhangGaussianEndpoint D x), Real.exp (-(t ^ 2))) =
        ∫ t : ℝ in Set.Ioi (-a), gaussianKernel t := by
    simp [a, gaussianKernel]
  rw [hrhs, htail]
  simp only [gaussianKernel]
  field_simp [hsqrt_pos.ne']
  ring

/-- A generic exponential majorant for the Gaussian tail.  If `K ≤ y`, then
`t² ≥ K t` on `t > y`, hence `exp(-t²) ≤ exp(-K t)` and the latter integrates
explicitly. -/
theorem zhangGaussianTail_le_exp_linear
    {K y : ℝ} (hK : 0 < K) (hy : K ≤ y) :
    (∫ t : ℝ in Set.Ioi y, Real.exp (-(t ^ 2))) ≤ Real.exp (-K * y) / K := by
  have hgauss : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi y) := by
    simpa [gaussianKernel] using gaussianKernel_integrable.integrableOn
  have hlin : IntegrableOn (fun t : ℝ => Real.exp ((-K) * t)) (Set.Ioi y) :=
    integrableOn_exp_mul_Ioi (by linarith) y
  have hpoint :
      (fun t : ℝ => Real.exp (-(t ^ 2))) ≤ᵐ[volume.restrict (Set.Ioi y)]
        (fun t : ℝ => Real.exp ((-K) * t)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have hKt : K ≤ t := hy.trans ht.le
    have ht0 : 0 ≤ t := le_trans hK.le hKt
    have hquad : K * t ≤ t ^ 2 := by
      nlinarith
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (∫ t : ℝ in Set.Ioi y, Real.exp (-(t ^ 2)))
        ≤ ∫ t : ℝ in Set.Ioi y, Real.exp ((-K) * t) :=
      setIntegral_mono_ae_restrict hgauss hlin hpoint
    _ = -Real.exp ((-K) * y) / (-K) :=
      integral_exp_mul_Ioi (a := -K) (by linarith) y
    _ = Real.exp (-K * y) / K := by
      ring


/-- Along the sequence sampled by Lemma 5.7, the reflected Gaussian endpoint is
exactly a positive multiple of `log (n / D^4)`.  This is the algebraic form in
which the tail tends to infinity. -/
theorem neg_zhangGaussianEndpoint_weightArgument_eq
    {D n : ℕ} (hD : 0 < D) (hn : 0 < n) :
    -zhangGaussianEndpoint D (lemma57WeightArgument D n) =
      (Real.log (D : ℝ)) ^ 15 *
        Real.log ((n : ℝ) / (D : ℝ) ^ 4) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hD4 : ((D : ℝ) ^ 4) ≠ 0 := pow_ne_zero _ hDr
  unfold zhangGaussianEndpoint lemma57WeightArgument
  rw [Real.log_div hD4 hnr, Real.log_div hnr hD4]
  rw [Real.log_pow]
  ring

/-- For every nontrivial modulus, the reflected endpoint sampled at `D^4 / n`
tends to `+∞`.  Thus every fixed positive Gaussian-tail threshold is eventually
reached. -/
theorem neg_zhangGaussianEndpoint_weightArgument_tendsto_atTop
    {D : ℕ} (hD : 1 < D) :
    Filter.Tendsto
      (fun n : ℕ => -zhangGaussianEndpoint D (lemma57WeightArgument D n))
      Filter.atTop Filter.atTop := by
  have hDposNat : 0 < D := Nat.zero_lt_of_lt hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
  have hlogD : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD)
  have hc : 0 < (Real.log (D : ℝ)) ^ 15 := pow_pos hlogD _
  have hD4 : 0 < (D : ℝ) ^ 4 := pow_pos hDpos _
  have hratio :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) / (D : ℝ) ^ 4)
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hD4 tendsto_natCast_atTop_atTop
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ => (Real.log (D : ℝ)) ^ 15 *
          Real.log ((n : ℝ) / (D : ℝ) ^ 4))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp hratio)
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact (neg_zhangGaussianEndpoint_weightArgument_eq hDposNat hn).symm

/-- A ready-to-use eventual exponential majorant for Zhang's Gaussian weight
along the Lemma 5.7 sequence.  The remaining passage to `n⁻³` is purely
logarithmic/algebraic. -/
theorem zhangGaussianWeight_eventually_le_exp_tail
    {D : ℕ} (hD : 1 < D) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in Filter.atTop,
      zhangGaussianWeight D (lemma57WeightArgument D n) ≤
        (Real.sqrt Real.pi)⁻¹ *
          (Real.exp
              (-K * (-zhangGaussianEndpoint D (lemma57WeightArgument D n))) / K) := by
  have hend :=
    (neg_zhangGaussianEndpoint_weightArgument_tendsto_atTop hD).eventually_ge_atTop K
  filter_upwards [hend, Filter.eventually_gt_atTop 0] with n hnend hn
  have hendpoint :
      zhangGaussianEndpoint D (lemma57WeightArgument D n) ≤ 0 := by
    linarith
  rw [zhangGaussianWeight_eq_tail_of_endpoint_nonpos hendpoint]
  have htail := zhangGaussianTail_le_exp_linear hK hnend
  exact mul_le_mul_of_nonneg_left htail
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The finite Gaussian normalization used in `zhangGaussianWeight` is globally
nonnegative on positive arguments.  The condition `1 < D` ensures `log D > 0`,
which is the paper's modulus range; the proof only uses the sign split of the
endpoint itself. -/
theorem zhangGaussianWeight_nonneg
    {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    0 ≤ zhangGaussianWeight D x := by
  let a := zhangGaussianEndpoint D x
  by_cases ha : 0 ≤ a
  · unfold zhangGaussianWeight
    have hint : 0 ≤ ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t := by
      refine intervalIntegral.integral_nonneg_of_forall ha ?_
      intro t
      exact gaussianKernel_nonneg t
    have hsqrt : 0 ≤ (Real.sqrt Real.pi)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    have htail : 0 ≤ (Real.sqrt Real.pi)⁻¹ *
        ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t :=
      mul_nonneg hsqrt hint
    simpa [a, gaussianKernel] using (show (0 : ℝ) ≤ (1 : ℝ) / 2 +
      (Real.sqrt Real.pi)⁻¹ * ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t by
        linarith)
  · have ha' : a < 0 := lt_of_not_ge ha
    have hreflect :
        ∫ t : ℝ in a..(0 : ℝ), gaussianKernel t ≤ Real.sqrt Real.pi / 2 := by
      rw [gaussianKernel_interval_neg_symm ha'.le]
      exact gaussianKernel_interval_le_half (neg_nonneg.mpr ha'.le)
    have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have hscaled :
        (Real.sqrt Real.pi)⁻¹ *
            (∫ t : ℝ in a..(0 : ℝ), gaussianKernel t) ≤ (1 : ℝ) / 2 := by
      calc
        (Real.sqrt Real.pi)⁻¹ *
            (∫ t : ℝ in a..(0 : ℝ), gaussianKernel t)
            ≤ (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi / 2) := by
              exact mul_le_mul_of_nonneg_left hreflect
                (inv_nonneg.mpr hsqrt_pos.le)
        _ = (1 : ℝ) / 2 := by field_simp [hsqrt_pos.ne']
    unfold zhangGaussianWeight
    have hsymm :
        ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t =
          -(∫ t : ℝ in a..(0 : ℝ), gaussianKernel t) := by
      simpa using intervalIntegral.integral_symm (f := gaussianKernel) a (0 : ℝ)
    have hkernel :
        (∫ t : ℝ in (0 : ℝ)..zhangGaussianEndpoint D x,
          Real.exp (-(t ^ 2))) =
          ∫ t : ℝ in (0 : ℝ)..a, gaussianKernel t := by
      simp [a, gaussianKernel]
    rw [hkernel]
    rw [hsymm]
    linarith

/-- The exact global sign interface introduced in Step 18 is now unconditional. -/
theorem zhangGaussianWeightNonnegative_proved
    {D : ℕ} (hD : 1 < D) : ZhangGaussianWeightNonnegative D := by
  intro x hx
  exact zhangGaussianWeight_nonneg hD hx

/-- After global positivity is discharged, convergence is the only remaining
analytic hypothesis in the full-series arithmetic lower bound. -/
theorem lemma57_full_gaussian_arithmetic_scale_of_summable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hsum : Lemma57FullSmoothedSummable χ (zhangGaussianWeight D)) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) := by
  exact lemma57_full_gaussian_arithmetic_scale χ hD hsum
    (zhangGaussianWeightNonnegative_proved hD)

/-- Corresponding arithmetic-lower-bound package with only summability left as
an input. -/
noncomputable def lemma57FullArithmeticLowerBound_of_summable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hsum : Lemma57FullSmoothedSummable χ (zhangGaussianWeight D)) :
    Lemma57ArithmeticLowerBound D :=
  lemma57FullArithmeticLowerBound χ hD hsum
    (zhangGaussianWeightNonnegative_proved hD)

end ZhangLS.Spec
