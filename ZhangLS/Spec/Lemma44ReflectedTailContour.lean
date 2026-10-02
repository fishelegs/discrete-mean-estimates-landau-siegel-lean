import ZhangLS.Spec.Lemma44ReflectedTail
import ZhangLS.Spec.Lemma44InitialLeftEstimates

/-!
# The reflected infinite tail integral

The uniform divisor-series saving and the local initial-left bounds give an
integrable actual tail integrand with a uniform `O(L^-180)` normalized integral.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_reflected_tail_vertical_continuous {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    Continuous (fun v : ℝ => ∑' n : ℕ,
      lemma44ReflectedTailTerm χ ψ (1 - s - lemma44InitialLeftShift s v) n) := by
  have hbase := summable_norm_iff.mpr lemma44_divisor_series_summable
  apply continuous_tsum (u := fun n : ℕ => Real.exp (-(lemma23PaperL D ^ 9) / 2) *
    ‖LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n‖)
  · intro n
    unfold lemma44ReflectedTailTerm
    by_cases hn : ⌊lemma23PaperP D ^ 2⌋₊ < n
    · simp only [if_pos hn]
      simp_rw [lemma44_LSeries_term_eq_exp _ _ (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))]
      unfold lemma44InitialLeftShift
      fun_prop
    · simp only [if_neg hn]
      exact continuous_const
  · exact hbase.mul_left _
  · intro n v
    apply lemma44_reflected_tail_term_bound χ ψ
    simp [lemma44InitialLeftShift]
    ring

noncomputable def lemma44ReflectedTailContourIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (v : ℝ) : ℂ :=
  let w := lemma44InitialLeftShift s v
  lemma44ActualZtilde χ ψ (s + w) *
    (∑' n : ℕ, lemma44ReflectedTailTerm χ ψ⁻¹ (1 - s - w) n) *
      exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) * lemma57OmegaOne D w / w

theorem lemma44_reflected_tail_contour_pointwise_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedTailContourIntegrand χ ψ s v‖ ≤
      2 * lemma44DivisorSeriesMass *
        Real.exp (3 * lemma23PaperL D + 1 + (9 / 5 : ℝ) * Real.pi -
          (3 / 10 : ℝ) * lemma23PaperL D ^ 9) := by
  let L := lemma23PaperL D
  let w := lemma44InitialLeftShift s v
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hz := lemma44_initial_left_Z_scale_bound χ ψ hD hψ hs hv
  have ho := lemma44_initial_left_omega_bound hL hs v
  have hd := lemma44_initial_left_denominator_bound hL hs v
  have ht := (lemma44_reflected_tail_summable_and_bound χ ψ⁻¹
    (z := 1 - s - w) (by simp [w, lemma44InitialLeftShift]; ring)).2
  have hm := lemma44_divisor_series_mass_nonneg
  unfold lemma44ReflectedTailContourIntegrand
  change ‖lemma44ActualZtilde χ ψ (s + w) *
    (∑' n : ℕ, lemma44ReflectedTailTerm χ ψ⁻¹ (1 - s - w) n) *
      exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) * lemma57OmegaOne D w / w‖ ≤ _
  calc
    _ = (‖lemma44ActualZtilde χ ψ (s + w)‖ *
        ‖exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖) *
        ‖∑' n : ℕ, lemma44ReflectedTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
          ‖lemma57OmegaOne D w‖ * ‖w‖⁻¹ := by
      simp only [norm_mul, norm_inv, div_eq_mul_inv]
      ring
    _ ≤ Real.exp (3 * L + (9 / 5 : ℝ) * Real.pi + L ^ 9 / 5) *
        (lemma44DivisorSeriesMass * Real.exp (-(L ^ 9) / 2)) * Real.exp 1 * 2 := by
      gcongr
    _ = _ := by
      calc
        _ = 2 * lemma44DivisorSeriesMass *
          (Real.exp (3 * L + (9 / 5 : ℝ) * Real.pi + L ^ 9 / 5) *
            Real.exp (-(L ^ 9) / 2) * Real.exp 1) := by ring
        _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          ring

theorem lemma44_reflected_tail_contour_continuousOn {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ContinuousOn (lemma44ReflectedTailContourIntegrand χ ψ s)
      (Set.Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hshift : Continuous (fun v : ℝ => lemma44InitialLeftShift s v) := by
    unfold lemma44InitialLeftShift
    fun_prop
  have hz : ContinuousOn (fun v : ℝ => lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v))
      (Set.Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
    intro v hv
    have hr := lemma44_initial_left_gamma_region hL hs (abs_le.mpr hv)
    have him := (lemma44_extended_gamma_region_height hL hr).2.2.1
    have hc : Continuous (fun v : ℝ => s + lemma44InitialLeftShift s v) :=
      continuous_const.add hshift
    exact (ContinuousAt.comp (f := fun v : ℝ => s + lemma44InitialLeftShift s v)
      (lemma44ActualZtilde_differentiableAt χ ψ him.ne').continuousAt
      hc.continuousAt).continuousWithinAt
  have htail := lemma44_reflected_tail_vertical_continuous χ ψ⁻¹ s
  have hB : Continuous (fun v : ℝ => exp (lemma44InitialLeftShift s v *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))) := by fun_prop
  have hO : Continuous (fun v : ℝ => lemma57OmegaOne D (lemma44InitialLeftShift s v)) := by
    unfold lemma57OmegaOne
    fun_prop
  have hne : ∀ v ∈ Set.Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
      lemma44InitialLeftShift s v ≠ 0 := by
    intro v _hv he
    have hre := congrArg Complex.re he
    simp only [lemma44_initial_left_shift_re, zero_re] at hre
    linarith [lemma44_omega3_re_pos hL hs]
  exact (((hz.mul htail.continuousOn).mul hB.continuousOn).mul hO.continuousOn).div₀
    hshift.continuousOn hne

theorem lemma44_reflected_tail_contour_intervalIntegrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    IntervalIntegrable (lemma44ReflectedTailContourIntegrand χ ψ s) volume
      (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have horder : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20 := by
    have hp : 0 ≤ lemma23PaperL D ^ 20 := by positivity
    linarith
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le horder]
  exact lemma44_reflected_tail_contour_continuousOn χ ψ hD hs

theorem lemma44_reflected_tail_contour_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
        lemma44ReflectedTailContourIntegrand χ ψ s v * I)‖ ≤
      (4 * lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * Real.pi)) *
        lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  let C := 2 * lemma44DivisorSeriesMass *
    Real.exp (3 * L + 1 + (9 / 5 : ℝ) * Real.pi - (3 / 10 : ℝ) * L ^ 9)
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hm := lemma44_divisor_series_mass_nonneg
  have hT : 0 ≤ L ^ 20 := by positivity
  have hlen : |L ^ 20 - -(L ^ 20)| = 2 * L ^ 20 := by
    rw [abs_of_nonneg (by linarith only [hT])]
    ring
  have hi : ‖∫ v : ℝ in -(L ^ 20)..L ^ 20,
      lemma44ReflectedTailContourIntegrand χ ψ s v * I‖ ≤ C * (2 * L ^ 20) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (congrArg (fun r : ℝ => C * r) hlen)
    intro v hv
    rw [Set.uIoc_of_le (by linarith only [hT] : -(L ^ 20) ≤ L ^ 20)] at hv
    rw [norm_mul, norm_I, mul_one]
    exact lemma44_reflected_tail_contour_pointwise_bound χ ψ hD hψ hs
      (abs_le.mpr ⟨hv.1.le, hv.2⟩)
  have hn : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, norm_mul, norm_I, mul_one]
    norm_num [Complex.norm_of_nonneg Real.pi_pos.le]
    have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.one_le_pi_div_two]
    have h := inv_le_one_of_one_le₀ hpi
    rw [abs_of_pos Real.pi_pos]
    convert h using 1
    ring
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∫ v : ℝ in -(L ^ 20)..L ^ 20,
        lemma44ReflectedTailContourIntegrand χ ψ s v * I‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ C * (2 * L ^ 20) := by simpa only [one_mul] using hi
    _ = (4 * lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * Real.pi)) *
        (L ^ 20 * Real.exp (3 * L - (3 / 10 : ℝ) * L ^ 9)) := by
      dsimp [C]
      have he : Real.exp (3 * L + 1 + (9 / 5 : ℝ) * Real.pi - (3 / 10 : ℝ) * L ^ 9) =
          Real.exp (1 + (9 / 5 : ℝ) * Real.pi) * Real.exp (3 * L - (3 / 10 : ℝ) * L ^ 9) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma44_initial_left_exponential_budget hL) (by positivity)

end ZhangLS.Spec
