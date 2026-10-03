import ZhangLS.Spec.LogContourBounds
import ZhangLS.Spec.LogGaussianInverse

/-! Exact absolutely convergent squared-Perron Mellin series for actual ν². -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real BigOperators

lemma lemma171_log_mellin_integrand_eq_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (w : ℂ) (hw : 0 < w.re) :
    lemma171LogMellinIntegrand χ w = lemma171DirichletSeries χ (1+w) *
      ((lemma56PaperT D : ℂ)^w * lemma57OmegaOne D w) / w^2 := by
  rw [lemma171LogMellinIntegrand, lemma171_mellin_integrand_eq_series χ w hw,
    div_div, ← pow_two]

noncomputable def lemma171LogSmoothedTerm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n : ℕ) : ℝ :=
  lemma171Coefficient χ n / (n : ℝ) *
    lemma171LogGaussianWeight D (lemma171WeightArgument D n)

noncomputable def lemma171LogSmoothedSum {D : ℕ} (χ : RealPrimitiveCharacter D) : ℝ :=
  ∑' n : ℕ, lemma171LogSmoothedTerm χ n

/-- The contribution of one squared-ν L-series coefficient to the
unnormalized vertical integral on `re s = 1`. -/
noncomputable def lemma171LogMellinSeriesTerm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) (t : ℝ) : ℂ :=
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (1 + z) n *
    lemma171GaussianMellinFactor D z / z ^ 2 * I

/-- Pointwise expansion of the full Mellin integrand into its L-series terms. -/
theorem lemma171LogMellinSeriesTerm_tsum
    {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) :
    (∑' n : ℕ, lemma171LogMellinSeriesTerm χ n t) =
      lemma171LogMellinIntegrand χ ((1 : ℂ) + (t : ℂ) * I) * I := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hz : ((1 : ℂ) + z).re = 2 := by
    norm_num [z]
  rw [lemma171_log_mellin_integrand_eq_series χ z (by norm_num [z])]
  unfold lemma171DirichletSeries LSeries lemma171LogMellinSeriesTerm
  simp_rw [lemma171_gaussian_factor_eq_paper]
  dsimp [z]
  simp_rw [div_eq_mul_inv, mul_assoc]
  rw [tsum_mul_right]

/-- Every coefficientwise integrand has the same scalar Gaussian norm profile,
up to its absolutely summable L-series coefficient. -/
theorem lemma171LogMellinSeriesTerm_norm
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (n : ℕ) (t : ℝ) :
    ‖lemma171LogMellinSeriesTerm χ n t‖ =
      (lemma56PaperT D *
          ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖) *
        ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖ := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.zero_lt_of_lt hD
  have hterm :
      ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (1 + z) n‖ =
        ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    norm_num [z]
  have hcpow : ‖(lemma56PaperT D : ℂ) ^ z‖ = lemma56PaperT D := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lemma56_paper_T_pos D)]
    norm_num [z]
  rw [lemma171LogMellinSeriesTerm]
  rw [lemma171_gaussian_factor_eq_paper]
  rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_I,
    mul_one, hterm, hcpow]
  simp only [lemma171LogGaussianKernelIntegrand, norm_div]
  norm_num [z]
  ring

/-- Each coefficientwise vertical integrand is Bochner integrable. -/
theorem lemma171LogMellinSeriesTerm_integrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (n : ℕ) : Integrable (lemma171LogMellinSeriesTerm χ n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : lemma171LogMellinSeriesTerm χ 0 = 0 := by
      funext t
      simp [lemma171LogMellinSeriesTerm]
    rw [hzero]
    exact integrable_zero ℝ ℂ volume
  let C : ℝ := lemma56PaperT D *
    ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖
  have hK : Integrable (lemma171LogGaussianKernelIntegrand D 1 1) :=
    lemma171_log_gaussian_kernel_integrable hD one_ne_zero zero_lt_one
  have hmajor : Integrable (fun t : ℝ =>
      C * ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖) :=
    hK.norm.const_mul C
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    let z : ℝ → ℂ := fun t => (1 : ℂ) + (t : ℂ) * I
    have hzcont : Continuous z := by
      dsimp [z]
      fun_prop
    have hzne : ∀ t : ℝ, z t ≠ 0 := by
      intro t ht
      have hre := congrArg Complex.re ht
      norm_num [z] at hre
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have htermcont : Continuous (fun t : ℝ =>
        LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (1 + z t) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      apply Continuous.div₀ continuous_const
        ((continuous_const.add hzcont).const_cpow (Or.inl hnC))
      intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hfactorcont : Continuous (fun t : ℝ =>
        lemma171GaussianMellinFactor D (z t)) := by
      unfold lemma171GaussianMellinFactor
      fun_prop
    unfold lemma171LogMellinSeriesTerm
    change Continuous (fun t : ℝ =>
      LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (1 + z t) n *
        lemma171GaussianMellinFactor D (z t) / z t ^ 2 * I)
    exact ((htermcont.mul hfactorcont).div₀ (hzcont.pow 2) (fun t => pow_ne_zero 2 (hzne t))).mul
      continuous_const
  · filter_upwards [] with t
    rw [lemma171LogMellinSeriesTerm_norm χ hD n t]

/-- The integrals of the coefficientwise norms form a summable series. -/
theorem lemma171LogMellinSeriesTerm_integral_norm_summable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖lemma171LogMellinSeriesTerm χ n t‖) := by
  let K : ℝ := lemma56PaperT D *
    ∫ t : ℝ, ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖
  have hL : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma171LSeriesSummable_two χ)
  have hscaled : Summable (fun n : ℕ =>
      K * ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖) :=
    hL.mul_left K
  apply hscaled.congr
  intro n
  simp_rw [lemma171LogMellinSeriesTerm_norm χ hD n]
  rw [MeasureTheory.integral_const_mul]
  dsimp [K]
  ring

/-- The pointwise sum of the coefficientwise integrands is integrable. -/
theorem lemma171LogMellinSeriesTerm_tsum_integrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Integrable (fun t : ℝ =>
      ∑' n : ℕ, lemma171LogMellinSeriesTerm χ n t) := by
  let A : ℝ := ∑' n : ℕ,
    ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖
  let C : ℝ := lemma56PaperT D * A
  have hL : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma171LSeriesSummable_two χ)
  have hK : Integrable (lemma171LogGaussianKernelIntegrand D 1 1) :=
    lemma171_log_gaussian_kernel_integrable hD one_ne_zero zero_lt_one
  have hmajor : Integrable (fun t : ℝ =>
      C * ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖) :=
    hK.norm.const_mul C
  apply hmajor.mono'
  · exact AEStronglyMeasurable.tsum fun n =>
      (lemma171LogMellinSeriesTerm_integrable χ hD n).1
  · filter_upwards [] with t
    have hnormsum : Summable (fun n : ℕ =>
        ‖lemma171LogMellinSeriesTerm χ n t‖) := by
      have hs := hL.mul_left
        (lemma56PaperT D * ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖)
      apply hs.congr
      intro n
      rw [lemma171LogMellinSeriesTerm_norm χ hD n t]
      ring
    calc
      ‖∑' n : ℕ, lemma171LogMellinSeriesTerm χ n t‖
          ≤ ∑' n : ℕ, ‖lemma171LogMellinSeriesTerm χ n t‖ :=
        norm_tsum_le_tsum_norm hnormsum
      _ = ∑' n : ℕ,
          (lemma56PaperT D * ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖) *
            ‖LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) (2 : ℂ) n‖ := by
        apply tsum_congr
        intro n
        rw [lemma171LogMellinSeriesTerm_norm χ hD n t]
        ring
      _ = (lemma56PaperT D * ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖) * A := by
        rw [tsum_mul_left]
      _ = C * ‖lemma171LogGaussianKernelIntegrand D 1 1 t‖ := by
        dsimp [A, C]
        ring

/-- A coefficientwise integrand is a constant multiple of the scalar Gaussian
kernel evaluated at `T/n`. -/
theorem lemma171LogMellinSeriesTerm_eq_kernel
    {D : ℕ} (χ : RealPrimitiveCharacter D) (_hD : 1 < D)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    lemma171LogMellinSeriesTerm χ n t =
      ((lemma171Coefficient χ n : ℂ) / (n : ℂ)) *
        (lemma171LogGaussianKernelIntegrand D 1
          (lemma171WeightArgument D n) t * I) := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  let x : ℝ := lemma171WeightArgument D n
  have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have hx : 0 < x := by
    dsimp [x, lemma171WeightArgument]
    exact div_pos (lemma56_paper_T_pos D) hnpos
  have hxn : x * (n : ℝ) = lemma56PaperT D := by
    dsimp [x, lemma171WeightArgument]
    field_simp
  have hxpow : (x : ℂ) ^ z =
      (lemma56PaperT D : ℂ) ^ z / (n : ℂ) ^ z := by
    rw [hncast]
    have hncpowR : (((n : ℝ) : ℂ) ^ z) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr hnpos.ne'))
    apply (eq_div_iff hncpowR).2
    have hmul := Complex.mul_cpow_ofReal_nonneg hx.le hnpos.le z
    have hbase : (x : ℂ) * ((n : ℝ) : ℂ) = (lemma56PaperT D : ℂ) := by
      exact_mod_cast hxn
    rw [← hmul, hbase]
  rw [lemma171LogMellinSeriesTerm,
    lemma171_gaussian_factor_eq_paper,
    LSeries.term_of_ne_zero hn]
  simp only [lemma171LogGaussianKernelIntegrand]
  change (lemma171Coefficient χ n : ℂ) / (n : ℂ) ^ (1 + z) *
      ((lemma56PaperT D : ℂ) ^ z * lemma57OmegaOne D z) / z ^ 2 * I =
    ((lemma171Coefficient χ n : ℂ) / (n : ℂ)) *
      ((x : ℂ) ^ z * lemma57OmegaOne D z / z ^ 2 * I)
  rw [Complex.cpow_add _ _ hnC, Complex.cpow_one, hxpow]
  field_simp

/-- The normalized integral of one L-series coefficient is precisely the
corresponding summand in Zhang's full smoothed sum. -/
theorem lemma171LogMellinSeriesTerm_normalized_integral
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t : ℝ, lemma171LogMellinSeriesTerm χ n t =
      (lemma171LogSmoothedTerm χ n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    have hzero : lemma171LogMellinSeriesTerm χ 0 = 0 := by
      funext t
      simp [lemma171LogMellinSeriesTerm]
    rw [hzero]
    simp [lemma171LogSmoothedTerm]
  have hpoint := lemma171LogMellinSeriesTerm_eq_kernel χ hD hn
  simp_rw [hpoint, MeasureTheory.integral_const_mul]
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ *
          (((lemma171Coefficient χ n : ℂ) / (n : ℂ)) *
            ∫ t : ℝ, lemma171LogGaussianKernelIntegrand D 1
              (lemma171WeightArgument D n) t * I) =
        ((lemma171Coefficient χ n : ℂ) / (n : ℂ)) *
          lemma171LogGaussianKernelVerticalIntegral D 1
            (lemma171WeightArgument D n) := by
              rw [lemma171LogGaussianKernelVerticalIntegral]
              ring
    _ = _ := by
      have harg : 0 < lemma171WeightArgument D n := by
        unfold lemma171WeightArgument
        have hDp := lemma56_paper_T_pos D
        have hnp : (0 : ℝ) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      rw [lemma171LogGaussianKernelVerticalIntegral_eq_weight hD zero_lt_one harg]
      rw [lemma171LogSmoothedTerm]
      unfold lemma171WeightArgument
      push_cast
      ring


/-- Absolute convergence of the actual smoothed harmonic series. It follows
from the coefficientwise Gaussian integral bound, without a presumed tail estimate. -/
theorem lemma171_log_smoothed_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) : Summable (lemma171LogSmoothedTerm χ) := by
  apply Complex.summable_ofReal.mp
  have hs := (lemma171LogMellinSeriesTerm_integral_norm_summable χ hD).mul_left
    ‖(2*(Real.pi : ℂ)*I)⁻¹‖
  apply hs.of_norm_bounded
  intro n
  rw [← lemma171LogMellinSeriesTerm_normalized_integral χ hD n, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (norm_nonneg _)

/-- Absolute convergence, genuine vertical integrability, and the exact
infinite Gaussian Mellin identity for the actual ν² harmonic coefficients. -/
theorem lemma171_log_gaussian_mellin_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Integrable (fun t : ℝ =>
      lemma171LogMellinIntegrand χ ((1 : ℂ)+(t : ℂ)*I)*I) ∧
    lemma171LogVerticalIntegral χ 1 = (lemma171LogSmoothedSum χ : ℂ) := by
  constructor
  · apply (lemma171LogMellinSeriesTerm_tsum_integrable χ hD).congr
    filter_upwards [] with t
    exact lemma171LogMellinSeriesTerm_tsum χ t
  · unfold lemma171LogVerticalIntegral
    have hinterchange := MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n : ℕ => lemma171LogMellinSeriesTerm_integrable χ hD n)
      (lemma171LogMellinSeriesTerm_integral_norm_summable χ hD)
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∫ t : ℝ, lemma171LogMellinIntegrand χ
            ((1 : ℂ) + (t : ℂ) * I) * I =
          (2 * (Real.pi : ℂ) * I)⁻¹ *
            ∫ t : ℝ, ∑' n : ℕ, lemma171LogMellinSeriesTerm χ n t := by
              congr 1
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with t
              exact (lemma171LogMellinSeriesTerm_tsum χ t).symm
      _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∑' n : ℕ, ∫ t : ℝ, lemma171LogMellinSeriesTerm χ n t := by
            rw [hinterchange]
      _ = ∑' n : ℕ, (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∫ t : ℝ, lemma171LogMellinSeriesTerm χ n t := by
            rw [tsum_mul_left]
      _ = ∑' n : ℕ, (lemma171LogSmoothedTerm χ n : ℂ) := by
            apply tsum_congr
            intro n
            exact lemma171LogMellinSeriesTerm_normalized_integral χ hD n
      _ = (lemma171LogSmoothedSum χ : ℂ) := by
        unfold lemma171LogSmoothedSum
        simpa using (Complex.ofRealCLM.map_tsum
          (lemma171_log_smoothed_summable χ hD)).symm

end ZhangLS.Spec
