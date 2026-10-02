import ZhangLS.Spec.Lemma57GaussianMellinTransform

/-!
# The exact Mellin identity in Zhang's Lemma 5.7

This module combines the scalar Gaussian Mellin transform with the absolutely
convergent divisor-character L-series on `re s = 2`.  A common Gaussian
majorant justifies exchanging the series and the vertical Bochner integral.
The resulting coefficientwise inverse Mellin formula is exactly Zhang's full
smoothed sum.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped Real BigOperators

/-- The contribution of one divisor-character L-series coefficient to the
unnormalized vertical integral on `re s = 1`. -/
noncomputable def lemma57MellinSeriesTerm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) (t : ℝ) : ℂ :=
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  LSeries.term (divisorCharacterSum χ) (1 + z) n *
    lemma57GaussianMellinFactor D z / z * I

/-- Absolute convergence of the divisor-character L-series at the fixed real
part used for the interchange. -/
theorem lemma57DivisorCharacterLSeriesSummable_two
    {D : ℕ} (χ : RealPrimitiveCharacter D) :
    LSeriesSummable (divisorCharacterSum χ) (2 : ℂ) := by
  rw [LSeriesSummable_congr (2 : ℂ)
    (fun {_n} _hn => divisorCharacterSum_eq_zetaMul χ)]
  exact χ.chi.LSeriesSummable_zetaMul (by norm_num)

/-- Pointwise expansion of the full Mellin integrand into its L-series terms. -/
theorem lemma57MellinSeriesTerm_tsum
    {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) :
    (∑' n : ℕ, lemma57MellinSeriesTerm χ n t) =
      lemma57MellinIntegrand χ ((1 : ℂ) + (t : ℂ) * I) * I := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hz : ((1 : ℂ) + z).re = 2 := by
    norm_num [z]
  have hprod := lemma57DirichletProduct_eq_divisorCharacterLSeries
    χ (s := 1 + z) (by rw [hz]; norm_num)
  rw [lemma57MellinIntegrand, hprod]
  unfold LSeries lemma57MellinSeriesTerm
  dsimp [z]
  simp_rw [div_eq_mul_inv, mul_assoc]
  rw [tsum_mul_right]

/-- Every coefficientwise integrand has the same scalar Gaussian norm profile,
up to its absolutely summable L-series coefficient. -/
theorem lemma57MellinSeriesTerm_norm
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (n : ℕ) (t : ℝ) :
    ‖lemma57MellinSeriesTerm χ n t‖ =
      ((D : ℝ) ^ 4 *
          ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖) *
        ‖lemma57GaussianKernelIntegrand D 1 1 t‖ := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.zero_lt_of_lt hD
  have hterm :
      ‖LSeries.term (divisorCharacterSum χ) (1 + z) n‖ =
        ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    norm_num [z]
  have hDcast : (D : ℂ) = ((D : ℝ) : ℂ) := by norm_num
  have hcpow : ‖(D : ℂ) ^ (4 * z)‖ = (D : ℝ) ^ 4 := by
    rw [hDcast, Complex.norm_cpow_eq_rpow_re_of_pos hDpos]
    norm_num [z]
  rw [lemma57MellinSeriesTerm]
  rw [lemma57GaussianMellinFactor_eq_cpow_mul_omegaOne hD]
  rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_I,
    mul_one, hterm, hcpow]
  simp only [lemma57GaussianKernelIntegrand, norm_div]
  norm_num [z]
  ring

/-- Each coefficientwise vertical integrand is Bochner integrable. -/
theorem lemma57MellinSeriesTerm_integrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (n : ℕ) : Integrable (lemma57MellinSeriesTerm χ n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : lemma57MellinSeriesTerm χ 0 = 0 := by
      funext t
      simp [lemma57MellinSeriesTerm]
    rw [hzero]
    exact integrable_zero ℝ ℂ volume
  let C : ℝ := (D : ℝ) ^ 4 *
    ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖
  have hK : Integrable (lemma57GaussianKernelIntegrand D 1 1) :=
    lemma57GaussianKernel_integrable hD one_ne_zero zero_lt_one
  have hmajor : Integrable (fun t : ℝ =>
      C * ‖lemma57GaussianKernelIntegrand D 1 1 t‖) :=
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
        LSeries.term (divisorCharacterSum χ) (1 + z t) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      apply Continuous.div₀ continuous_const
        ((continuous_const.add hzcont).const_cpow (Or.inl hnC))
      intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hfactorcont : Continuous (fun t : ℝ =>
        lemma57GaussianMellinFactor D (z t)) := by
      unfold lemma57GaussianMellinFactor
      fun_prop
    unfold lemma57MellinSeriesTerm
    change Continuous (fun t : ℝ =>
      LSeries.term (divisorCharacterSum χ) (1 + z t) n *
        lemma57GaussianMellinFactor D (z t) / z t * I)
    exact ((htermcont.mul hfactorcont).div₀ hzcont hzne).mul
      continuous_const
  · filter_upwards [] with t
    rw [lemma57MellinSeriesTerm_norm χ hD n t]

/-- The integrals of the coefficientwise norms form a summable series. -/
theorem lemma57MellinSeriesTerm_integral_norm_summable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖lemma57MellinSeriesTerm χ n t‖) := by
  let K : ℝ := (D : ℝ) ^ 4 *
    ∫ t : ℝ, ‖lemma57GaussianKernelIntegrand D 1 1 t‖
  have hL : Summable (fun n : ℕ =>
      ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma57DivisorCharacterLSeriesSummable_two χ)
  have hscaled : Summable (fun n : ℕ =>
      K * ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖) :=
    hL.mul_left K
  apply hscaled.congr
  intro n
  simp_rw [lemma57MellinSeriesTerm_norm χ hD n]
  rw [MeasureTheory.integral_const_mul]
  dsimp [K]
  ring

/-- The pointwise sum of the coefficientwise integrands is integrable. -/
theorem lemma57MellinSeriesTerm_tsum_integrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Integrable (fun t : ℝ =>
      ∑' n : ℕ, lemma57MellinSeriesTerm χ n t) := by
  let A : ℝ := ∑' n : ℕ,
    ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖
  let C : ℝ := (D : ℝ) ^ 4 * A
  have hL : Summable (fun n : ℕ =>
      ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖) :=
    summable_norm_iff.mpr (lemma57DivisorCharacterLSeriesSummable_two χ)
  have hK : Integrable (lemma57GaussianKernelIntegrand D 1 1) :=
    lemma57GaussianKernel_integrable hD one_ne_zero zero_lt_one
  have hmajor : Integrable (fun t : ℝ =>
      C * ‖lemma57GaussianKernelIntegrand D 1 1 t‖) :=
    hK.norm.const_mul C
  apply hmajor.mono'
  · exact AEStronglyMeasurable.tsum fun n =>
      (lemma57MellinSeriesTerm_integrable χ hD n).1
  · filter_upwards [] with t
    have hnormsum : Summable (fun n : ℕ =>
        ‖lemma57MellinSeriesTerm χ n t‖) := by
      have hs := hL.mul_left
        ((D : ℝ) ^ 4 * ‖lemma57GaussianKernelIntegrand D 1 1 t‖)
      apply hs.congr
      intro n
      rw [lemma57MellinSeriesTerm_norm χ hD n t]
      ring
    calc
      ‖∑' n : ℕ, lemma57MellinSeriesTerm χ n t‖
          ≤ ∑' n : ℕ, ‖lemma57MellinSeriesTerm χ n t‖ :=
        norm_tsum_le_tsum_norm hnormsum
      _ = ∑' n : ℕ,
          ((D : ℝ) ^ 4 * ‖lemma57GaussianKernelIntegrand D 1 1 t‖) *
            ‖LSeries.term (divisorCharacterSum χ) (2 : ℂ) n‖ := by
        apply tsum_congr
        intro n
        rw [lemma57MellinSeriesTerm_norm χ hD n t]
        ring
      _ = ((D : ℝ) ^ 4 * ‖lemma57GaussianKernelIntegrand D 1 1 t‖) * A := by
        rw [tsum_mul_left]
      _ = C * ‖lemma57GaussianKernelIntegrand D 1 1 t‖ := by
        dsimp [A, C]
        ring

/-- A coefficientwise integrand is a constant multiple of the scalar Gaussian
kernel evaluated at `D⁴/n`. -/
theorem lemma57MellinSeriesTerm_eq_kernel
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    lemma57MellinSeriesTerm χ n t =
      (divisorCharacterSum χ n / (n : ℂ)) *
        (lemma57GaussianKernelIntegrand D 1
          (lemma57WeightArgument D n) t * I) := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  let x : ℝ := lemma57WeightArgument D n
  have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have hDcast : (D : ℂ) = ((D : ℝ) : ℂ) := by norm_num
  have hx : 0 < x := by
    dsimp [x, lemma57WeightArgument]
    positivity
  have hxn : x * (n : ℝ) = (D : ℝ) ^ 4 := by
    dsimp [x, lemma57WeightArgument]
    field_simp
  have hxpow : (x : ℂ) ^ z =
      (D : ℂ) ^ (4 * z) / (n : ℂ) ^ z := by
    rw [hncast, hDcast]
    have hncpowR : (((n : ℝ) : ℂ) ^ z) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr hnpos.ne'))
    apply (eq_div_iff hncpowR).2
    have hmul := Complex.mul_cpow_ofReal_nonneg hx.le hnpos.le z
    have hbase : (x : ℂ) * ((n : ℝ) : ℂ) =
        (((D : ℝ) ^ 4 : ℝ) : ℂ) := by
      norm_cast
      simpa only [Nat.cast_pow] using hxn
    rw [← hmul, hbase]
    push_cast
    simpa using (Complex.natCast_cpow_natCast_mul D 4 z).symm
  rw [lemma57MellinSeriesTerm,
    lemma57GaussianMellinFactor_eq_cpow_mul_omegaOne hD,
    LSeries.term_of_ne_zero hn]
  simp only [lemma57GaussianKernelIntegrand]
  change divisorCharacterSum χ n / (n : ℂ) ^ (1 + z) *
      ((D : ℂ) ^ (4 * z) * lemma57OmegaOne D z) / z * I =
    (divisorCharacterSum χ n / (n : ℂ)) *
      ((x : ℂ) ^ z * lemma57OmegaOne D z / z * I)
  rw [Complex.cpow_add _ _ hnC, Complex.cpow_one, hxpow]
  field_simp

/-- The complex divisor-character coefficient is the coercion of its declared
real form. -/
theorem divisorCharacterSumReal_coe
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (divisorCharacterSumReal χ n : ℂ) = divisorCharacterSum χ n := by
  apply Complex.ext
  · simp [divisorCharacterSumReal]
  · simp only [Complex.ofReal_im]
    unfold divisorCharacterSum
    rw [Complex.im_sum]
    symm
    apply Finset.sum_eq_zero
    intro d _hd
    exact χ.evalNat_im d

/-- The normalized integral of one L-series coefficient is precisely the
corresponding summand in Zhang's full smoothed sum. -/
theorem lemma57MellinSeriesTerm_normalized_integral
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t : ℝ, lemma57MellinSeriesTerm χ n t =
      (lemma57FullSmoothedTerm χ (zhangGaussianWeight D) n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    have hzero : lemma57MellinSeriesTerm χ 0 = 0 := by
      funext t
      simp [lemma57MellinSeriesTerm]
    rw [hzero]
    simp [lemma57FullSmoothedTerm]
  have hpoint := lemma57MellinSeriesTerm_eq_kernel χ hD hn
  simp_rw [hpoint, MeasureTheory.integral_const_mul]
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ *
          ((divisorCharacterSum χ n / (n : ℂ)) *
            ∫ t : ℝ, lemma57GaussianKernelIntegrand D 1
              (lemma57WeightArgument D n) t * I) =
        (divisorCharacterSum χ n / (n : ℂ)) *
          lemma57GaussianKernelVerticalIntegral D 1
            (lemma57WeightArgument D n) := by
              rw [lemma57GaussianKernelVerticalIntegral]
              ring
    _ = _ := by
      have harg : 0 < lemma57WeightArgument D n := by
        unfold lemma57WeightArgument
        have hDp : (0 : ℝ) < D := by
          exact_mod_cast Nat.zero_lt_of_lt hD
        have hnp : (0 : ℝ) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      rw [lemma57GaussianKernelVerticalIntegral_eq_weight hD zero_lt_one harg]
      rw [lemma57FullSmoothedTerm, if_neg hn, lemma57SmoothedTerm]
      unfold lemma57WeightArgument
      rw [← divisorCharacterSumReal_coe χ n]
      push_cast
      ring

/-- Zhang's exact Mellin identity, including honest vertical integrability and
the series/integral interchange, is unconditional for every `D > 1`. -/
theorem lemma57MellinIdentity_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57MellinIdentity χ := by
  constructor
  · unfold Lemma57VerticalIntegrable
    apply (lemma57MellinSeriesTerm_tsum_integrable χ hD).congr
    filter_upwards [] with t
    exact lemma57MellinSeriesTerm_tsum χ t
  · unfold lemma57VerticalIntegral
    have hinterchange := MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n : ℕ => lemma57MellinSeriesTerm_integrable χ hD n)
      (lemma57MellinSeriesTerm_integral_norm_summable χ hD)
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∫ t : ℝ, lemma57MellinIntegrand χ
            ((1 : ℂ) + (t : ℂ) * I) * I =
          (2 * (Real.pi : ℂ) * I)⁻¹ *
            ∫ t : ℝ, ∑' n : ℕ, lemma57MellinSeriesTerm χ n t := by
              congr 1
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with t
              exact (lemma57MellinSeriesTerm_tsum χ t).symm
      _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∑' n : ℕ, ∫ t : ℝ, lemma57MellinSeriesTerm χ n t := by
            rw [hinterchange]
      _ = ∑' n : ℕ, (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∫ t : ℝ, lemma57MellinSeriesTerm χ n t := by
            rw [tsum_mul_left]
      _ = ∑' n : ℕ,
          (lemma57FullSmoothedTerm χ (zhangGaussianWeight D) n : ℂ) := by
            apply tsum_congr
            intro n
            exact lemma57MellinSeriesTerm_normalized_integral χ hD n
      _ = (lemma57FullSmoothedSum χ (zhangGaussianWeight D) : ℂ) := by
        unfold lemma57FullSmoothedSum
        simpa using (Complex.ofRealCLM.map_tsum
          (lemma57FullSmoothedSummable_proved χ hD)).symm

end ZhangLS.Spec
