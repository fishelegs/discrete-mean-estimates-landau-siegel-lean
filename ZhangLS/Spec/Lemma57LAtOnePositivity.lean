import ZhangLS.Spec.Lemma57ShiftedIntegralEnvelope
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Positivity of the real Dirichlet L-value at one

The Dirichlet L-series tends to `1` as its real argument tends to infinity.
The nontrivial character's continued L-function has no zero on `re s ≥ 1`.
Since our real character has a real L-value on the real half-line, continuity
and the intermediate value theorem force that value to be positive everywhere
on `x ≥ 1`, including the endpoint. This makes Assumption (A) usable for the
absolute value of Zhang's residue correction.
-/

namespace ZhangLS.Spec

open Filter Complex Set
open scoped Topology

/-- The L-value of a nontrivial primitive real character is positive on the
closed real half-line beginning at one. -/
theorem realLValue_pos_of_one_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) : 0 < realLValue χ x := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hdiff : Differentiable ℂ (dirichletLFunction χ) :=
    differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hcont : Continuous (realLValue χ) := by
    exact Complex.continuous_re.comp (hdiff.continuous.comp Complex.continuous_ofReal)
  have hseries : Tendsto
      (fun y : ℝ => LSeries (fun n : ℕ => χ.chi (n : ZMod D)) (y : ℂ))
      atTop (nhds (1 : ℂ)) := by
    have habs : LSeries.abscissaOfAbsConv
        (fun n : ℕ => χ.chi (n : ZMod D)) < ⊤ := by
      rw [DirichletCharacter.absicssaOfAbsConv_eq_one χ.modulus_ne_zero χ.chi]
      exact EReal.coe_lt_top 1
    simpa using LSeries.tendsto_atTop habs
  have heq :
      (fun y : ℝ => dirichletLFunction χ (y : ℂ)) =ᶠ[atTop]
        (fun y : ℝ => LSeries (fun n : ℕ => χ.chi (n : ZMod D)) (y : ℂ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    simpa [dirichletLSeries, dirichletCoeffs] using
      (dirichletLFunction_eq_series χ (by simpa using hy))
  have hlimC : Tendsto (fun y : ℝ => dirichletLFunction χ (y : ℂ))
      atTop (nhds (1 : ℂ)) := hseries.congr' heq.symm
  have hlim : Tendsto (realLValue χ) atTop (nhds (1 : ℝ)) := by
    exact (Complex.continuous_re.tendsto (1 : ℂ)).comp hlimC
  have hpos : ∀ᶠ y : ℝ in atTop, 0 < realLValue χ y :=
    hlim.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨y, hxy, hypos⟩ := ((eventually_ge_atTop x).and hpos).exists
  have hne (z : ℝ) (hz : 1 ≤ z) : realLValue χ z ≠ 0 := by
    have hχ : χ.chi ≠ 1 := χ.nontrivial_of_one_lt_modulus hD
    have hLne : dirichletLFunction χ (z : ℂ) ≠ 0 := by
      have hz' : 1 ≤ (z : ℂ).re := by simpa using hz
      simpa [dirichletLFunction] using
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.chi (.inl hχ) hz')
    have him : (dirichletLFunction χ (z : ℂ)).im = 0 := by
      rcases hz.eq_or_lt with heq | hlt
      · subst z
        exact dirichletLFunction_im_eq_zero_at_one χ hD
      · exact dirichletLFunction_im_eq_zero_of_one_lt χ hlt
    intro hz0
    apply hLne
    apply Complex.ext
    · simpa [realLValue] using hz0
    · simpa using him
  by_contra hnpos
  have hxnonpos : realLValue χ x ≤ 0 := le_of_not_gt hnpos
  have hinterval : (0 : ℝ) ∈ Icc (realLValue χ x) (realLValue χ y) :=
    ⟨hxnonpos, hypos.le⟩
  obtain ⟨z, hz, hz0⟩ :=
    (intermediate_value_Icc hxy hcont.continuousOn) hinterval
  exact hne z (hx.trans hz.1) hz0

/-- In particular, the paper's real value at one is strictly positive. -/
theorem realLAtOne_pos {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    0 < realLAtOne χ := by
  exact realLValue_pos_of_one_le χ hD (le_refl 1)

/-- Assumption (A) now bounds the absolute residue correction, without an
extra positivity hypothesis on `L(1,χ)`. -/
theorem lemma57ResidueCorrection_abs_le_of_assumptionA
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hA : NormalizedAssumptionA χ) :
    |lemma57ResidueCorrection χ| ≤
      |Real.eulerMascheroniConstant + 4 * Real.log (D : ℝ)| *
        (Real.log (D : ℝ)) ^ (-2022 : ℤ) := by
  have hpos := realLAtOne_pos χ hD
  have hsmall : realLAtOne χ <
      (Real.log (D : ℝ)) ^ (-2022 : ℤ) := by
    simpa [NormalizedAssumptionA, AssumptionAWithConstant] using hA
  rw [lemma57ResidueCorrection, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left hsmall.le (abs_nonneg _)

/-- Under Assumption (A), only the actual shifted integral remains to be
quantitatively controlled for the analytic error budget. -/
theorem lemma57AnalyticError_le_shifted_norm_of_assumptionA
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hA : NormalizedAssumptionA χ) :
    lemma57AnalyticError χ ≤
      |Real.eulerMascheroniConstant + 4 * Real.log (D : ℝ)| *
          (Real.log (D : ℝ)) ^ (-2022 : ℤ) +
        ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ := by
  unfold lemma57AnalyticError
  exact add_le_add
    (lemma57ResidueCorrection_abs_le_of_assumptionA χ hD hA)
    (Complex.abs_re_le_norm _)

/-- Combining positivity with the unconditional Gaussian envelope leaves a
single weighted zeta/L integral to estimate in the analytic error. -/
theorem lemma57AnalyticError_le_envelope_of_assumptionA
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hA : NormalizedAssumptionA χ) :
    lemma57AnalyticError χ ≤
      |Real.eulerMascheroniConstant + 4 * Real.log (D : ℝ)| *
          (Real.log (D : ℝ)) ^ (-2022 : ℤ) +
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (Real.exp (-2 * Real.log (D : ℝ) +
            1 / (16 * Real.log (D : ℝ) ^ 30)) *
            lemma57LeftGaussianEnvelope χ) := by
  exact (lemma57AnalyticError_le_shifted_norm_of_assumptionA χ hD hA).trans
    (add_le_add_right (lemma57LeftVerticalIntegral_norm_le_envelope χ hD) _)

end ZhangLS.Spec
