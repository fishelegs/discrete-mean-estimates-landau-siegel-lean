import ZhangLS.Spec.Lemma57LAtOnePositivity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# A numerical error budget for the residue correction

Under Zhang's small-value hypothesis, the now-proved positivity of `L(1,χ)`
turns the residue correction into a genuinely small term. For `log D ≥ 2`,
elementary power estimates put it below `1/32` of the arithmetic scale.
Thus the remaining shifted integral gets the other `1/32` of the `1/16`
analytic-error budget.
-/

namespace ZhangLS.Spec

open Complex
open scoped Real

/-- The natural arithmetic scale `D/φ(D)` is at least one. -/
theorem lemma57Scale_ge_one {D : ℕ} (hD : 1 < D) :
    1 ≤ lemma57Scale D := by
  unfold lemma57Scale
  have hphiNat : 0 < Nat.totient D :=
    Nat.totient_pos.mpr (Nat.zero_lt_of_lt hD)
  have hphi : (0 : ℝ) < Nat.totient D := by exact_mod_cast hphiNat
  have hle : (Nat.totient D : ℝ) ≤ D := by
    exact_mod_cast Nat.totient_le D
  exact (le_div_iff₀ hphi).2 (by simpa using hle)

/-- The explicit logarithmic threshold used below holds for all sufficiently
large natural moduli. -/
theorem exists_modulus_threshold_log_ge_two :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 2 ≤ Real.log (D : ℝ) := by
  have hlim : Filter.Tendsto (fun D : ℕ => Real.log (D : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.1 (hlim.eventually_ge_atTop 2)

/-- Once `log D ≥ 2`, Assumption (A) makes the absolute residue correction
at most `1/32`, an explicit numerical bound independent of `D`. -/
theorem lemma57ResidueCorrection_abs_le_one_thirtysecond
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hlog : 2 ≤ Real.log (D : ℝ))
    (hA : NormalizedAssumptionA χ) :
    |lemma57ResidueCorrection χ| ≤ (1 : ℝ) / 32 := by
  let L : ℝ := Real.log (D : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hgamma : |Real.eulerMascheroniConstant + 4 * L| ≤ 5 * L := by
    have hγ0 : 0 < Real.eulerMascheroniConstant := by
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    rw [abs_of_nonneg (by positivity)]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hpow : L ^ (-2022 : ℤ) ≤ L ^ (-9 : ℤ) :=
    zpow_le_zpow_right₀ hLone (by norm_num)
  have hpow8 : (256 : ℝ) ≤ L ^ 8 := by
    calc
      (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
      _ ≤ L ^ 8 := by gcongr
  have hpow9 : (256 : ℝ) * L ≤ L ^ 9 := by
    nlinarith [hpow8]
  have hfive : (5 : ℝ) * L / L ^ 9 ≤ 5 / 256 := by
    apply (div_le_iff₀ (pow_pos hL 9)).2
    nlinarith [hpow9]
  calc
    |lemma57ResidueCorrection χ| ≤
        |Real.eulerMascheroniConstant + 4 * L| * L ^ (-2022 : ℤ) := by
      simpa [L] using
        lemma57ResidueCorrection_abs_le_of_assumptionA χ hD hA
    _ ≤ 5 * L * L ^ (-9 : ℤ) := by
      have hnonneg : 0 ≤ L ^ (-2022 : ℤ) := zpow_nonneg hL.le _
      exact (mul_le_mul_of_nonneg_right hgamma hnonneg).trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = 5 * L / L ^ 9 := by
      simp [zpow_neg, div_eq_mul_inv, hL.ne']
      rfl
    _ ≤ 5 / 256 := hfive
    _ ≤ (1 : ℝ) / 32 := by norm_num

/-- The residue uses no more than half of the `1/16` analytic-error budget. -/
theorem lemma57ResidueCorrection_abs_le_scale_thirtysecond
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hlog : 2 ≤ Real.log (D : ℝ))
    (hA : NormalizedAssumptionA χ) :
    |lemma57ResidueCorrection χ| ≤ (1 : ℝ) / 32 * lemma57Scale D := by
  have hres := lemma57ResidueCorrection_abs_le_one_thirtysecond χ hD hlog hA
  have hscale := lemma57Scale_ge_one hD
  linarith

/-- It now suffices to spend the remaining `1/32` on the actual shifted
integral. The residue estimate is no longer an assumption. -/
theorem lemma57GaussianAnalyticErrorBound_of_shifted_norm
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hlog : 2 ≤ Real.log (D : ℝ))
    (hA : NormalizedAssumptionA χ)
    (hleft : ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
      (1 : ℝ) / 32 * lemma57Scale D) :
    Lemma57GaussianAnalyticErrorBound χ := by
  unfold Lemma57GaussianAnalyticErrorBound lemma57AnalyticError
  have hres := lemma57ResidueCorrection_abs_le_scale_thirtysecond χ hD hlog hA
  have hre := Complex.abs_re_le_norm
    (lemma57VerticalIntegral χ (-(1 : ℝ) / 2))
  linarith

/-- An explicit sufficient bound on Step 46's Gaussian-weighted envelope is
the sole remaining analytic inequality for the `1/16` error target. -/
theorem lemma57GaussianAnalyticErrorBound_of_envelope
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hlog : 2 ≤ Real.log (D : ℝ))
    (hA : NormalizedAssumptionA χ)
    (henvelope :
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (Real.exp (-2 * Real.log (D : ℝ) +
            1 / (16 * Real.log (D : ℝ) ^ 30)) *
            lemma57LeftGaussianEnvelope χ) ≤
        (1 : ℝ) / 32 * lemma57Scale D) :
    Lemma57GaussianAnalyticErrorBound χ := by
  apply lemma57GaussianAnalyticErrorBound_of_shifted_norm χ hD hlog hA
  exact (lemma57LeftVerticalIntegral_norm_le_envelope χ hD).trans henvelope

end ZhangLS.Spec
