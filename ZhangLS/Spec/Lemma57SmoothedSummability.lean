import ZhangLS.Spec.Lemma57GaussianGlobal
import Mathlib.Analysis.PSeries

/-!
# Reduction of Lemma 5.7 smoothed-series summability to Gaussian tail decay

The arithmetic coefficient satisfies the elementary bound `0 ≤ νχ(n) ≤ n`.
Consequently the factor `νχ(n) / n` is at most one for positive `n`.  Thus the
full smoothed series is summable as soon as Zhang's Gaussian weight along
`D^4 / n` has any summable polynomial majorant.  We record the concrete cubic
majorant needed here; its proof is the remaining pure Gaussian-tail estimate.
-/

namespace ZhangLS.Spec

open scoped BigOperators

/-- The divisor-character coefficient is bounded by the number of divisors. -/
theorem divisorCharacterSumReal_le_card_divisors
    {D : ℕ} (χ : RealPrimitiveCharacter D) {n : ℕ} (hn : n ≠ 0) :
    divisorCharacterSumReal χ n ≤ (Nat.divisors n).card := by
  unfold divisorCharacterSumReal divisorCharacterSum
  rw [Complex.re_sum]
  calc
    (∑ d ∈ Nat.divisors n, (χ.evalNat d).re)
        ≤ ∑ _d ∈ Nat.divisors n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          calc
            (χ.evalNat d).re ≤ ‖χ.evalNat d‖ := Complex.re_le_norm _
            _ ≤ 1 := by
              unfold RealPrimitiveCharacter.evalNat
              exact χ.chi.norm_le_one (d : ZMod D)
    _ = (Nat.divisors n).card := by simp

/-- A very coarse but sufficient coefficient bound: `νχ(n) ≤ n`. -/
theorem divisorCharacterSumReal_le_nat
    {D : ℕ} (χ : RealPrimitiveCharacter D) {n : ℕ} (hn : n ≠ 0) :
    divisorCharacterSumReal χ n ≤ (n : ℝ) := by
  calc
    divisorCharacterSumReal χ n ≤ (Nat.divisors n).card :=
      divisorCharacterSumReal_le_card_divisors χ hn
    _ ≤ (n : ℝ) := by exact_mod_cast Nat.card_divisors_le_self n

/-- Hence the positive coefficient factor `νχ(n)/n` is at most one. -/
theorem lemma57CoefficientFactor_le_one
    {D n : ℕ} (χ : RealPrimitiveCharacter D) (hn : n ≠ 0) :
    divisorCharacterSumReal χ n * ((n : ℝ)⁻¹) ≤ 1 := by
  have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hnr : (n : ℝ) ≠ 0 := hnpos.ne'
  have hnu := divisorCharacterSumReal_le_nat χ hn
  calc
    divisorCharacterSumReal χ n * ((n : ℝ)⁻¹)
        ≤ (n : ℝ) * ((n : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hnu (inv_nonneg.mpr hnpos.le)
    _ = 1 := mul_inv_cancel₀ hnr

/-- The one remaining Gaussian-tail statement.  It asks only for an eventual
cubic majorant along the exact sequence sampled by Lemma 5.7. -/
def ZhangGaussianCubicDecay (D : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      zhangGaussianWeight D (lemma57WeightArgument D n) ≤
        C * (n : ℝ) ^ (-3 : ℝ)


/-- The Zhang Gaussian weight has the concrete cubic decay required by the
smoothed-series comparison test.  The choice
`K = 3 / (log D)^15` turns the Gaussian exponential tail into a fixed
`D`-dependent constant times `n⁻³`. -/
theorem zhangGaussianCubicDecay_proved
    {D : ℕ} (hD : 1 < D) : ZhangGaussianCubicDecay D := by
  let c : ℝ := (Real.log (D : ℝ)) ^ 15
  let K : ℝ := 3 / c
  let C : ℝ := (Real.sqrt Real.pi)⁻¹ * (Real.exp (12 * Real.log (D : ℝ)) / K)
  have hDposNat : 0 < D := Nat.zero_lt_of_lt hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
  have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
  have hlogD : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD)
  have hc : 0 < c := by
    dsimp [c]
    exact pow_pos hlogD _
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by norm_num) hc
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have htail := zhangGaussianWeight_eventually_le_exp_tail hD hK
  filter_upwards [htail, Filter.eventually_gt_atTop 0] with n hweight hn
  have hnposNat : 0 < n := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hD4ne : ((D : ℝ) ^ 4) ≠ 0 := pow_ne_zero _ hDne
  have hendpoint := neg_zhangGaussianEndpoint_weightArgument_eq hDposNat hnposNat
  have hexp :
      Real.exp
          (-K * (-zhangGaussianEndpoint D (lemma57WeightArgument D n))) =
        Real.exp (12 * Real.log (D : ℝ)) * (n : ℝ) ^ (-3 : ℝ) := by
    rw [hendpoint]
    dsimp [K, c]
    rw [Real.log_div hnne hD4ne, Real.log_pow]
    rw [Real.rpow_def_of_pos hnpos]
    rw [← Real.exp_add]
    congr 1
    field_simp [show (Real.log (D : ℝ)) ^ 15 ≠ 0 by exact hc.ne']
    ring
  calc
    zhangGaussianWeight D (lemma57WeightArgument D n)
        ≤ (Real.sqrt Real.pi)⁻¹ *
            (Real.exp
              (-K * (-zhangGaussianEndpoint D (lemma57WeightArgument D n))) / K) :=
      hweight
    _ = (Real.sqrt Real.pi)⁻¹ *
          ((Real.exp (12 * Real.log (D : ℝ)) * (n : ℝ) ^ (-3 : ℝ)) / K) := by
      rw [hexp]
    _ = C * (n : ℝ) ^ (-3 : ℝ) := by
      dsimp [C]
      ring

/-- Cubic decay of the Gaussian weight implies summability of the complete
smoothed series. -/
theorem lemma57FullSmoothedSummable_of_cubicDecay
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hdecay : ZhangGaussianCubicDecay D) :
    Lemma57FullSmoothedSummable χ (zhangGaussianWeight D) := by
  rcases hdecay with ⟨C, hC, htail⟩
  unfold Lemma57FullSmoothedSummable
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => C * (n : ℝ) ^ (-3 : ℝ))
  · exact (Real.summable_nat_rpow.mpr (by norm_num : (-3 : ℝ) < -1)).mul_left C
  · filter_upwards [htail, Filter.eventually_gt_atTop 0] with n hweight hn0
    have hn : n ≠ 0 := Nat.ne_of_gt hn0
    have hterm_nonneg := lemma57FullSmoothedTerm_nonneg χ
      (Nat.zero_lt_of_lt hD) (zhangGaussianWeightNonnegative_proved hD) n
    rw [Real.norm_of_nonneg hterm_nonneg]
    rw [lemma57FullSmoothedTerm, if_neg hn]
    unfold lemma57SmoothedTerm
    have hcoef1 := lemma57CoefficientFactor_le_one χ hn
    have hw0 := zhangGaussianWeight_nonneg hD
      (x := lemma57WeightArgument D n) (by
      unfold lemma57WeightArgument
      have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
      have hnp : (0 : ℝ) < n := by exact_mod_cast hn0
      positivity)
    calc
      divisorCharacterSumReal χ n * (n : ℝ)⁻¹ *
          zhangGaussianWeight D (lemma57WeightArgument D n)
          ≤ 1 * zhangGaussianWeight D (lemma57WeightArgument D n) := by
            exact mul_le_mul_of_nonneg_right hcoef1 hw0
      _ = zhangGaussianWeight D (lemma57WeightArgument D n) := one_mul _
      _ ≤ C * (n : ℝ) ^ (-3 : ℝ) := hweight


/-- The complete Zhang smoothed series is now summable from the proved Gaussian
cubic tail. -/
theorem lemma57FullSmoothedSummable_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57FullSmoothedSummable χ (zhangGaussianWeight D) := by
  exact lemma57FullSmoothedSummable_of_cubicDecay χ hD
    (zhangGaussianCubicDecay_proved hD)

/-- Once the pure Gaussian cubic-decay estimate is supplied, the full arithmetic
lower bound becomes unconditional. -/
theorem lemma57_full_gaussian_arithmetic_scale_of_cubicDecay
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hdecay : ZhangGaussianCubicDecay D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) := by
  exact lemma57_full_gaussian_arithmetic_scale_of_summable χ hD
    (lemma57FullSmoothedSummable_of_cubicDecay χ hD hdecay)


/-- With cubic decay discharged, the full Gaussian arithmetic lower bound no
longer carries a summability hypothesis. -/
theorem lemma57_full_gaussian_arithmetic_scale_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) := by
  exact lemma57_full_gaussian_arithmetic_scale_of_cubicDecay χ hD
    (zhangGaussianCubicDecay_proved hD)

end ZhangLS.Spec
