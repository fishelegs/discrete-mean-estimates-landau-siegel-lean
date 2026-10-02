import ZhangLS.Spec.DivisorCharacterSumNonnegative

/-!
# The full smoothed Dirichlet series in Zhang's Lemma 5.7

The finite segment isolated in Steps 16--17 is only the arithmetic core of Zhang's
Mellin identity.  The actual right-hand side is the infinite series

  ∑_{m ≥ 1} νχ(m) / m * g(D^4 / m).

This file introduces that full series without hiding convergence inside a definition.
We extend the positive-integer summand by zero at `n = 0`.  This keeps the paper's natural indexing while allowing `Finset.Icc 1 D` to be used directly as a finite subset of the full series.

The results here deliberately separate the two genuinely analytic statements still
needed before the Mellin identity can be used:

* global nonnegativity of Zhang's Gaussian weight on positive arguments;
* summability of the smoothed coefficient sequence.

Once these are available, the full series automatically dominates the already-proved
finite `1/8 · D/φ(D)` arithmetic contribution.
-/

namespace ZhangLS.Spec

open scoped BigOperators

/-- The full-series summand, extended by zero at `n = 0`. -/
noncomputable def lemma57FullSmoothedTerm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else lemma57SmoothedTerm χ g n

/-- Zhang's full positive-integer smoothed arithmetic series. -/
noncomputable def lemma57FullSmoothedSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, lemma57FullSmoothedTerm χ g n

/-- The honest convergence obligation for the full smoothed series. -/
def Lemma57FullSmoothedSummable {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) : Prop :=
  Summable (lemma57FullSmoothedTerm χ g)

/-- The global sign property required to compare a finite initial segment with the
full series.  For Zhang's Gaussian this should follow from its cumulative-Gaussian
interpretation. -/
def ZhangGaussianWeightNonnegative (D : ℕ) : Prop :=
  ∀ {x : ℝ}, 0 < x → 0 ≤ zhangGaussianWeight D x

/-- The coefficient factor in every positive-index summand is nonnegative. -/
theorem lemma57CoefficientFactor_nonneg
    {D n : ℕ} (χ : RealPrimitiveCharacter D) (hn : n ≠ 0) :
    0 ≤ divisorCharacterSumReal χ n * ((n : ℝ)⁻¹) := by
  have hnu : 0 ≤ divisorCharacterSumReal χ n :=
    divisorCharacterSumReal_nonneg χ n
  have hinv : 0 ≤ ((n : ℝ)⁻¹) := by positivity
  exact mul_nonneg hnu hinv

/-- If Zhang's Gaussian is globally nonnegative on positive arguments, then every
summand of the full series is nonnegative. -/
theorem lemma57FullSmoothedTerm_nonneg
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D) (hweight : ZhangGaussianWeightNonnegative D) (n : ℕ) :
    0 ≤ lemma57FullSmoothedTerm χ (zhangGaussianWeight D) n := by
  by_cases hn : n = 0
  · simp [lemma57FullSmoothedTerm, hn]
  · rw [lemma57FullSmoothedTerm, if_neg hn]
    unfold lemma57SmoothedTerm
    have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have harg : 0 < lemma57WeightArgument D n := by
      unfold lemma57WeightArgument
      have hD4pos : (0 : ℝ) < (D : ℝ) ^ 4 := pow_pos hDpos _
      positivity
    have hw : 0 ≤ zhangGaussianWeight D (lemma57WeightArgument D n) :=
      hweight harg
    have hc := lemma57CoefficientFactor_nonneg χ hn
    exact mul_nonneg hc hw

/-- On the initial segment, the full-series summand agrees with the Step-17 finite
summand. -/
theorem lemma57FullSmoothedTerm_eq_initial
    {D n : ℕ} (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ)
    (hn : n ∈ Finset.Icc 1 D) :
    lemma57FullSmoothedTerm χ g n = lemma57SmoothedTerm χ g n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1)
  simp [lemma57FullSmoothedTerm, hn0]

/-- A summable nonnegative full series dominates its finite initial segment. -/
theorem lemma57InitialSmoothedSum_le_fullSmoothedSum
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 0 < D)
    (hsum : Lemma57FullSmoothedSummable χ (zhangGaussianWeight D))
    (hweight : ZhangGaussianWeightNonnegative D) :
    lemma57InitialSmoothedSum χ (zhangGaussianWeight D) ≤
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) := by
  unfold lemma57InitialSmoothedSum lemma57FullSmoothedSum
  calc
    (∑ n ∈ Finset.Icc 1 D,
        lemma57SmoothedTerm χ (zhangGaussianWeight D) n)
        = ∑ n ∈ Finset.Icc 1 D,
            lemma57FullSmoothedTerm χ (zhangGaussianWeight D) n := by
              apply Finset.sum_congr rfl
              intro n hn
              exact (lemma57FullSmoothedTerm_eq_initial χ (zhangGaussianWeight D) hn).symm
    _ ≤ ∑' n : ℕ, lemma57FullSmoothedTerm χ (zhangGaussianWeight D) n := by
      exact hsum.sum_le_tsum (Finset.Icc 1 D)
        (fun n _ => lemma57FullSmoothedTerm_nonneg χ hD hweight n)

/-- Therefore convergence plus global positivity upgrades the unconditional finite
arithmetic lower bound from Step 17 to Zhang's full smoothed sum. -/
theorem lemma57_full_gaussian_arithmetic_scale
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hsum : Lemma57FullSmoothedSummable χ (zhangGaussianWeight D))
    (hweight : ZhangGaussianWeightNonnegative D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57FullSmoothedSum χ (zhangGaussianWeight D) := by
  exact le_trans (lemma57_initial_gaussian_arithmetic_scale_proved χ hD)
    (lemma57InitialSmoothedSum_le_fullSmoothedSum χ (Nat.zero_lt_of_lt hD) hsum hweight)

/-- Package the full series as the arithmetic lower-bound structure used by the
contour-transfer theorem, once the two analytic series facts have been supplied. -/
noncomputable def lemma57FullArithmeticLowerBound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hsum : Lemma57FullSmoothedSummable χ (zhangGaussianWeight D))
    (hweight : ZhangGaussianWeightNonnegative D) :
    Lemma57ArithmeticLowerBound D where
  constant := (1 : ℝ) / 8
  mainSum := lemma57FullSmoothedSum χ (zhangGaussianWeight D)
  constant_pos := by norm_num
  lower_bound := lemma57_full_gaussian_arithmetic_scale χ hD hsum hweight

end ZhangLS.Spec
