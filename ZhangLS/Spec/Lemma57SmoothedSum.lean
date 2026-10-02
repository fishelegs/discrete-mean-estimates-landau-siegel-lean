import ZhangLS.Spec.Lemma57GaussianWeight

/-!
# The finite smoothed sum in Zhang's Lemma 5.7

The paper's Mellin identity contains

  ∑ n, νχ(n) / n * g(D^4 / n).

Before formalizing the infinite sum and contour identity, it is useful to isolate the
finite initial segment `1 ≤ n ≤ D`.  This segment already contains every divisor of
`D`, and every Gaussian argument `D^4 / n` in it is at least `1`.

Consequently, once the standard arithmetic fact `νχ(n) ≥ 0` is available, the whole
initial segment dominates the divisor subsum formalized in `Lemma57Arithmetic`, and
therefore inherits the explicit `1/8 * D/φ(D)` lower bound from Step 15.
-/

namespace ZhangLS.Spec

open scoped BigOperators Interval

/-- One summand in Zhang's smoothed arithmetic sum. -/
noncomputable def lemma57SmoothedTerm {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  divisorCharacterSumReal χ n * (n : ℝ)⁻¹ * g (lemma57WeightArgument D n)

/-- The initial segment `1 ≤ n ≤ D` of Zhang's smoothed sum.  This is finite and
already contains the divisor contribution responsible for the main lower bound. -/
noncomputable def lemma57InitialSmoothedSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 D, lemma57SmoothedTerm χ g n

/-- The remaining arithmetic sign statement needed to pass from the divisor subsum
to a larger smoothed sum.  This is the genuine assertion `νχ(n) ≥ 0`, not a lower
bound on the final main sum. -/
def DivisorCharacterSumNonnegative {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Prop :=
  ∀ n : ℕ, 0 ≤ divisorCharacterSumReal χ n

/-- Every divisor of a positive `D` lies in the initial segment `[1,D]`. -/
theorem divisors_subset_Icc_one_self {D : ℕ} (hD : 0 < D) :
    Nat.divisors D ⊆ Finset.Icc 1 D := by
  intro n hn
  rw [Finset.mem_Icc]
  constructor
  · exact Nat.succ_le_iff.mpr (Nat.pos_of_mem_divisors hn)
  · exact Nat.divisor_le hn

/-- The weight argument is at least one on the whole initial segment, not merely on
divisors. -/
theorem one_le_lemma57WeightArgument_of_mem_Icc
    {D n : ℕ} (hD : 1 < D) (hn : n ∈ Finset.Icc 1 D) :
    (1 : ℝ) ≤ lemma57WeightArgument D n := by
  have hn_bounds := Finset.mem_Icc.mp hn
  have hnposNat : 0 < n := Nat.zero_lt_of_lt hn_bounds.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hnle : (n : ℝ) ≤ (D : ℝ) := by exact_mod_cast hn_bounds.2
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast (Nat.le_of_lt hD)
  have hcube : (1 : ℝ) ≤ (D : ℝ) ^ 3 := one_le_pow₀ hDone
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  have hnle4 : (n : ℝ) ≤ (D : ℝ) ^ 4 := by
    calc
      (n : ℝ) ≤ (D : ℝ) := hnle
      _ = (D : ℝ) * 1 := by ring
      _ ≤ (D : ℝ) * ((D : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hcube hDnonneg
      _ = (D : ℝ) ^ 4 := by ring
  unfold lemma57WeightArgument
  exact (le_div_iff₀ hnpos).2 (by simpa using hnle4)

/-- On `1 ≤ n ≤ D`, every Gaussian weight occurring in the smoothed sum is at
least `1/2`. -/
theorem zhangGaussianWeight_half_le_on_initial_segment
    {D n : ℕ} (hD : 1 < D) (hn : n ∈ Finset.Icc 1 D) :
    (1 : ℝ) / 2 ≤
      zhangGaussianWeight D (lemma57WeightArgument D n) := by
  exact zhangGaussianWeight_half_le hD
    (one_le_lemma57WeightArgument_of_mem_Icc hD hn)

/-- If `νχ(n)` is nonnegative, every summand in the initial Gaussian-smoothed segment
is nonnegative. -/
theorem lemma57SmoothedTerm_nonneg_on_initial_segment
    {D n : ℕ} (χ : RealPrimitiveCharacter D)
    (hnu : DivisorCharacterSumNonnegative χ)
    (hD : 1 < D) (hn : n ∈ Finset.Icc 1 D) :
    0 ≤ lemma57SmoothedTerm χ (zhangGaussianWeight D) n := by
  unfold lemma57SmoothedTerm
  have hcoeff : 0 ≤ divisorCharacterSumReal χ n := hnu n
  have hinv : 0 ≤ ((n : ℝ)⁻¹) := by positivity
  have hweight : 0 ≤ zhangGaussianWeight D (lemma57WeightArgument D n) := by
    have hhalf := zhangGaussianWeight_half_le_on_initial_segment hD hn
    linarith
  exact mul_nonneg (mul_nonneg hcoeff hinv) hweight

/-- The finite initial segment dominates the divisor subsum.  The only arithmetic
input not already proved in Steps 09--15 is the standard sign property `νχ(n) ≥ 0`. -/
theorem lemma57DivisorSubsum_le_initialSmoothedSum
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hnu : DivisorCharacterSumNonnegative χ) (hD : 1 < D) :
    lemma57DivisorSubsum χ (zhangGaussianWeight D) ≤
      lemma57InitialSmoothedSum χ (zhangGaussianWeight D) := by
  unfold lemma57DivisorSubsum lemma57InitialSmoothedSum lemma57SmoothedTerm
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact divisors_subset_Icc_one_self (Nat.zero_lt_of_lt hD)
  · intro n hnIcc hnNotDiv
    have hterm := lemma57SmoothedTerm_nonneg_on_initial_segment χ hnu hD hnIcc
    simpa [lemma57SmoothedTerm] using hterm

/-- Therefore the initial Gaussian-smoothed sum already has the explicit arithmetic
scale `1/8 * D/φ(D)`. -/
theorem lemma57_initial_gaussian_arithmetic_scale
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hnu : DivisorCharacterSumNonnegative χ) (hD : 1 < D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57InitialSmoothedSum χ (zhangGaussianWeight D) := by
  exact le_trans (lemma57_gaussian_divisor_arithmetic_scale χ hD)
    (lemma57DivisorSubsum_le_initialSmoothedSum χ hnu hD)

/-- Package the initial smoothed sum directly as the arithmetic input structure used
by the Step-08 contour transfer. -/
noncomputable def lemma57InitialArithmeticLowerBound
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hnu : DivisorCharacterSumNonnegative χ) (hD : 1 < D) :
    Lemma57ArithmeticLowerBound D where
  constant := (1 : ℝ) / 8
  mainSum := lemma57InitialSmoothedSum χ (zhangGaussianWeight D)
  constant_pos := by norm_num
  lower_bound := lemma57_initial_gaussian_arithmetic_scale χ hnu hD

end ZhangLS.Spec
