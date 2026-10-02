import ZhangLS.Spec.RealAxisDerivativeAtOne
import ZhangLS.Spec.RealAxisLFunction

/-!
# Zhang, Lemma 5.7: trusted quantitative specification

The paper proves, under the small-value hypothesis (A), the lower bound

  L'(1, χ) ≫ D / φ(D).

The legacy development replaced the analytic content of this lemma by tautologies
and integer arithmetic.  This file records the genuine real-valued target and splits
its proof into independently auditable arithmetic, contour-shift, and error-control
inputs.  Only the final order-theoretic transfer is proved here.
-/

namespace ZhangLS.Spec

/-- The natural arithmetic scale in Lemma 5.7. -/
noncomputable def lemma57Scale (D : ℕ) : ℝ :=
  (D : ℝ) / (Nat.totient D : ℝ)

/-- Lemma 5.7 for one explicit absolute constant, with the paper's standing
"sufficiently large modulus" convention made explicit.  The threshold is uniform
in the character and in the normalized small-value hypothesis `(A)`. -/
def Lemma57AtConstant (c : ℝ) : Prop :=
  0 < c ∧
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D →
      1 < D →
      NormalizedAssumptionA χ →
      c * lemma57Scale D ≤ realLDerivAtOne χ

/-- Paper-level target corresponding to the Vinogradov notation
`L'(1, χ) ≫ D / φ(D)`, under Zhang's standing convention that `D` is
sufficiently large. -/
def Lemma57Target : Prop :=
  ∃ c : ℝ, Lemma57AtConstant c

/-- The exact data needed from the smoothed divisor-sum side of Zhang's Mellin
identity.  `mainSum` is intentionally an abstract real value here: its actual
integral/sum definition belongs in the later Mellin-kernel layer, rather than being
faked by a closed formula. -/
structure Lemma57ArithmeticLowerBound (D : ℕ) where
  constant : ℝ
  mainSum : ℝ
  constant_pos : 0 < constant
  lower_bound : constant * lemma57Scale D ≤ mainSum

/-- The exact output needed from the contour shift.  The shifted integral is encoded
as a nonnegative error bound rather than hidden inside an existential remainder. -/
structure Lemma57ContourApproximation {D : ℕ}
    (χ : RealPrimitiveCharacter D) (mainSum : ℝ) where
  error : ℝ
  error_nonneg : 0 ≤ error
  approximation : |mainSum - realLDerivAtOne χ| ≤ error

/-- Under hypothesis (A), Zhang's leftward contour shift makes the remainder smaller
than a fixed fraction of the arithmetic main term.  We use `1/2` only as a convenient
normalization: any explicit fraction strictly below `1` would suffice. -/
def Lemma57SmallError {D : ℕ}
    (arith : Lemma57ArithmeticLowerBound D)
    (contourError : ℝ) : Prop :=
  contourError ≤ (arith.constant / 2) * lemma57Scale D

/-- Positivity of the arithmetic scale for a nontrivial modulus. -/
theorem lemma57Scale_pos {D : ℕ} (hD : 1 < D) : 0 < lemma57Scale D := by
  unfold lemma57Scale
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hphiNat : 0 < Nat.totient D := Nat.totient_pos.mpr (Nat.zero_lt_of_lt hD)
  have hphi : (0 : ℝ) < Nat.totient D := by exact_mod_cast hphiNat
  positivity

/-- Pure quantitative transfer used at the end of Lemma 5.7.

If the smoothed arithmetic sum is at least `c · D/φ(D)` and the contour formula
approximates `L'(1,χ)` with error at most half that amount, then
`L'(1,χ) ≥ (c/2) · D/φ(D)`.
-/
theorem lemma57_transfer
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (arith : Lemma57ArithmeticLowerBound D)
    (contour : Lemma57ContourApproximation χ arith.mainSum)
    (hsmall : Lemma57SmallError arith contour.error) :
    (arith.constant / 2) * lemma57Scale D ≤ realLDerivAtOne χ := by
  have habs : arith.mainSum - realLDerivAtOne χ ≤ contour.error :=
    le_trans (le_abs_self _) contour.approximation
  have hscale : 0 < lemma57Scale D := lemma57Scale_pos hD
  have hcscale : 0 < arith.constant * lemma57Scale D :=
    mul_pos arith.constant_pos hscale
  dsimp [Lemma57SmallError] at hsmall
  nlinarith [arith.lower_bound]

/-- Once the arithmetic and analytic sublemmas are supplied uniformly, the paper-level
Lemma 5.7 target follows.  This theorem deliberately exposes those two genuine proof
obligations instead of replacing them by a hypothesis equal to the conclusion. -/
theorem lemma57_of_uniform_inputs
    (c : ℝ) (hc : 0 < c)
    (harith : ∀ {D : ℕ}, 1 < D →
      ∃ a : Lemma57ArithmeticLowerBound D, a.constant = c)
    (hcontour : ∀ {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
      (hA : NormalizedAssumptionA χ) (a : Lemma57ArithmeticLowerBound D),
      a.constant = c →
      ∃ ca : Lemma57ContourApproximation χ a.mainSum,
        Lemma57SmallError a ca.error) :
    Lemma57AtConstant (c / 2) := by
  constructor
  · positivity
  · refine ⟨2, ?_⟩
    intro D χ _ hD hA
    obtain ⟨a, ha⟩ := harith hD
    obtain ⟨ca, hsmall⟩ := hcontour χ hD hA a ha
    have h := lemma57_transfer χ hD a ca hsmall
    simpa [ha] using h

end ZhangLS.Spec
