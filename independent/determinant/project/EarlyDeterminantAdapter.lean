import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Elementary adapter for the early determinant comparison

Intended toolchain: Lean 4.34.1.
Intended mathlib revision: d13f23b723b8a846827a245b89c10fc7d3f11612.

This file proves only implications between explicit real inequalities.  It does
not construct a determinant, prove a finite-place estimate, prove an
archimedean estimate, prove rectangular spanning, or establish a prime-mass
estimate.  In particular, its main theorem is conditional.

The intended substitutions are
  ell = log D, U = D^32, M = D^96,
  a = log 8, b = log 4, m = m_chi(U), t = L(1, chi).
The identities log N = 24 ell, log U = 32 ell, log M = 96 ell
are already substituted into the hypotheses below.  No theorem identifying
these real placeholders with analytic quantities is claimed here.

One structure packages all four finite inequalities for the SAME values of
S1, S2, and Q.  Q is intended to equal (1/4) log |Norm Delta|.  A caller must
supply the structure; separate existential witnesses cannot be spliced.

The two final error bounds are assumptions.  They have NOT been derived from
a conductor cutoff in this file.  Likewise, the identification of t with the
chosen L-function normalization remains outside this arithmetic adapter.
-/

namespace EarlyDeterminantAdapter

/-- The four supplied finite inequalities, all for one coherent witness. -/
structure FiniteWitness (ell k M U m a b : ℝ) where
  S1 : ℝ
  S2 : ℝ
  Q : ℝ
  mass_lower : k * M * U ≤ S1
  row_ratio : 0 ≤ S2 / S1 ∧ S2 / S1 ≤ 1 / 12
  finite_lower : S1 * m - b * M * U ≤ Q
  arch_upper : Q ≤ (M / 2) * (96 * ell) +
    (S1 + S2) * (24 * ell + ell / 2 + a)

/-- The fully explicit finite DET upper bound; no error term is discarded. -/
noncomputable def detUpper (ell k U a b : ℝ) : ℝ :=
  637 / 768 + ((13 / 12) * a + b / k) / (32 * ell) +
    3 / (2 * k * U)

/-- Algebraic extraction of DET from one supplied finite witness. -/
theorem determinant_upper
    {ell k M U m a b : ℝ}
    (hell : 0 < ell) (hk : 0 < k) (hM : 0 < M) (hU : 0 < U)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (w : FiniteWitness ell k M U m a b) :
    m / (32 * ell) ≤ detUpper ell k U a b := by
  have hS1 : 0 < w.S1 :=
    lt_of_lt_of_le (mul_pos (mul_pos hk hM) hU) w.mass_lower
  have hS2 : w.S2 ≤ (1 / 12 : ℝ) * w.S1 :=
    (div_le_iff₀ hS1).mp w.row_ratio.2
  have hrows : w.S1 + w.S2 ≤ (13 / 12 : ℝ) * w.S1 := by
    linarith
  let C : ℝ := 24 * ell + ell / 2 + a
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have harch : w.Q ≤ 48 * M * ell + ((13 / 12 : ℝ) * w.S1) * C := by
    have hproduct := mul_le_mul_of_nonneg_right hrows hC
    have hw := w.arch_upper
    change w.Q ≤ (M / 2) * (96 * ell) + (w.S1 + w.S2) * C at hw
    nlinarith
  have hbterm : b * M * U ≤ (b / k) * w.S1 := by
    calc
      b * M * U = (b / k) * (k * M * U) := by
        field_simp [ne_of_gt hk] <;> ring
      _ ≤ (b / k) * w.S1 :=
        mul_le_mul_of_nonneg_left w.mass_lower (div_nonneg hb hk.le)
  have hmterm : 48 * M * ell ≤ (48 * ell / (k * U)) * w.S1 := by
    calc
      48 * M * ell = (48 * ell / (k * U)) * (k * M * U) := by
        field_simp [ne_of_gt hk, ne_of_gt hU] <;> ring
      _ ≤ (48 * ell / (k * U)) * w.S1 :=
        mul_le_mul_of_nonneg_left w.mass_lower (by positivity)
  have hm : m ≤ (13 / 12 : ℝ) * C + b / k + 48 * ell / (k * U) := by
    apply le_of_mul_le_mul_left (a := w.S1) _ hS1
    have hfinite := w.finite_lower
    nlinarith
  apply (div_le_iff₀ (show 0 < 32 * ell by positivity)).2
  calc
    m ≤ (13 / 12 : ℝ) * C + b / k + 48 * ell / (k * U) := hm
    _ = detUpper ell k U a b * (32 * ell) := by
      dsimp [C, detUpper]
      field_simp [ne_of_gt hell, ne_of_gt hk, ne_of_gt hU] <;> ring

/-- The displayed DET formula with log 8 and log 4, still conditional on the
four finite inequalities.  This does not establish those inequalities. -/
theorem determinant_upper_log
    {ell k M U m : ℝ}
    (hell : 0 < ell) (hk : 0 < k) (hM : 0 < M) (hU : 0 < U)
    (w : FiniteWitness ell k M U m (Real.log 8) (Real.log 4)) :
    m / (32 * ell) ≤
      637 / 768 + ((13 / 12) * Real.log 8 + Real.log 4 / k) /
        (32 * ell) + 3 / (2 * k * U) := by
  exact determinant_upper hell hk hM hU
    (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num)) w

/-- The exact rational margin forced by the assumed prime-mass and DET bounds.
The assumptions a ≤ 3 and b ≤ 2 expose the elementary log bounds used later. -/
theorem prime_mass_margin
    {ell k m t a b e1 e2 : ℝ}
    (hell : 0 < ell) (hk : 1 ≤ k)
    (ha : a ≤ 3) (hb : b ≤ 2)
    (hprime : 7 / 8 - 1 / (4 * ell) - 14 * ell * t - e1 ≤
      m / (32 * ell))
    (hdet : m / (32 * ell) ≤
      637 / 768 + ((13 / 12) * a + b / k) / (32 * ell) + e2) :
    35 / 768 - 53 / (128 * ell) - e1 - e2 ≤ 14 * ell * t := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hbk : b / k ≤ 2 := by
    apply (div_le_iff₀ hkpos).2
    linarith
  have hcoeff : (13 / 12 : ℝ) * a + b / k ≤ 21 / 4 := by
    linarith
  have herr : ((13 / 12 : ℝ) * a + b / k) / (32 * ell) ≤
      21 / (128 * ell) := by
    calc
      ((13 / 12 : ℝ) * a + b / k) / (32 * ell) ≤
          (21 / 4 : ℝ) / (32 * ell) :=
        div_le_div_of_nonneg_right hcoeff (by positivity)
      _ = 21 / (128 * ell) := by
        field_simp [ne_of_gt hell] <;> ring
  have hdet' : m / (32 * ell) ≤
      637 / 768 + 21 / (128 * ell) + e2 := by
    linarith
  have hid : 1 / (4 * ell) + 21 / (128 * ell) =
      53 / (128 * ell) := by
    field_simp [ne_of_gt hell] <;> ring
  linarith

/-- Strict finite-error arithmetic.  The hypotheses e1,e2 < 1/1024 are
explicit; no positivity or smallness assumption on t is required. -/
theorem strict_lower_of_margin
    {ell t e1 e2 : ℝ}
    (hell : 12 ≤ ell)
    (he1 : e1 < 1 / 1024) (he2 : e2 < 1 / 1024)
    (hmargin : 35 / 768 - 53 / (128 * ell) - e1 - e2 ≤
      14 * ell * t) :
    1 / (1536 * ell) < t := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hfrac : (53 : ℝ) / (128 * ell) ≤ 53 / 1536 := by
    apply (div_le_iff₀ (show 0 < 128 * ell by positivity)).2
    nlinarith
  have hstrict : (7 : ℝ) / 768 < 14 * ell * t := by
    linarith
  apply (div_lt_iff₀ (show 0 < 1536 * ell by positivity)).2
  nlinarith

/-- The requested weaker constant follows from the stronger endpoint. -/
theorem weaker_lower_of_strong
    {ell t : ℝ} (hell : 0 < ell)
    (hstrong : 1 / (1536 * ell) < t) :
    1 / (4096 * ell) < t := by
  have hcompare : (1 : ℝ) / (4096 * ell) < 1 / (1536 * ell) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  exact lt_trans hcompare hstrong

/-- The arithmetic endpoint from supplied prime-mass and determinant bounds. -/
theorem lower_bound_of_comparison
    {ell k m t a b e1 e2 : ℝ}
    (hell : 12 ≤ ell) (hk : 1 ≤ k)
    (ha : a ≤ 3) (hb : b ≤ 2)
    (he1 : e1 < 1 / 1024) (he2 : e2 < 1 / 1024)
    (hprime : 7 / 8 - 1 / (4 * ell) - 14 * ell * t - e1 ≤
      m / (32 * ell))
    (hdet : m / (32 * ell) ≤
      637 / 768 + ((13 / 12) * a + b / k) / (32 * ell) + e2) :
    1 / (1536 * ell) < t ∧ 1 / (4096 * ell) < t := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hmargin := prime_mass_margin hellpos hk ha hb hprime hdet
  have hstrong := strict_lower_of_margin hell he1 he2 hmargin
  exact ⟨hstrong, weaker_lower_of_strong hellpos hstrong⟩

/-- Full conditional same-witness adapter.

The caller supplies:
* ell ≥ 12, k ≥ 1, M > 0, U > 0;
* 0 ≤ a ≤ 3 and 0 ≤ b ≤ 2 (intended log 8 and log 4);
* e1 < 1/1024, e2 < 1/1024, and coverage of the exact determinant tail;
* the prime-mass lower bound;
* one coherent witness for all four determinant inequalities.

Nothing in this theorem proves the existence or validity of those inputs. -/
theorem lower_bound_from_same_witness
    {ell k M U m t a b e1 e2 : ℝ}
    (hell : 12 ≤ ell) (hk : 1 ≤ k) (hM : 0 < M) (hU : 0 < U)
    (ha0 : 0 ≤ a) (ha3 : a ≤ 3) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (he1 : e1 < 1 / 1024) (he2 : e2 < 1 / 1024)
    (htail : 3 / (2 * k * U) ≤ e2)
    (hprime : 7 / 8 - 1 / (4 * ell) - 14 * ell * t - e1 ≤
      m / (32 * ell))
    (w : FiniteWitness ell k M U m a b) :
    1 / (1536 * ell) < t ∧ 1 / (4096 * ell) < t := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hd := determinant_upper hellpos hkpos hM hU ha0 hb0 w
  have hdet : m / (32 * ell) ≤
      637 / 768 + ((13 / 12) * a + b / k) / (32 * ell) + e2 := by
    dsimp [detUpper] at hd
    linarith
  exact lower_bound_of_comparison hell hk ha3 hb2 he1 he2 hprime hdet

#check determinant_upper
#check determinant_upper_log
#check prime_mass_margin
#check strict_lower_of_margin
#check lower_bound_of_comparison
#check lower_bound_from_same_witness

#print axioms determinant_upper
#print axioms determinant_upper_log
#print axioms prime_mass_margin
#print axioms strict_lower_of_margin
#print axioms weaker_lower_of_strong
#print axioms lower_bound_of_comparison
#print axioms lower_bound_from_same_witness

end EarlyDeterminantAdapter
