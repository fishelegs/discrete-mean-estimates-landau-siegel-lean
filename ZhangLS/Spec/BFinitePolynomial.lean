import ZhangLS.Spec.Lemma151Basis
import ZhangLS.Spec.Lemma44RightMellinApproximation
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Strict positive-index support, retaining the endpoint rather than rounding it. -/
def BStrictSupport (X : ℝ) (a : ℕ → ℂ) : Prop :=
  ∀ n, a n ≠ 0 → 0 < n ∧ (n : ℝ) < X

lemma b_strict_support_mem {X : ℝ} {a : ℕ → ℂ}
    (ha : BStrictSupport X a) {n : ℕ} (hn : a n ≠ 0) :
    n ∈ Icc 1 ⌈X⌉₊ := by
  obtain ⟨hn0,hnX⟩ := ha n hn
  exact mem_Icc.mpr ⟨hn0,Nat.le_of_lt (Nat.lt_ceil.mpr hnX)⟩

lemma b_strict_support_term_zero {X : ℝ} {a : ℕ → ℂ}
    (ha : BStrictSupport X a) (s : ℂ) {n : ℕ} (hn : n ∉ Icc 1 ⌈X⌉₊) :
    LSeries.term a s n = 0 := by
  have hz : a n = 0 := by
    by_contra hne
    exact hn (b_strict_support_mem ha hne)
  simp [LSeries.term_def,hz]

lemma b_strict_support_summable {X : ℝ} {a : ℕ → ℂ}
    (ha : BStrictSupport X a) (s : ℂ) : LSeriesSummable a s :=
  summable_of_ne_finset_zero (fun _ hn => b_strict_support_term_zero ha s hn)

/-- Exact bridge to the existing project finite Dirichlet-polynomial API. -/
theorem b_strict_support_LSeries_eq_polynomial {X : ℝ} {a : ℕ → ℂ}
    (ha : BStrictSupport X a) (s : ℂ) :
    LSeries a s = lemma23FiniteDirichletPolynomial ⌈X⌉₊ a s := by
  unfold LSeries lemma23FiniteDirichletPolynomial
  rw [tsum_eq_sum (fun _ hn => b_strict_support_term_zero ha s hn)]
  exact sum_congr rfl (fun n hn =>
    lemma44_LSeries_term_eq_exp a s (Nat.ne_of_gt (mem_Icc.mp hn).1))

lemma b_strict_support_mul_left {X : ℝ} {a : ℕ → ℂ}
    (ha : BStrictSupport X a) (w : ℕ → ℂ) :
    BStrictSupport X (fun n => w n * a n) := by
  intro n hn
  exact ha n (right_ne_zero_of_mul hn)

lemma b_strict_support_add {X Y : ℝ} {a b : ℕ → ℂ}
    (ha : BStrictSupport X a) (hb : BStrictSupport Y b) :
    BStrictSupport (max X Y) (fun n => a n + b n) := by
  intro n hn
  by_cases h : a n = 0
  · have hbn : b n ≠ 0 := by simpa [h] using hn
    exact ⟨(hb n hbn).1,(hb n hbn).2.trans_le (le_max_right X Y)⟩
  · exact ⟨(ha n h).1,(ha n h).2.trans_le (le_max_left X Y)⟩

/-- Finite convolution has the strict product cutoff, including the boundary. -/
theorem b_strict_support_convolution {X Y : ℝ} {a b : ℕ → ℂ}
    (ha : BStrictSupport X a) (hb : BStrictSupport Y b) :
    BStrictSupport (X*Y) (LSeries.convolution a b) := by
  intro n hn
  have hex : ∃ p ∈ n.divisorsAntidiagonal, a p.1*b p.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (by rw [LSeries.convolution_def]; exact sum_eq_zero h)
  obtain ⟨p,hp,hne⟩ := hex
  obtain ⟨ha0,haX⟩ := ha p.1 (left_ne_zero_of_mul hne)
  obtain ⟨hb0,hbY⟩ := hb p.2 (right_ne_zero_of_mul hne)
  have hpEq := (Nat.mem_divisorsAntidiagonal.mp hp).1
  constructor
  · rw [← hpEq]; exact Nat.mul_pos ha0 hb0
  · have har : (0 : ℝ) < p.1 := Nat.cast_pos.mpr ha0
    have hbr : (0 : ℝ) < p.2 := Nat.cast_pos.mpr hb0
    rw [← hpEq,Nat.cast_mul]
    exact mul_lt_mul haX hbY.le hbr (har.trans haX).le

/-- A genuinely derived finite product identity, with its support assumptions explicit. -/
theorem b_finite_polynomial_product {X Y : ℝ} {a b : ℕ → ℂ}
    (ha : BStrictSupport X a) (hb : BStrictSupport Y b) (s : ℂ) :
    lemma23FiniteDirichletPolynomial ⌈X⌉₊ a s *
      lemma23FiniteDirichletPolynomial ⌈Y⌉₊ b s =
    lemma23FiniteDirichletPolynomial ⌈X*Y⌉₊ (LSeries.convolution a b) s := by
  rw [← b_strict_support_LSeries_eq_polynomial ha,
    ← b_strict_support_LSeries_eq_polynomial hb,
    ← b_strict_support_LSeries_eq_polynomial (b_strict_support_convolution ha hb)]
  exact (LSeries_convolution' (b_strict_support_summable ha s)
    (b_strict_support_summable hb s)).symm

end ZhangLS.Spec
