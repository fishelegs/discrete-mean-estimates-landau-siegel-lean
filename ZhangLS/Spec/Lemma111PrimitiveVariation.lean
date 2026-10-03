import ZhangLS.Spec.Lemma111SmoothedTent
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Bounded variation of the actual Gaussian primitive error. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped BigOperators

noncomputable def lemma111PrimitiveError (D : ℕ) (t : ℝ) : ℝ :=
  lemma111Primitive D t - max t 0

lemma lemma111_primitive_monotone {D : ℕ} (hD : 1 < D) :
    Monotone (lemma111Primitive D) :=
  monotone_of_hasDerivAt_nonneg (lemma111_primitive_hasDerivAt hD)
    (lemma111_profile_nonneg hD)

lemma lemma111_primitive_sub_id_antitone {D : ℕ} (hD : 1 < D) :
    Antitone (fun t => lemma111Primitive D t - t) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t => (lemma111_primitive_hasDerivAt hD t).sub (hasDerivAt_id t))
  intro t
  exact sub_nonpos.mpr (lemma111_profile_le_one hD t)

lemma lemma111_primitive_zero_le {D : ℕ} (hD : 1 < D) :
    lemma111Primitive D 0 ≤ 1 / lemma111Scale D := by
  have hA := lemma111_scale_pos hD
  have hπ := lemma111_sqrt_pi_ge_one
  simp only [lemma111Primitive, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
    neg_zero, Real.exp_zero, zero_add]
  apply one_div_le_one_div_of_le hA
  nlinarith

lemma lemma111_primitive_error_split (D : ℕ) (t : ℝ) :
    lemma111PrimitiveError D t =
      lemma111Primitive D (min t 0) +
        (lemma111Primitive D (max t 0) - max t 0) - lemma111Primitive D 0 := by
  by_cases ht : t ≤ 0
  · simp [lemma111PrimitiveError, min_eq_left ht, max_eq_right ht]
  · simp [lemma111PrimitiveError, min_eq_right (le_of_not_ge ht),
      max_eq_left (le_of_not_ge ht)]

lemma lemma111_primitive_error_variation {D : ℕ} (hD : 1 < D)
    (t : ℕ → ℝ) (ht : Antitone t) (N : ℕ) :
    |lemma111PrimitiveError D (t N)| +
      ∑ n ∈ range N, |lemma111PrimitiveError D (t (n+1)) -
        lemma111PrimitiveError D (t n)| ≤ 8 / lemma111Scale D := by
  let a : ℕ → ℝ := fun n => lemma111Primitive D (min (t n) 0)
  let b : ℕ → ℝ := fun n => lemma111Primitive D (max (t n) 0) - max (t n) 0
  have ha : Antitone a := fun i j hij =>
    lemma111_primitive_monotone hD (min_le_min_right 0 (ht hij))
  have hb : Monotone b := fun i j hij =>
    lemma111_primitive_sub_id_antitone hD (max_le_max_right 0 (ht hij))
  have hea (n : ℕ) : a n = lemma111PrimitiveError D (min (t n) 0) := by
    simp [a, lemma111PrimitiveError, max_eq_right (min_le_right (t n) 0)]
  have heb (n : ℕ) : b n = lemma111PrimitiveError D (max (t n) 0) := by
    simp [b, lemma111PrimitiveError, max_eq_left (le_max_right (t n) 0)]
  have ha0 : a 0 ≤ 1 / lemma111Scale D :=
    (lemma111_primitive_monotone hD (min_le_right (t 0) 0)).trans
      (lemma111_primitive_zero_le hD)
  have hbN : b N ≤ 1 / lemma111Scale D := by
    have h := lemma111_primitive_sub_id_antitone hD (le_max_right (t N) 0)
    simp only [sub_zero] at h
    exact h.trans (lemma111_primitive_zero_le hD)
  have haN : -(2 / lemma111Scale D) ≤ a N := by
    rw [hea]
    exact (abs_le.mp (lemma111_primitive_error_uniform hD _)).1
  have hb0 : -(2 / lemma111Scale D) ≤ b 0 := by
    rw [heb]
    exact (abs_le.mp (lemma111_primitive_error_uniform hD _)).1
  have hs : (∑ n ∈ range N, |lemma111PrimitiveError D (t (n+1)) -
      lemma111PrimitiveError D (t n)|) ≤ (a 0 - a N) + (b N - b 0) := by
    calc
      _ ≤ ∑ n ∈ range N, ((a n - a (n+1)) + (b (n+1) - b n)) := by
        apply sum_le_sum
        intro n hn
        have he : lemma111PrimitiveError D (t (n+1)) -
            lemma111PrimitiveError D (t n) =
              -(a n - a (n+1)) + (b (n+1) - b n) := by
          rw [lemma111_primitive_error_split, lemma111_primitive_error_split]
          dsimp [a, b]
          ring
        rw [he]
        calc
          _ ≤ |-(a n - a (n+1))| + |b (n+1) - b n| := abs_add_le _ _
          _ = _ := by
            rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr (ha (Nat.le_succ n))),
              abs_of_nonneg (sub_nonneg.mpr (hb (Nat.le_succ n)))]
      _ = _ := by
        rw [sum_add_distrib]
        have hsa : (∑ n ∈ range N, (a n - a (n+1))) = a 0 - a N := by
          clear hbN haN
          induction N with
          | zero => simp
          | succ N ih => rw [sum_range_succ, ih]; ring
        have hsb : (∑ n ∈ range N, (b (n+1) - b n)) = b N - b 0 := by
          clear hbN haN hsa
          induction N with
          | zero => simp
          | succ N ih => rw [sum_range_succ, ih]; ring
        rw [hsa, hsb]
  have he := lemma111_primitive_error_uniform hD (t N)
  change |lemma111PrimitiveError D (t N)| ≤ _ at he
  simp only [div_eq_mul_inv] at ha0 hbN haN hb0 he ⊢
  linarith

end ZhangLS.Spec
