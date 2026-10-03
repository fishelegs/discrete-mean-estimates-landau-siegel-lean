import ZhangLS.Spec.Lemma111TentVariation

/-! Strict real cutoffs, first-endpoint convention, and positive-index handling. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped BigOperators Classical

lemma lemma111_sequence_variation_congr {f g : ℕ → ℝ} {N : ℕ}
    (h : ∀ n ≤ N, f n = g n) :
    lemma111SequenceVariation f N = lemma111SequenceVariation g N := by
  unfold lemma111SequenceVariation
  rw [h N le_rfl]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn' := mem_range.mp hn
  rw [h n (by omega), h (n+1) (by omega)]

/-- A strict initial-segment cutoff costs no extra factor in the last-endpoint
variation norm: its terminal jump is precisely the replaced endpoint term. -/
lemma lemma111_sequence_variation_cutoff {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ N, lemma111SequenceVariation f N ≤ C)
    (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ i j, i ≤ j → p j → p i) (N : ℕ) :
    lemma111SequenceVariation (fun n => if p n then f n else 0) N ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (by simpa [lemma111SequenceVariation] using hf 0)
  induction N with
  | zero =>
      by_cases h : p 0
      · simpa [lemma111SequenceVariation, h] using hf 0
      · simpa [lemma111SequenceVariation, h] using hC
  | succ N ih =>
      by_cases h : p (N+1)
      · have he : lemma111SequenceVariation (fun n => if p n then f n else 0) (N+1) =
            lemma111SequenceVariation f (N+1) := by
          apply lemma111_sequence_variation_congr
          intro n hn
          simp [hp n (N+1) hn h]
        rw [he]
        exact hf (N+1)
      · have he : lemma111SequenceVariation (fun n => if p n then f n else 0) (N+1) =
            lemma111SequenceVariation (fun n => if p n then f n else 0) N := by
          simp only [lemma111SequenceVariation, if_neg h, abs_zero, sum_range_succ,
            zero_sub, abs_neg, zero_add]
          ring
        rw [he]
        exact ih

lemma lemma111_tent_error_one_strict_variation {D : ℕ} (hD : 1 < D)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n) (hm : Monotone y) (X : ℝ) (N : ℕ) :
    lemma111SequenceVariation
      (fun n => if y n < X then lemma111TentErrorOne D (y n) else 0) N ≤
      16000 / lemma111Scale D := by
  apply lemma111_sequence_variation_cutoff (lemma111_tent_error_one_variation hD y hy hm)
  exact fun i j hij hj => lt_of_le_of_lt (hm hij) hj

lemma lemma111_tent_error_two_strict_variation {D : ℕ} (hD : 1 < D)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n) (hm : Monotone y) (X : ℝ) (N : ℕ) :
    lemma111SequenceVariation
      (fun n => if y n < X then lemma111TentErrorTwo D (y n) else 0) N ≤
      16000 / lemma111Scale D := by
  apply lemma111_sequence_variation_cutoff (lemma111_tent_error_two_variation hD y hy hm)
  exact fun i j hij hj => lt_of_le_of_lt (hm hij) hj

lemma lemma111_sequence_initial_le (f : ℕ → ℝ) (N : ℕ) :
    |f 0| ≤ lemma111SequenceVariation f N := by
  unfold lemma111SequenceVariation
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ]
      have ha : |f N| ≤ |f (N+1)| + |f (N+1) - f N| := by
        simpa only [sub_zero, abs_sub_comm (f N) (f (N+1)), add_comm] using
          abs_sub_le (f N) (f (N+1)) 0
      linarith

lemma lemma111_sequence_first_endpoint_le (f : ℕ → ℝ) (N : ℕ) :
    |f 0| + ∑ n ∈ range N, |f (n+1) - f n| ≤
      2 * lemma111SequenceVariation f N := by
  have h := lemma111_sequence_initial_le f N
  unfold lemma111SequenceVariation at h ⊢
  linarith [abs_nonneg (f N)]

lemma lemma111_sequence_first_Ico_le (f : ℕ → ℝ) (N : ℕ) :
    |f 1| + ∑ n ∈ Ico 1 N, |f (n+1) - f n| ≤
      2 * lemma111SequenceVariation (fun n => f (n+1)) (N-1) := by
  rw [sum_Ico_eq_sum_range]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    lemma111_sequence_first_endpoint_le (fun n => f (n+1)) (N-1)

lemma lemma111_positive_index_variation {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ N, lemma111SequenceVariation f N ≤ C) (N : ℕ) :
    |(if N = 0 then 0 else f (N-1))| +
      ∑ n ∈ range N, |(if n+1 = 0 then 0 else f n) -
        (if n = 0 then 0 else f (n-1))| ≤ 2*C := by
  cases N with
  | zero =>
      have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (by simpa [lemma111SequenceVariation] using hf 0)
      simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC
  | succ N =>
      have he : (∑ n ∈ range (N+1), |(if n+1 = 0 then 0 else f n) -
          (if n = 0 then 0 else f (n-1))|) =
          |f 0| + ∑ n ∈ range N, |f (n+1) - f n| := by
        rw [sum_range_succ']
        simp [add_comm]
      rw [he]
      simp only [show N+1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]
      have hstart := lemma111_sequence_initial_le f N
      have hv := hf N
      unfold lemma111SequenceVariation at hstart hv
      linarith

lemma lemma111_tent_error_one_first_Ico {D : ℕ} (hD : 1 < D) (N : ℕ) :
    |lemma111TentErrorOne D 1| + ∑ n ∈ Ico 1 N,
      |lemma111TentErrorOne D (n+1) - lemma111TentErrorOne D n| ≤
      32000 / lemma111Scale D := by
  have hv := lemma111_tent_error_one_variation hD (fun n => (n+1 : ℕ))
    (fun n => by dsimp; exact_mod_cast Nat.zero_lt_succ n)
    (fun i j hij => by dsimp; exact_mod_cast Nat.add_le_add_right hij 1) (N-1)
  have hf := lemma111_sequence_first_Ico_le (fun n => lemma111TentErrorOne D n) N
  simp only [Nat.cast_add, Nat.cast_one] at hv hf
  refine hf.trans ?_
  calc
    _ ≤ 2 * (16000 / lemma111Scale D) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

lemma lemma111_tent_error_two_first_Ico {D : ℕ} (hD : 1 < D) (N : ℕ) :
    |lemma111TentErrorTwo D 1| + ∑ n ∈ Ico 1 N,
      |lemma111TentErrorTwo D (n+1) - lemma111TentErrorTwo D n| ≤
      32000 / lemma111Scale D := by
  have hv := lemma111_tent_error_two_variation hD (fun n => (n+1 : ℕ))
    (fun n => by dsimp; exact_mod_cast Nat.zero_lt_succ n)
    (fun i j hij => by dsimp; exact_mod_cast Nat.add_le_add_right hij 1) (N-1)
  have hf := lemma111_sequence_first_Ico_le (fun n => lemma111TentErrorTwo D n) N
  simp only [Nat.cast_add, Nat.cast_one] at hv hf
  refine hf.trans ?_
  calc
    _ ≤ 2 * (16000 / lemma111Scale D) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

end ZhangLS.Spec
