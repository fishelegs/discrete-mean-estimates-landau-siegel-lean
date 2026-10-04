import Mathlib.Analysis.PSeries
import ZhangLS.Spec.SquareNuTailMajorantDefs
import ZhangLS.Spec.DivisorSmallPowerBudget

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ZhangLS.Spec
open Finset

lemma squareTauMoment_rpow_square (n : ℕ) :
    ((n^2 : ℕ) : ℝ)^(-(3/4:ℝ)) = (n:ℝ)^(-(3/2:ℝ)) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

lemma squareTauMoment_summable_of_quarter_bound (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hbound : ∀ n, a n ≤ C*(n:ℝ)^(1/4:ℝ)) :
    Summable (fun n : ℕ => a n*(n:ℝ)^(-(3/2:ℝ))) := by
  have hs : Summable (fun n : ℕ => C*(n:ℝ)^(-(5/4:ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(5/4:ℝ) < -1)).mul_left C
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) _ hs
  intro n
  calc
    a n*(n:ℝ)^(-(3/2:ℝ)) ≤ (C*(n:ℝ)^(1/4:ℝ))*(n:ℝ)^(-(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (hbound n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = C*(n:ℝ)^(-(5/4:ℝ)) := by
      by_cases hn : n=0
      · subst n; norm_num
      rw [mul_assoc, ←Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
      norm_num

lemma squareTauMoment_summable_of_square_support (f : ℕ → ℝ)
    (hf : ∀ n, ¬IsSquare n → f n=0)
    (hs : Summable (fun h : ℕ => f (h^2)*(h:ℝ)^(-(3/2:ℝ)))) :
    Summable (fun n : ℕ => f n*(n:ℝ)^(-(3/4:ℝ))) := by
  apply (Nat.pow_left_injective (by norm_num : (2:ℕ)≠0)).summable_iff ?_ |>.mp
  · change Summable (fun h : ℕ => f (h^2)*((h^2:ℕ):ℝ)^(-(3/4:ℝ)))
    simpa only [squareTauMoment_rpow_square] using hs
  · intro n hn
    have hn' : ¬IsSquare n := by
      rintro ⟨h, rfl⟩
      exact hn ⟨h, by simp [pow_two]⟩
    rw [hf n hn', zero_mul]

lemma squareTauMoment_harmonic_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n : ℕ => f n*(n:ℝ)^(-(3/4:ℝ)))) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n/(n:ℝ)) ≤ ∑' n : ℕ, f n*(n:ℝ)^(-(3/4:ℝ)) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, f n*(n:ℝ)^(-(3/4:ℝ)) := by
      apply sum_le_sum
      intro n hn
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (mem_Icc.mp hn).1)
          (by norm_num : (-1:ℝ) ≤ -(3/4:ℝ))) (hf n)
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ => mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma squareTauMoment_tail_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n : ℕ => f n*(n:ℝ)^(-(3/4:ℝ))))
    (D : ℝ) (hD : 1 ≤ D) (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => D<(n:ℝ)), f n/(n:ℝ)) ≤
      D^(-(1/4:ℝ))*(∑' n : ℕ, f n*(n:ℝ)^(-(3/4:ℝ))) := by
  calc
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => D<(n:ℝ)),
        D^(-(1/4:ℝ))*(f n*(n:ℝ)^(-(3/4:ℝ))) := by
      apply sum_le_sum
      intro n hn
      have hnD : D < (n:ℝ) := (mem_filter.mp hn).2
      have hn0 : 0 < (n:ℝ) := lt_trans (lt_of_lt_of_le zero_lt_one hD) hnD
      have hp := Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hD) hnD.le
        (by norm_num : -(1/4:ℝ) ≤ 0)
      calc
        _ = (n:ℝ)^(-(1/4:ℝ))*(f n*(n:ℝ)^(-(3/4:ℝ))) := by
          rw [mul_left_comm, ← Real.rpow_add hn0]
          norm_num [div_eq_mul_inv, Real.rpow_neg_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right hp
          (mul_nonneg (hf n) (Real.rpow_nonneg hn0.le _))
    _ = D^(-(1/4:ℝ))*(∑ n ∈ (Icc 1 N).filter (fun n : ℕ => D<(n:ℝ)),
        f n*(n:ℝ)^(-(3/4:ℝ))) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ (fun n _ => mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (Real.rpow_nonneg (by positivity) _)

/-- The three-quarter moment of the square lift is summable at every order. -/
lemma squareTau_moment_summable (K : ℕ) :
    Summable (fun n : ℕ => squareTau K n*(n:ℝ)^(-(3/4:ℝ))) := by
  cases K with
  | zero =>
    have he : (fun n : ℕ => squareTau 0 n*(n:ℝ)^(-(3/4:ℝ))) =
        (fun n : ℕ => if n=1 then (1:ℝ) else 0) := by
      funext n
      rw [squareTau_zero_order]
      by_cases hn : n=1
      · subst n; simp
      · simp [ArithmeticFunction.one_apply, hn]
    rw [he]
    exact (hasSum_ite_eq 1 (1:ℝ)).summable
  | succ K =>
    apply squareTauMoment_summable_of_square_support (fun n => squareTau (K+1) n)
      (fun n hn => squareTau_eq_zero (K+1) hn)
    simpa only [squareTau_sq] using squareTauMoment_summable_of_quarter_bound
      (fun n => (lemma34Tau (K+1) n:ℝ)) (divisorPowerQuarterConstant (K+1))
      (fun n => Nat.cast_nonneg _) (fun n => divisorPower_tau_quarter (by omega) n)

/-- A fixed finite constant controlling harmonic square mass and its strict tails. -/
noncomputable def squareTauMomentConstant (K : ℕ) : ℝ :=
  ∑' n : ℕ, squareTau K n*(n:ℝ)^(-(3/4:ℝ))

lemma squareTauMomentConstant_nonneg (K : ℕ) : 0 ≤ squareTauMomentConstant K := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (squareTau_nonneg K n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma squareTau_harmonic_le_moment (K N : ℕ) :
    (∑ n ∈ Icc 1 N, squareTau K n/(n:ℝ)) ≤ squareTauMomentConstant K :=
  squareTauMoment_harmonic_le _ (squareTau_nonneg K) (squareTau_moment_summable K) N

lemma squareTau_strict_tail_le_moment (K : ℕ) (D : ℝ) (hD : 1 ≤ D) (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => D<(n:ℝ)), squareTau K n/(n:ℝ)) ≤
      D^(-(1/4:ℝ))*squareTauMomentConstant K :=
  squareTauMoment_tail_le _ (squareTau_nonneg K) (squareTau_moment_summable K) D hD N

lemma squareTau_exists_harmonic_tail_constant (K : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ N : ℕ, (∑ n ∈ Icc 1 N, squareTau K n/(n:ℝ)) ≤ M) ∧
      (∀ (D : ℝ), 1 ≤ D → ∀ N : ℕ,
        (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => D<(n:ℝ)), squareTau K n/(n:ℝ)) ≤
          D^(-(1/4:ℝ))*M) :=
  ⟨squareTauMomentConstant K, squareTauMomentConstant_nonneg K,
    squareTau_harmonic_le_moment K, squareTau_strict_tail_le_moment K⟩

end ZhangLS.Spec
