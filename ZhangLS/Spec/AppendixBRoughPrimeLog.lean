import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Genuine prime logarithmic mass, from Chebyshev's upper bound by discrete
partial summation. Replacing the prime sum by all integers would lose a log. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- Elementary Abel bound with a linear bound on nonnegative prefix sums. -/
lemma appendixB_weighted_prefix_bound (a : ℕ→ℝ) (C : ℝ) (hC : 0≤C)
    (ha : ∀ n, 0≤a n)
    (hprefix : ∀ n, (∑ i∈range n, a i)≤C*n) (N : ℕ) :
    (∑ i∈range N, a i/(i+1 : ℕ))≤C*(1+(harmonic N : ℝ)) := by
  by_cases hN : N=0
  · subst N; simp [hC]
  have hNp : 0<N := Nat.pos_of_ne_zero hN
  have hNr : 0<(N : ℝ) := by exact_mod_cast hNp
  have hab := Finset.sum_range_by_parts (fun i : ℕ => ((i+1 : ℕ) : ℝ)⁻¹) a N
  simp only [smul_eq_mul] at hab
  have hlast : ((N-1+1 : ℕ) : ℝ)⁻¹*(∑ i∈range N,a i)≤C := by
    rw [Nat.sub_add_cancel hNp]
    calc
      _ ≤ (N : ℝ)⁻¹*(C*N) := mul_le_mul_of_nonneg_left (hprefix N) (by positivity)
      _ = _ := by field_simp
  have hd (i : ℕ) : 0≤((i+1 : ℕ) : ℝ)⁻¹-((i+1+1 : ℕ) : ℝ)⁻¹ := by
    apply sub_nonneg.mpr
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.le_succ (i+1))
  have hterm (i : ℕ) :
      (((i+1 : ℕ) : ℝ)⁻¹-((i+1+1 : ℕ) : ℝ)⁻¹)*
        (∑ j∈range (i+1),a j)≤C*((i+1 : ℕ) : ℝ)⁻¹ := by
    calc
      _ ≤ (((i+1 : ℕ) : ℝ)⁻¹-((i+1+1 : ℕ) : ℝ)⁻¹)*(C*(i+1 : ℕ)) :=
        mul_le_mul_of_nonneg_left (hprefix (i+1)) (hd i)
      _ = C*((i+2 : ℕ) : ℝ)⁻¹ := by push_cast; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (by exact_mod_cast Nat.le_succ (i+1))) hC
  have hs : (∑ i∈range (N-1),
      (((i+1 : ℕ) : ℝ)⁻¹-((i+1+1 : ℕ) : ℝ)⁻¹)*(∑ j∈range (i+1),a j))≤
      C*(harmonic N : ℝ) := by
    calc
      _ ≤ ∑ i∈range (N-1),C*((i+1 : ℕ) : ℝ)⁻¹ := sum_le_sum (fun i _ => hterm i)
      _ ≤ ∑ i∈range N,C*((i+1 : ℕ) : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _)) (by intros; positivity)
      _ = _ := by simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,mul_sum]
  have he : (∑ i∈range N,a i/(i+1 : ℕ))=
      ((N-1+1 : ℕ) : ℝ)⁻¹*(∑ i∈range N,a i)+
      ∑ i∈range (N-1),
        (((i+1 : ℕ) : ℝ)⁻¹-((i+1+1 : ℕ) : ℝ)⁻¹)*(∑ j∈range (i+1),a j) := by
    rw [show (∑ i∈range N,a i/(i+1 : ℕ))=
      ∑ i∈range N,((i+1 : ℕ) : ℝ)⁻¹*a i by apply sum_congr rfl; intros; ring,hab]
    simp only [sub_mul,sum_sub_distrib]
    ring
  rw [he]
  nlinarith only [hlast,hs]

/-- This logarithmic prime mass estimate includes p=2 and closed p=N. -/
theorem appendixB_prime_log_mass (N : ℕ) :
    (∑ p∈(Icc 1 N).filter Nat.Prime, Real.log (p : ℝ)/(p : ℝ))≤
      Real.log 4*(2+Real.log (N : ℝ)) := by
  let a : ℕ→ℝ := fun i => if (i+1).Prime then Real.log (i+1 : ℕ) else 0
  have ha : ∀ i, 0≤a i := by
    intro i
    dsimp [a]
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos i)
    · exact le_rfl
  have hpref (n : ℕ) : (∑ i∈range n,a i)=Chebyshev.theta n := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    rw [←Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) n]
    simp only [zero_add,sum_filter]
    dsimp [a]
    rw [Finset.range_eq_Ico,Finset.sum_Ico_add' (fun i : ℕ => if i.Prime then Real.log (i : ℝ) else 0) 0 n (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc,zero_add]
  have hbound := appendixB_weighted_prefix_bound a (Real.log 4) (by positivity) ha
    (fun n => by rw [hpref n]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) N
  have he : (∑ p∈(Icc 1 N).filter Nat.Prime, Real.log (p : ℝ)/(p : ℝ))=
      ∑ i∈range N,a i/(i+1 : ℕ) := by
    rw [sum_filter]
    symm
    dsimp [a]
    simp only [ite_div,zero_div]
    rw [Finset.range_eq_Ico,Finset.sum_Ico_add' (fun i : ℕ => if i.Prime then Real.log (i : ℝ)/(i : ℝ) else 0) 0 N (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc,zero_add]
  rw [he]
  exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith [harmonic_le_one_add_log N]) (by positivity))

/-- The strict source domain is a subset of the closed Chebyshev domain. -/
theorem appendixB_prime_log_mass_strict (N : ℕ) :
    (∑ p∈(range N).filter Nat.Prime, Real.log (p : ℝ)/(p : ℝ))≤
      Real.log 4*(2+Real.log (N : ℝ)) := by
  apply le_trans _ (appendixB_prime_log_mass N)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases mem_filter.mp hp with ⟨hpN,hp⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos,(mem_range.mp hpN).le⟩,hp⟩
  · intro p hp hnot
    have hp := (mem_filter.mp hp).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Nat.cast_nonneg p)

end ZhangLS.Spec
