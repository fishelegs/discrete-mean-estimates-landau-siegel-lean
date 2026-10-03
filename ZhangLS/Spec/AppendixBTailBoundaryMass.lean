import ZhangLS.Spec.AppendixBTailUnsmoothing

/-! A genuine short-interval harmonic mass bound. The coefficient bound is
constant on n<=P, so no divisor average or artificial log(P) factor is lost. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma appendixB_interval_card_bound (S : Finset ℕ) {A B : ℝ}
    (hA : 0<A) (hAB : A≤B) (hS : ∀ n∈S, A≤(n : ℝ) ∧ (n : ℝ)≤B) :
    (S.card : ℝ)≤B-A+2 := by
  have hsub : S⊆Finset.Icc ⌊A⌋₊ ⌊B⌋₊ := by
    intro n hn
    refine Finset.mem_Icc.mpr ⟨?_,?_⟩
    · exact Nat.floor_le_of_le (hS n hn).1
    · exact (Nat.le_floor_iff (hA.le.trans hAB)).mpr (hS n hn).2
  have hfloor : ⌊A⌋₊≤⌊B⌋₊ := Nat.floor_mono hAB
  have hc := Finset.card_le_card hsub
  have hcr : (S.card : ℝ)≤((Finset.Icc ⌊A⌋₊ ⌊B⌋₊).card : ℝ) := by exact_mod_cast hc
  rw [Nat.card_Icc,Nat.cast_sub (by omega : ⌊A⌋₊≤⌊B⌋₊+1),Nat.cast_add,Nat.cast_one] at hcr
  have hlo := Nat.sub_one_lt_floor A
  have hhi := Nat.floor_le (hA.le.trans hAB)
  linarith

lemma appendixB_interval_harmonic_mass (S : Finset ℕ) {A B : ℝ}
    (hA : 0<A) (hAB : A≤B) (hS : ∀ n∈S, A≤(n : ℝ) ∧ (n : ℝ)≤B) :
    (∑ n∈S, (1 : ℝ)/n)≤(B-A+2)/A := by
  calc
    _ ≤ ∑ _n∈S, (1 : ℝ)/A := by
      apply Finset.sum_le_sum
      intro n hn
      exact one_div_le_one_div_of_le hA (hS n hn).1
    _ = (S.card : ℝ)/A := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (appendixB_interval_card_bound S hA hAB hS) hA.le

/-- The boundary mass includes an endpoint contribution of size 2 exp(delta)/Y.
It remains valid when Y itself is an integer and belongs to the complementary tail. -/
theorem appendixB_logarithmic_boundary_mass (S : Finset ℕ) {Y δ : ℝ}
    (hY : 0<Y) (hδ : 0≤δ) (hS : ∀ n∈S, 0<n)
    (hband : ∀ n∈S, |Real.log (Y/(n : ℝ))|≤δ) :
    (∑ n∈S, (1 : ℝ)/n)≤Real.exp (2*δ)-1+2*Real.exp δ/Y := by
  let A := Y*Real.exp (-δ)
  let B := Y*Real.exp δ
  have hA : 0<A := by dsimp [A]; positivity
  have hAB : A≤B := by dsimp [A,B]; gcongr; linarith
  have hbound (n : ℕ) (hn : n∈S) : A≤(n : ℝ) ∧ (n : ℝ)≤B := by
    have hnp : 0<(n : ℝ) := Nat.cast_pos.mpr (hS n hn)
    have hb := abs_le.mp (hband n hn)
    rw [Real.log_div hY.ne' hnp.ne'] at hb
    constructor
    · apply (Real.log_le_log_iff hA hnp).mp
      rw [show Real.log A=Real.log Y-δ by dsimp [A]; rw [Real.log_mul hY.ne' (Real.exp_pos _).ne',Real.log_exp]; ring]
      linarith
    · apply (Real.log_le_log_iff hnp (by dsimp [B]; positivity)).mp
      rw [show Real.log B=Real.log Y+δ by dsimp [B]; rw [Real.log_mul hY.ne' (Real.exp_pos _).ne',Real.log_exp]]
      linarith
  apply (appendixB_interval_harmonic_mass S hA hAB hbound).trans_eq
  dsimp [A,B]
  rw [Real.exp_neg,show Real.exp (2*δ)=(Real.exp δ)^2 by
    rw [show 2*δ=δ+δ by ring,Real.exp_add,pow_two]]
  field_simp [hY.ne',(Real.exp_pos δ).ne']
  <;> ring

end ZhangLS.Spec
