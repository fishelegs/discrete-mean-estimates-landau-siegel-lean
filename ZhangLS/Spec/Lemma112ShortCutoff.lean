import ZhangLS.Spec.Lemma112ShortMellin
import ZhangLS.Spec.Lemma112ErrorFloor
/-! # Recovering the full dual Gaussian sum from the actual P₁ polynomial -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112FiniteGaussianSum {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (B : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
    (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D),
      LSeries.term (lemma112Coefficient χ ψ) s n * (zhangGaussianWeight D (B / n) : ℂ)

lemma lemma112_dual_scale_twice_below_cutoff {D : ℕ} (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {z : ℝ} (hz : 1 / 2 ≤ z) : 2 * lemma112DualScale D z ≤ lemma112PaperP1 D := by
  have hB := lemma112_dual_scale_pos hD z
  have hP : 0 < lemma112PaperP1 D := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hgap := (lemma112_dual_scale_cutoff_gap hD hL hz).2
  have h9 : (1000 : ℝ) ≤ lemma23PaperL D ^ 9 := by
    have h := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hL 2).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : 2 ≤ 9))
    norm_num at h
    linarith only [h]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  apply (Real.log_le_log_iff (by positivity : 0 < 2 * lemma112DualScale D z) hP).mp
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB.ne']
  linarith only [hgap, h9, hlog2]

lemma lemma112_finite_gaussian_cutoff_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {B : ℝ}
    (hB : 0 < B) (hlogB : Real.log B ≤ 2 * lemma23PaperL D ^ 9)
    (hcut : 2 * B ≤ lemma112PaperP1 D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma112GaussianSeries χ ψ B s - lemma112FiniteGaussianSum χ ψ B s‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  classical
  let S := (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
    (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D)
  let f : ℕ → ℂ := fun n => LSeries.term (lemma112Coefficient χ ψ) s n *
    (zhangGaussianWeight D (B / n) : ℂ)
  let short : ℕ → ℂ := fun n => if n ∈ S then f n else 0
  have hshort : Summable short := summable_of_ne_finset_zero (s := S) (fun n hn => by simp [short, hn])
  have hfull : Summable f := lemma112_actual_gaussian_summable χ ψ s hD hB
  have hmem (n : ℕ) (hn : n ≠ 0) : n ∈ S ↔ (n : ℝ) < lemma112PaperP1 D := by
    dsimp [S]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · exact fun h => h.2
    · intro h
      have hc : n ≤ ⌈lemma112PaperP1 D⌉₊ := by
        exact_mod_cast h.le.trans (Nat.le_ceil (lemma112PaperP1 D))
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hn, hc⟩, h⟩
  have he : (∑' n : ℕ, short n) = lemma112FiniteGaussianSum χ ψ B s := by
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [short, hn])]
    unfold lemma112FiniteGaussianSum
    apply Finset.sum_congr rfl
    intro n hn
    simp only [short, if_pos hn]
    rfl
  have hp (n : ℕ) : ‖f n - short n‖ ≤ Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹ := by
    by_cases hn0 : n = 0
    · subst n
      simp [f, short]
    by_cases hm : n ∈ S
    · simp only [short, if_pos hm, sub_self, norm_zero]
      positivity
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hncut : 2 * B ≤ (n : ℝ) := hcut.trans (le_of_not_gt (fun h => hm ((hmem n hn0).mpr h)))
    have hg : 0 ≤ zhangGaussianWeight D (B / n) := zhangGaussianWeight_nonneg hD (div_pos hB hnR)
    have hterm : ‖LSeries.term (lemma112Coefficient χ ψ) s n‖ ≤ 1 := by
      rw [LSeries.norm_term_eq, if_neg hn0]
      exact (div_le_self (norm_nonneg _) (Real.one_le_rpow (by exact_mod_cast hn) hs)).trans
        (lemma112_coefficient_norm_le_one χ ψ n)
    simp only [short, if_neg hm, sub_zero, f, norm_mul, Complex.norm_of_nonneg hg]
    exact (mul_le_mul hterm (lemma61_cutoff_gaussian_weight_bound hL hB hlogB hn hncut) hg
      (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  rw [lemma112GaussianSeries, ← he, ← hfull.tsum_sub hshort]
  have hnorm := summable_norm_iff.mpr (hfull.sub hshort)
  apply (norm_tsum_le_tsum_norm hnorm).trans
  exact (hnorm.tsum_le_tsum hp (lemma44_inverse_square_summable.mul_left _)).trans_eq (by
    rw [tsum_mul_left]
    unfold lemma44InverseSquareMass
    ring)

lemma lemma112_exp_remainder_le_polynomial {L : ℝ} (hL : 64 ≤ L) :
    Real.exp (-(L ^ 10) / 8) ≤ L ^ (-53 : ℤ) := by
  have h0 : 0 < L := by linarith
  have h1 : 1 ≤ L := by linarith
  have h9 : (424 : ℝ) ≤ L ^ 9 := by
    have h := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hL 2).trans
      (pow_le_pow_right₀ h1 (by norm_num : 2 ≤ 9))
    norm_num at h
    linarith only [h]
  have h10 : 424 * L ≤ L ^ 10 := by
    convert mul_le_mul_of_nonneg_right h9 h0.le using 1 <;> ring
  have hlog := Real.log_le_sub_one_of_pos h0
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos h0]
  apply Real.exp_le_exp.mpr
  norm_num
  linarith only [h10, hlog]

lemma lemma112_exp_remainder_le_E2 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    Real.exp (-(lemma23PaperL D ^ 10) / 8) ≤ lemma112ActualE2 χ ψ s :=
  (lemma112_exp_remainder_le_polynomial hL).trans (lemma112_E2_polynomial_floor χ ψ hL hs)

end ZhangLS.Spec
