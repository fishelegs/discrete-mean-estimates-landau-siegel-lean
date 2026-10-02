import ZhangLS.Spec.Lemma61ShortMellin

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_short_star_sum_eq_weighted {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) {B : ℝ}
    (hcut : 2 * B < lemma56PaperT D ^ 3) :
    (∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
        LSeries.term (fun n => ψ (n : ZMod p)) s n *
          (lemma61GaussianStar D (B / n) : ℂ)) =
      lemma61WeightedPolynomial D ψ B s := by
  rw [← lemma61_actual_weighted_tsum_eq_finite ψ B s]
  symm
  rw [tsum_eq_sum (s := (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
      (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3))]
  · exact Finset.sum_congr rfl (fun n _ => lemma61_weighted_term_eq_LSeries_term ψ B s n)
  · intro n hn
    by_cases hn0 : n = 0
    · simp [lemma61WeightedTerm,hn0]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnr : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlarge : lemma56PaperT D ^ 3 ≤ (n : ℝ) := by
      by_contra h
      have hsmall : (n : ℝ) < lemma56PaperT D ^ 3 := lt_of_not_ge h
      have hceil : n ≤ ⌈lemma56PaperT D ^ 3⌉₊ := by
        exact_mod_cast hsmall.le.trans (Nat.le_ceil _)
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1,hceil⟩,hsmall⟩)
    have hy : B / n ≤ 1 / 2 := by
      apply (div_le_iff₀ hnr).mpr
      linarith
    rw [lemma61_weighted_term_eq_LSeries_term,lemma61_gaussian_star_below_half hy]
    simp

lemma lemma61_short_gaussian_cutoff_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) {B : ℝ} (hB : 0 < B)
    (hlogB : Real.log B ≤ 2 * lemma23PaperL D ^ 9)
    (hcut : 2 * B < lemma56PaperT D ^ 3) (hs : 0 ≤ s.re) :
    ‖(∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
        LSeries.term (fun n => ψ (n : ZMod p)) s n *
          (zhangGaussianWeight D (B / n) : ℂ)) -
      lemma61WeightedPolynomial D ψ B s‖ ≤
        lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  rw [← lemma61_short_star_sum_eq_weighted ψ s hcut,← Finset.sum_sub_distrib]
  simp_rw [← mul_sub,← Complex.ofReal_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
        (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
        Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum (fun n _ => lemma61_cutoff_correction_term_bound ψ hD hL hB hlogB hs n)
    _ ≤ ∑' n : ℕ, Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ) ^ 2)⁻¹ :=
      (lemma44_inverse_square_summable.mul_left _).sum_le_tsum _ (fun n _ => by positivity)
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

lemma lemma61_N_support_inside_short_sum {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    2 * lemma56PaperT D ^ 2 < lemma56PaperT D ^ 3 := by
  have hpos : 0 < lemma56PaperT D := Real.exp_pos _
  have hlog := (lemma61_T_log_bounds hL).1
  have ht : 2 < lemma56PaperT D := by
    have h := Real.add_one_le_exp (Real.log (lemma56PaperT D))
    rw [Real.exp_log hpos] at h
    linarith
  convert mul_lt_mul_of_pos_right ht (pow_pos hpos 2) using 1 <;> ring

lemma lemma61_actual_full_short_mellin_N_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) (hs : s.re ≤ 1) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma61ShortRightMellinIntegrand D ψ (1 - s)
        (lemma56PaperT D ^ 2) 1 t * I) - lemma61ActualN D ψ (1 - s)‖ ≤
      lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  have hpos : 0 < lemma56PaperT D ^ 2 := pow_pos (Real.exp_pos _) 2
  rw [lemma61_actual_short_gaussian_mellin ψ (1 - s) hD hpos
    (by norm_num : (0 : ℝ) < 1)]
  exact lemma61_short_gaussian_cutoff_bound ψ (1 - s) hD hL
    hpos (lemma61_T_squared_log_bound hL)
    (lemma61_N_support_inside_short_sum hL) (by simpa using sub_nonneg.mpr hs)

end ZhangLS.Spec
