import ZhangLS.Spec.Lemma44SmoothedTruncation

/-!
# The infinite Gaussian-smoothed tail above `P²`

At `B=P^(9/5)`, the tail starts with a logarithmic gap `L^9/5`.
Gaussian decay dominates a cubic power of `n`, with a remaining factor
`exp(-L^24/10) ≤ L^-180`. The resulting absolute constant is the convergent
inverse-square mass, independent of the character and modulus.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma44_gaussian_tail_weight {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {n : ℕ}
    (hn : ⌊lemma23PaperP D ^ 2⌋₊ < n) :
    zhangGaussianWeight D (lemma44PaperGaussianScale D / n) ≤
      Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹ := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnr : lemma23PaperP D ^ 2 < (n : ℝ) :=
    (Nat.floor_lt (by positivity)).mp hn
  have hlogn : 2 * L ^ 9 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (pow_pos (Real.exp_pos _) 2 : 0 < lemma23PaperP D ^ 2) hnr.le
    simpa [Real.log_pow, lemma23PaperP, Real.log_exp, L] using h
  have hlogB : Real.log (lemma44PaperGaussianScale D) = (9 / 5 : ℝ) * L ^ 9 := by
    rw [lemma44PaperGaussianScale, lemma23PaperP,
      Real.log_rpow (Real.exp_pos _), Real.log_exp]
  have hc : 60 ≤ L ^ 15 := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 4
    have h415 : L ^ 4 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by norm_num)
    norm_num at h4
    linarith only [h4, h415]
  have hB : 0 < lemma44PaperGaussianScale D :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hy : L ^ 24 / 10 + 3 * Real.log (n : ℝ) ≤
      -zhangGaussianEndpoint D (lemma44PaperGaussianScale D / n) := by
    rw [zhangGaussianEndpoint, Real.log_div hB.ne' hnp.ne', hlogB]
    change L ^ 24 / 10 + 3 * Real.log (n : ℝ) ≤
      -(L ^ 15 * ((9 / 5 : ℝ) * L ^ 9 - Real.log (n : ℝ)))
    have hp := mul_nonneg (by linarith only [hc] : 0 ≤ L ^ 15 - 3)
      (sub_nonneg.mpr hlogn)
    have hq := mul_nonneg (by linarith only [hc] : 0 ≤ L ^ 15 / 10 - 6)
      (show 0 ≤ L ^ 9 by positivity)
    have heq : L ^ 15 * L ^ 9 = L ^ 24 := by ring
    nlinarith only [hp, hq, heq]
  have h24 := lemma44_L24_dominates_linear hL
  have hlognpos : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hn)
  have hw := lemma44_gaussian_weight_le_exp_endpoint
    (by nlinarith only [hy, h24, hL, hlognpos] :
      1 ≤ -zhangGaussianEndpoint D (lemma44PaperGaussianScale D / n))
  calc
    _ ≤ Real.exp (zhangGaussianEndpoint D (lemma44PaperGaussianScale D / n)) := hw
    _ ≤ Real.exp (-(L ^ 24) / 10 - 3 * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith only [hy])
    _ = Real.exp (-(L ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹ := by
      rw [Real.exp_sub]
      have h3 : Real.exp (3 * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
        simpa [Real.exp_log hnp] using Real.exp_nat_mul (Real.log (n : ℝ)) 3
      rw [h3]
      ring

theorem lemma44_gaussian_tail_budget {L : ℝ} (hL : 3 ≤ L) :
    Real.exp (-(L ^ 24) / 10) ≤ L ^ (-180 : ℤ) := by
  have hL0 : 0 < L := by linarith
  have hlog := Real.log_le_sub_one_of_pos hL0
  have h24 := lemma44_L24_dominates_linear hL
  calc
    _ ≤ Real.exp (-180 * Real.log L) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hlog, h24, hL0]
    _ = L ^ (-180 : ℤ) := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hL0]
      congr 1
      norm_num
      ring

noncomputable def lemma44GaussianTailTerm {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) : ℂ :=
  if ⌊lemma23PaperP D ^ 2⌋₊ < n then
    LSeries.term (fun m => lemma23NuArithmeticFunction χ m * ψ (m : ZMod N)) s n *
      (zhangGaussianWeight D (lemma44PaperGaussianScale D / n) : ℂ)
  else 0

noncomputable def lemma44InverseSquareMass : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

theorem lemma44_inverse_square_summable :
    Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
  Real.summable_nat_pow_inv.mpr (by norm_num)

theorem lemma44_gaussian_tail_term_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖lemma44GaussianTailTerm χ ψ s n‖ ≤
      lemma23PaperL D ^ (-180 : ℤ) * ((n : ℝ) ^ 2)⁻¹ := by
  unfold lemma44GaussianTailTerm
  split_ifs with hn
  · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hnne : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
    have hnu : ‖lemma23NuArithmeticFunction χ n‖ ≤ (n : ℝ) :=
      (lemma23NuArithmeticFunction_norm_le_card_divisors χ n).trans
        (by exact_mod_cast Nat.card_divisors_le_self n)
    have hcoeff : ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)‖ ≤ (n : ℝ) := by
      rw [norm_mul]
      simpa using mul_le_mul hnu (ψ.norm_le_one _) (norm_nonneg _) (by positivity)
    have hp : 1 ≤ (n : ℝ) ^ s.re :=
      Real.one_le_rpow (by exact_mod_cast Nat.one_le_of_lt hn) hs
    have ht : ‖LSeries.term
        (fun m => lemma23NuArithmeticFunction χ m * ψ (m : ZMod N)) s n‖ ≤ (n : ℝ) := by
      rw [LSeries.norm_term_eq, if_neg hnne]
      exact (div_le_self (norm_nonneg _) hp).trans hcoeff
    have hx : 0 < lemma44PaperGaussianScale D / (n : ℝ) :=
      div_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _) hnp
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zhangGaussianWeight_nonneg hD hx)]
    calc
      _ ≤ (n : ℝ) * (Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 3)⁻¹) :=
        mul_le_mul ht (lemma44_gaussian_tail_weight hL hn)
          (zhangGaussianWeight_nonneg hD hx) hnp.le
      _ = Real.exp (-(lemma23PaperL D ^ 24) / 10) * ((n : ℝ) ^ 2)⁻¹ := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (lemma44_gaussian_tail_budget hL) (by positivity)
  · simp only [norm_zero]
    positivity

/-- An absolute constant controls the infinite smoothed tail; the defining
series is proved summable before its norm is estimated. -/
theorem lemma44_gaussian_tail_summable_and_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (lemma44GaussianTailTerm χ ψ s) ∧
      ‖∑' n : ℕ, lemma44GaussianTailTerm χ ψ s n‖ ≤
        lemma44InverseSquareMass * lemma23PaperL D ^ (-180 : ℤ) := by
  have hmajor := lemma44_inverse_square_summable.mul_left
    (lemma23PaperL D ^ (-180 : ℤ))
  have hnorm : Summable (fun n : ℕ => ‖lemma44GaussianTailTerm χ ψ s n‖) :=
    hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
      (lemma44_gaussian_tail_term_bound χ ψ hD hL hs)
  refine ⟨hnorm.of_norm, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, ‖lemma44GaussianTailTerm χ ψ s n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, lemma23PaperL D ^ (-180 : ℤ) * ((n : ℝ) ^ 2)⁻¹ :=
      hnorm.tsum_le_tsum (lemma44_gaussian_tail_term_bound χ ψ hD hL hs) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

end ZhangLS.Spec
