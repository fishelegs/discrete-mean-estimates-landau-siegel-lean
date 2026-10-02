import ZhangLS.Spec.Lemma44FiniteProductShift
import ZhangLS.Spec.Lemma44MiddleContour

/-!
# The reflected infinite tail on the initial finite left contour

The reflected series has real part `3/2`. Comparing its tail with the fixed
divisor series at `5/4` extracts `P^-1/2`, independent of both characters.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped LSeries.notation

set_option maxHeartbeats 1000000

noncomputable def lemma44DivisorCoefficient : ℕ → ℂ := (1 : ℕ → ℂ) ⍟ 1

theorem lemma44_divisor_coefficient_norm (n : ℕ) :
    ‖lemma44DivisorCoefficient n‖ = ((Nat.divisors n).card : ℝ) := by
  have hcard : n.divisors.card = n.divisorsAntidiagonal.card := by
    rw [← Nat.map_div_right_divisors]
    simp
  simp [lemma44DivisorCoefficient, LSeries.convolution_def, ← hcard]

theorem lemma44_divisor_series_summable :
    LSeriesSummable lemma44DivisorCoefficient (5 / 4 : ℂ) := by
  have h : LSeriesSummable (1 : ℕ → ℂ) (5 / 4 : ℂ) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  exact h.convolution h

noncomputable def lemma44DivisorSeriesMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n‖

theorem lemma44_divisor_series_mass_nonneg : 0 ≤ lemma44DivisorSeriesMass :=
  tsum_nonneg (fun _ => norm_nonneg _)

theorem lemma44_norm_LSeries_term_eq_real_exp (c : ℕ → ℂ) (s : ℂ)
    {n : ℕ} (hn : n ≠ 0) :
    ‖LSeries.term c s n‖ = ‖c n‖ * Real.exp (-s.re * Real.log (n : ℝ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.norm_term_eq, if_neg hn, Real.rpow_def_of_pos hnp,
    div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

noncomputable def lemma44ReflectedTailTerm {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (z : ℂ) (n : ℕ) : ℂ :=
  if ⌊lemma23PaperP D ^ 2⌋₊ < n then
    LSeries.term (fun m => lemma23NuArithmeticFunction χ m * ψ (m : ZMod N)) z n
  else 0

theorem lemma44_reflected_tail_term_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.re = 3 / 2) (n : ℕ) :
    ‖lemma44ReflectedTailTerm χ ψ z n‖ ≤
      Real.exp (-(lemma23PaperL D ^ 9) / 2) *
        ‖LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n‖ := by
  unfold lemma44ReflectedTailTerm
  split_ifs with hn
  · have hnne : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
    have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hnr : lemma23PaperP D ^ 2 < (n : ℝ) :=
      (Nat.floor_lt (by positivity)).mp hn
    have hlogn : 2 * lemma23PaperL D ^ 9 ≤ Real.log (n : ℝ) := by
      have h := Real.log_le_log (pow_pos (Real.exp_pos _) 2 : 0 < lemma23PaperP D ^ 2) hnr.le
      simpa [Real.log_pow, lemma23PaperP, Real.log_exp] using h
    have hc : ‖lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)‖ ≤
        ‖lemma44DivisorCoefficient n‖ := by
      rw [norm_mul, lemma44_divisor_coefficient_norm]
      simpa using mul_le_mul (lemma23NuArithmeticFunction_norm_le_card_divisors χ n)
        (ψ.norm_le_one _) (norm_nonneg _) (by positivity)
    rw [lemma44_norm_LSeries_term_eq_real_exp _ _ hnne,
      lemma44_norm_LSeries_term_eq_real_exp _ _ hnne, hz]
    rw [show (5 / 4 : ℂ).re = (5 / 4 : ℝ) by norm_num]
    calc
      _ ≤ ‖lemma44DivisorCoefficient n‖ * Real.exp (-(3 / 2 : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = ‖lemma44DivisorCoefficient n‖ *
          (Real.exp (-Real.log (n : ℝ) / 4) * Real.exp (-(5 / 4 : ℝ) * Real.log (n : ℝ))) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        have he : Real.exp (-Real.log (n : ℝ) / 4) ≤
            Real.exp (-(lemma23PaperL D ^ 9) / 2) :=
          Real.exp_le_exp.mpr (by linarith only [hlogn])
        have hm := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right he
            (Real.exp_pos (-(5 / 4 : ℝ) * Real.log (n : ℝ))).le)
          (norm_nonneg (lemma44DivisorCoefficient n))
        nlinarith only [hm]
  · simp only [norm_zero]
    positivity

theorem lemma44_reflected_tail_summable_and_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.re = 3 / 2) :
    Summable (lemma44ReflectedTailTerm χ ψ z) ∧
      ‖∑' n : ℕ, lemma44ReflectedTailTerm χ ψ z n‖ ≤
        lemma44DivisorSeriesMass * Real.exp (-(lemma23PaperL D ^ 9) / 2) := by
  have hbase := summable_norm_iff.mpr lemma44_divisor_series_summable
  have hmajor := hbase.mul_left (Real.exp (-(lemma23PaperL D ^ 9) / 2))
  have hnorm : Summable (fun n : ℕ => ‖lemma44ReflectedTailTerm χ ψ z n‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (lemma44_reflected_tail_term_bound χ ψ hz)
  refine ⟨hnorm.of_norm, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, ‖lemma44ReflectedTailTerm χ ψ z n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, Real.exp (-(lemma23PaperL D ^ 9) / 2) *
        ‖LSeries.term lemma44DivisorCoefficient (5 / 4 : ℂ) n‖ :=
      hnorm.tsum_le_tsum (lemma44_reflected_tail_term_bound χ ψ hz) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

end ZhangLS.Spec
