import ZhangLS.Spec.Lemma56PrimeMassBounds


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_paper_prime_log_upper {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    1 ≤ Real.log (lemma56PrimeUpper D) ∧
      Real.log (lemma56PrimeUpper D) ≤ 2 * lemma23PaperL D ^ 9 := by
  have hp := lemma56_paper_prime_weight_parameters hL
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hlow := hp.1.trans (Real.log_le_log hP hp.2.2.1)
  have hhigh := Real.log_le_log (hP.trans_le hp.2.2.1)
    (by linarith only [hp.2.2.2.1] : lemma56PrimeUpper D ≤ 2 * lemma23PaperP D)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP.ne', lemma23PaperP, Real.log_exp] at hhigh
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hL9 : 1 ≤ lemma23PaperL D ^ 9 := by
    simpa only [lemma23PaperP, Real.log_exp] using hp.1
  exact ⟨hlow, by linarith only [hhigh, hlog2, hL9]⟩

lemma lemma56_actual_prime_mass_log_reduction {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {c : ℝ} (hlogmass : c * lemma23PaperP D / lemma23PaperL D ^ 68 ≤
      lemma56PaperPrimeLogMass D) :
    (c / 2) * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤ lemma56PrimeMass D := by
  have hy := lemma56_paper_prime_log_upper hL
  have hY0 : 0 ≤ lemma56PrimeUpper D := (Real.exp_pos _).le.trans
    (lemma56_paper_prime_weight_parameters hL).2.2.1
  have hY : 1 < lemma56PrimeUpper D :=
    (Real.log_pos_iff hY0).mp (by linarith only [hy.1])
  have hm := lemma56_actual_prime_mass_from_logmass hY
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hL0 : 0 < lemma23PaperL D := by linarith only [hL]
  have hlogmass0 := lemma56_paper_prime_log_mass_nonneg D
  have hratio : lemma23PaperP D / (2 * lemma23PaperL D ^ 9) ≤
      lemma23PaperP D / Real.log (lemma56PrimeUpper D) :=
    div_le_div_of_nonneg_left hP.le (by linarith only [hy.1]) hy.2
  have hfirst := mul_le_mul_of_nonneg_right hratio hlogmass0
  have hsecond := mul_le_mul_of_nonneg_left hlogmass
    (by positivity : 0 ≤ lemma23PaperP D / (2 * lemma23PaperL D ^ 9))
  have heq : (c / 2) * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 =
      (lemma23PaperP D / (2 * lemma23PaperL D ^ 9)) *
        (c * lemma23PaperP D / lemma23PaperL D ^ 68) := by
    rw [show lemma23PaperL D ^ 77 = lemma23PaperL D ^ 9 * lemma23PaperL D ^ 68 by
      rw [← pow_add]]
    field_simp
  rw [heq]
  exact hsecond.trans (hfirst.trans hm)

end ZhangLS.Spec
