import ZhangLS.Spec.Lemma32MellinTerms
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_Gamma_mellin_term_eq_kernel (c : ℕ → ℂ) (B : ℝ) (hB : 0 < B)
    (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    lemma32GammaMellinTerm c B n t = LSeries.term c 1 n*
      (((n/B : ℝ) : ℂ)^(-(1+(t : ℂ)*I))*Complex.Gamma (1+(t : ℂ)*I)) := by
  let w : ℂ := 1+(t : ℂ)*I
  have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hx : 0 < (n : ℝ)/B := div_pos hnp hB
  have hlog : Complex.log (((n : ℝ)/B : ℝ) : ℂ) =
      (Real.log (n : ℝ) : ℂ)-(Real.log B : ℂ) := by
    rw [← Complex.ofReal_log hx.le,Real.log_div hnp.ne' hB.ne',Complex.ofReal_sub]
  have hnlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hnp.le).symm
  have hpow : Complex.exp (w*(Real.log B : ℂ))/(n : ℂ)^w =
      (((n : ℝ)/B : ℝ) : ℂ)^(-w) := by
    rw [Complex.cpow_def_of_ne_zero hnC,hnlog,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),hlog,← Complex.exp_sub]
    congr 1
    ring
  unfold lemma32GammaMellinTerm
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
  rw [show (2 : ℂ)+(t : ℂ)*I = 1+w by dsimp [w]; ring]
  change c n/(n : ℂ)^(1+w)*Complex.exp (w*(Real.log B : ℂ))*Complex.Gamma w =
    (c n/(n : ℂ)^1)*((((n : ℝ)/B : ℝ) : ℂ)^(-w)*Complex.Gamma w)
  rw [← hpow,Complex.cpow_add _ _ hnC,Complex.cpow_one]
  ring

lemma lemma32_Gamma_mellin_term_normalized_integral (c : ℕ → ℂ) (B : ℝ) (hB : 0 < B) (n : ℕ) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, lemma32GammaMellinTerm c B n t) =
      LSeries.term c 1 n*(Real.exp (-(n : ℝ)/B) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [lemma32GammaMellinTerm]
  have hx : 0 < (n : ℝ)/B := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hB
  simp_rw [lemma32_Gamma_mellin_term_eq_kernel c B hB n hn,integral_const_mul]
  calc
    _ = LSeries.term c 1 n*mellinInv 1 Complex.Gamma ((n : ℝ)/B) := by
      unfold mellinInv
      simp only [Complex.real_smul,smul_eq_mul,Complex.ofReal_one]
      ring
    _ = _ := by rw [lemma32_actual_Gamma_mellin_inversion _ hx]; congr 2; ring

end ZhangLS.Spec
