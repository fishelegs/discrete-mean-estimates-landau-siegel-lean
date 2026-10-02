import ZhangLS.Spec.Lemma56GaussianPhaseTerms
import ZhangLS.Spec.Lemma55ZetaLocalData

/-! # Unconditional 3–4–1 positivity for the actual Riemann zeta function

A new bounded seam for the unconditional prime-mass normalization in Lemma 8.1.
No Assumption (A), prime asymptotic, or zero-free-region hypothesis occurs.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex LSeries
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma81_three_four_one_phase_nonneg {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ 3 + 4 * u.re + (u ^ 2).re := by
  have hnorm := Complex.sq_norm_sub_sq_re u
  rw [hu] at hnorm
  rw [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (1 + u.re)]

lemma lemma81_three_four_one_mangoldt_term_nonneg (σ t : ℝ) (n : ℕ) :
    let f : ℕ → ℂ := fun m => (ArithmeticFunction.vonMangoldt m : ℂ)
    0 ≤ ((3 : ℂ) * LSeries.term f (σ : ℂ) n +
      4 * LSeries.term f ((σ : ℂ) + (t : ℂ) * I) n +
        LSeries.term f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  dsimp only
  let f : ℕ → ℂ := fun m => (ArithmeticFunction.vonMangoldt m : ℂ)
  by_cases hn : n = 0
  · subst n
    simp
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  let b := LSeries.term f (σ : ℂ) n
  let u := lemma56GaussianPhase (-t) n
  have hb : 0 ≤ b := LSeries.term_nonneg
    (Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg) σ
  have hbr : 0 ≤ b.re := (Complex.nonneg_iff.mp hb).1
  have hbi : b.im = 0 := (Complex.nonneg_iff.mp hb).2.symm
  have hu : ‖u‖ = 1 := lemma56_gaussian_phase_norm hn (-t)
  have hp := lemma81_three_four_one_phase_nonneg hu
  have h1 : LSeries.term f ((σ : ℂ) + (t : ℂ) * I) n = u * b := by
    have he := lemma56_gaussian_phase_LSeries_term f (σ : ℂ) (-t) n
    simpa only [u, b, Complex.ofReal_neg, neg_mul, sub_neg_eq_add] using he.symm
  have hphase : lemma56GaussianPhase (-(2 * t)) n = u ^ 2 := by
    dsimp [lemma56GaussianPhase, u]
    rw [pow_two, ← Complex.cpow_add _ _ hnC]
    congr 1
    push_cast
    ring
  have h2 : LSeries.term f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n = u ^ 2 * b := by
    have he := lemma56_gaussian_phase_LSeries_term f (σ : ℂ) (-(2 * t)) n
    rw [hphase] at he
    simpa only [b, Complex.ofReal_neg, neg_mul, sub_neg_eq_add] using he.symm
  change 0 ≤ ((3 : ℂ) * b +
    4 * LSeries.term f ((σ : ℂ) + (t : ℂ) * I) n +
      LSeries.term f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re
  rw [h1, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    hbi, mul_zero, zero_mul, sub_zero]
  nlinarith [mul_nonneg hbr hp]

/-- The actual logarithmic-derivative positivity inequality on Re s > 1. -/
theorem lemma81_zeta_three_four_one_logDeriv_nonpos {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    ((3 : ℂ) * logDeriv riemannZeta (σ : ℂ) +
      4 * logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) +
        logDeriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤ 0 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs0 : LSeriesSummable f (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hs1 : LSeriesSummable f ((σ : ℂ) + (t : ℂ) * I) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hs2 : LSeriesSummable f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have h0 := hs0.mul_left (3 : ℂ)
  have h1 := hs1.mul_left (4 : ℂ)
  have hsum : 0 ≤ ((3 : ℂ) * LSeries f (σ : ℂ) +
      4 * LSeries f ((σ : ℂ) + (t : ℂ) * I) +
        LSeries f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
    have he : (∑' n : ℕ, ((3 : ℂ) * LSeries.term f (σ : ℂ) n +
        4 * LSeries.term f ((σ : ℂ) + (t : ℂ) * I) n +
          LSeries.term f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n)) =
        (3 : ℂ) * LSeries f (σ : ℂ) +
          4 * LSeries f ((σ : ℂ) + (t : ℂ) * I) +
            LSeries f ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by
      rw [(h0.add h1).tsum_add hs2, h0.tsum_add h1, tsum_mul_left, tsum_mul_left]
      rfl
    rw [← he, Complex.re_tsum ((h0.add h1).add hs2)]
    exact tsum_nonneg (fun n => lemma81_three_four_one_mangoldt_term_nonneg σ t n)
  have hlog (z : ℂ) (hz : 1 < z.re) : LSeries f z = -logDeriv riemannZeta z := by
    simpa only [f, logDeriv_apply, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  rw [hlog _ (by simpa using hσ), hlog _ (by simpa using hσ),
    hlog _ (by simpa using hσ)] at hsum
  have he : (3 : ℂ) * (-logDeriv riemannZeta (σ : ℂ)) +
      4 * (-logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)) +
        (-logDeriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)) =
      -((3 : ℂ) * logDeriv riemannZeta (σ : ℂ) +
        4 * logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) +
          logDeriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)) := by ring
  rw [he, Complex.neg_re] at hsum
  linarith

end ZhangLS.Spec
