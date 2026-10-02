import ZhangLS.Spec.Lemma81ZetaThreeFourOne
import ZhangLS.Spec.Lemma56ZetaLogDerivativeLocal

/-! # Unconditional real-part bounds retaining an actual zeta zero -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma81_zeta_local_zero_term_re_nonneg {t : ℝ} {z ρ : ℂ}
    (hz : 1 < z.re) (hρ : ρ ∈ lemma55ZetaLocalZeroFinset t) :
    0 ≤ ((analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (z - ρ)).re := by
  have hm := (lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ
  have hpos := lemma55_zeta_disk_re_pos (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2) hm.1
  have hzero := (lemma55_actual_zeta_pole_removed_zero_iff hpos).mpr hm.2
  have hre := lemma55_actual_zeta_pole_removed_zero_re_lt_one hzero
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.sub_re, zero_mul,
    zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Complex.normSq_nonneg _)

lemma lemma81_zeta_logDeriv_re_lower_sum {D : ℕ}
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {σ t : ℝ}
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ 2 * (D : ℝ)) :
    (∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
      ((analyticOrderNatAt zetaPoleRemoved ρ : ℂ) /
        (((σ : ℂ) + (t : ℂ) * I) - ρ)).re) -
      (1 / (((σ : ℂ) + (t : ℂ) * I) - 1)).re - 21600 * Real.log (D : ℝ) ≤
        (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hz : 1 < z.re := by simpa [z] using hσ
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  have hR : zetaPoleRemoved z ≠ 0 := by
    intro hzero
    exact hζ ((lemma55_actual_zeta_pole_removed_zero_iff (by linarith only [hz])).mp hzero)
  have hz1 : z ≠ 1 := by intro he; simp only [he, one_re] at hz; linarith
  have hdist : ‖z - lemma55JensenCenter t‖ ≤ (17 / 16 : ℝ) := by
    have he : z - lemma55JensenCenter t = ((σ - 2 : ℝ) : ℂ) := by
      dsimp [z, lemma55JensenCenter]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hσ2])]
    linarith only [hσ]
  have hb := lemma56_actual_zeta_removed_logDeriv_near_center_bound hD hL ht hdist
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm
    (logDeriv (lemma55ZetaZeroRemoved t) z)).trans hb)).1
  have he := lemma55_actual_zeta_removed_local_logDeriv_formula t
    (z := z) (by linarith only [hz]) hR
  rw [lemma55_actual_zeta_pole_removed_logDeriv (by linarith only [hz]) hz1 hζ] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.re_sum] at hre
  change (∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
      ((analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (z - ρ)).re) -
      (1 / (z - 1)).re - 21600 * Real.log (D : ℝ) ≤ (logDeriv riemannZeta z).re
  linarith only [hre, hreal]

lemma lemma81_zeta_logDeriv_re_lower {D : ℕ}
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {σ t : ℝ}
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ 2 * (D : ℝ)) :
    -(1 / (((σ : ℂ) + (t : ℂ) * I) - 1)).re - 21600 * Real.log (D : ℝ) ≤
      (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re := by
  have hb := lemma81_zeta_logDeriv_re_lower_sum hD hL hσ hσ2 ht
  have hs : 0 ≤ ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
      ((analyticOrderNatAt zetaPoleRemoved ρ : ℂ) /
        (((σ : ℂ) + (t : ℂ) * I) - ρ)).re :=
    Finset.sum_nonneg (fun ρ hρ => lemma81_zeta_local_zero_term_re_nonneg
      (by simpa using hσ) hρ)
  linarith only [hb, hs]

lemma lemma81_zeta_logDeriv_re_lower_retaining_zero {D : ℕ}
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {σ t : ℝ}
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ 2 * (D : ℝ))
    {ρ : ℂ} (hρ : ρ ∈ lemma55ZetaLocalZeroFinset t) (hρim : ρ.im = t) :
    1 / (σ - ρ.re) - (1 / (((σ : ℂ) + (t : ℂ) * I) - 1)).re -
      21600 * Real.log (D : ℝ) ≤
        (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re := by
  have hb := lemma81_zeta_logDeriv_re_lower_sum hD hL hσ hσ2 ht
  have hm := (lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ
  have hpos := lemma55_zeta_disk_re_pos (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2) hm.1
  have hzero := (lemma55_actual_zeta_pole_removed_zero_iff hpos).mpr hm.2
  have hre := lemma55_actual_zeta_pole_removed_zero_re_lt_one hzero
  have hden : 0 < σ - ρ.re := by linarith only [hσ, hre]
  have hterm : 1 / (σ - ρ.re) ≤
      ((analyticOrderNatAt zetaPoleRemoved ρ : ℂ) /
        (((σ : ℂ) + (t : ℂ) * I) - ρ)).re := by
    have he : ((σ : ℂ) + (t : ℂ) * I) - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hρim]
    rw [he, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
    apply div_le_div_of_nonneg_right _ hden.le
    exact_mod_cast lemma55_actual_zeta_local_zero_order_pos hρ
  have hs := Finset.single_le_sum
    (fun ξ hξ => lemma81_zeta_local_zero_term_re_nonneg
      (z := (σ : ℂ) + (t : ℂ) * I) (by simpa using hσ) hξ) hρ
  have hsingle : 1 / (σ - ρ.re) ≤
      ∑ ξ ∈ lemma55ZetaLocalZeroFinset t,
        ((analyticOrderNatAt zetaPoleRemoved ξ : ℂ) /
          (((σ : ℂ) + (t : ℂ) * I) - ξ)).re := hterm.trans hs
  linarith only [hb, hsingle]

lemma lemma81_zeta_pole_re_le_one {σ t : ℝ}
    (_hσ : 1 < σ) (hσ2 : σ ≤ 2) (ht : 1 ≤ |t|) :
    (1 / (((σ : ℂ) + (t : ℂ) * I) - 1)).re ≤ 1 := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hden : 0 < (σ - 1) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (σ - 1)]
  rw [one_div, Complex.inv_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    add_zero, Complex.one_re, Complex.normSq_apply, Complex.sub_im, Complex.add_im,
    Complex.mul_im, mul_one, zero_add, Complex.one_im]
  simp only [← pow_two]
  apply (div_le_one hden).mpr
  nlinarith [sq_nonneg (σ - 1)]

/-- The classical zero-detection inequality, with its actual pole terms. -/
theorem lemma81_zeta_three_four_one_zero_inequality {D : ℕ}
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {σ : ℝ}
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) {ρ : ℂ}
    (hρ : ρ ∈ lemma55ZetaLocalZeroFinset ρ.im)
    (hheight : |ρ.im| ≤ D) (hlow : 1 ≤ |ρ.im|) :
    4 / (σ - ρ.re) ≤ 3 / (σ - 1) + 172800 * Real.log (D : ℝ) + 5 := by
  have hDp : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have h0 := lemma81_zeta_logDeriv_re_lower hD hL hσ hσ2
    (t := 0) (by simp)
  have h1 := lemma81_zeta_logDeriv_re_lower_retaining_zero hD hL hσ hσ2
    (hheight.trans (by linarith)) hρ rfl
  have h2 := lemma81_zeta_logDeriv_re_lower hD hL hσ hσ2
    (t := 2 * ρ.im) (by simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left hheight (by norm_num : (0 : ℝ) ≤ 2))
  have hp1 := lemma81_zeta_pole_re_le_one hσ hσ2 hlow
  have hp2 := lemma81_zeta_pole_re_le_one hσ hσ2
    (t := 2 * ρ.im) (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
  have hcomb := lemma81_zeta_three_four_one_logDeriv_nonpos hσ ρ.im
  have hp0 : (1 / (((σ : ℂ) + (0 : ℂ) * I) - 1)).re = 1 / (σ - 1) := by
    simp only [zero_mul, add_zero]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0 hp0
  rw [hp0] at h0
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero] at hcomb
  rw [show 4 / (σ - ρ.re) = 4 * (1 / (σ - ρ.re)) by ring,
    show 3 / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  linarith only [h0, h1, h2, hp1, hp2, hcomb]

end ZhangLS.Spec
