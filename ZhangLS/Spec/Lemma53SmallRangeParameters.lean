import ZhangLS.Spec.Lemma53StationaryContour

/-! # Deriving stationary-contour smallness from the original small-x range

The integer majorant L^530 avoids weakening the original upper endpoint.
It gives a uniform perturbation bound 1305/L^10, smaller than alpha when
L >= 2000. No contour smallness is assumed in the final specialization.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma53_small_range_power_bound {D : ℕ} (hL : 1 ≤ lemma23PaperL D)
    {x : ℝ} (hx : x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ)) :
    x ≤ lemma23PaperL D ^ 530 := by
  apply hx.trans
  unfold lemma51PaperT0
  rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ lemma23PaperL D), ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem lemma53_small_contour_radius_bound {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 ≤ x)
    (hxhi : x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ)) :
    lemma53ContourRadius D x (lemma53SmallRadius D) ≤ 9 / lemma23PaperL D ^ 270 := by
  let L := lemma23PaperL D
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hx530 : x ≤ L ^ 530 := lemma53_small_range_power_bound hL hxhi
  have ht530 : lemma51PaperT0 D ≤ L ^ 530 :=
    pow_le_pow_right₀ hL (by norm_num : 519 ≤ 530)
  have ht0 : 0 ≤ lemma51PaperT0 D := pow_nonneg hLp.le _
  have hd : |lemma51PaperT0 D - x| ≤ 2 * L ^ 530 := by
    rw [abs_le]
    constructor <;> linarith
  have hv : |lemma53StationaryHeight D x| ≤ 8 / L ^ 270 := by
    unfold lemma53StationaryHeight
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg (sq_nonneg (lemma53PaperScale D))]
    apply (div_le_iff₀ (sq_pos_of_pos (lemma53_scale_pos hD))).mpr
    have hm := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
    have hπ := mul_le_mul_of_nonneg_right Real.pi_le_four (show 0 ≤ 2 * L ^ 530 by positivity)
    have he : (8 / L ^ 270) * lemma53PaperScale D ^ 2 = 8 * L ^ 530 := by
      change (8 / L ^ 270) * (L ^ 400) ^ 2 = 8 * L ^ 530
      field_simp [hLp.ne']
    rw [he]
    linarith
  have hr : lemma53SmallRadius D ≤ 1 / L ^ 270 := by
    unfold lemma53SmallRadius
    change L ^ 5 / L ^ 400 ≤ 1 / L ^ 270
    have hpow : L ^ 275 ≤ L ^ 400 := pow_le_pow_right₀ hL (by norm_num)
    apply (div_le_div_iff₀ (pow_pos hLp 400) (pow_pos hLp 270)).mpr
    simpa only [one_mul, ← pow_add] using hpow
  unfold lemma53ContourRadius
  calc
    _ ≤ 1 / L ^ 270 + 8 / L ^ 270 := add_le_add hr hv
    _ = _ := by ring

theorem lemma53_small_contour_error_bound {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 ≤ x)
    (hxhi : x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ)) :
    lemma53ContourErrorBound D x (lemma53SmallRadius D) ≤ 1305 / lemma23PaperL D ^ 10 := by
  let L := lemma23PaperL D
  let R := lemma53ContourRadius D x (lemma53SmallRadius D)
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr : 0 ≤ lemma53SmallRadius D := by
    unfold lemma53SmallRadius
    have := lemma53_scale_pos hD
    positivity
  have hR0 : 0 ≤ R := by dsimp [R, lemma53ContourRadius]; positivity
  have hR : R ≤ 9 / L ^ 270 := lemma53_small_contour_radius_bound hD hL hx hxhi
  have hx530 : x ≤ L ^ 530 := lemma53_small_range_power_bound hL hxhi
  have hs : R ^ 2 ≤ (9 / L ^ 270) ^ 2 := pow_le_pow_left₀ hR0 hR 2
  have hm : 4 * Real.pi * x * R ^ 2 ≤
      16 * L ^ 530 * (9 / L ^ 270) ^ 2 := by
    apply mul_le_mul
      (mul_le_mul (by nlinarith [Real.pi_le_four]) hx530 hx (by norm_num)) hs
      (sq_nonneg _) (by positivity)
  have he : 16 * L ^ 530 * (9 / L ^ 270) ^ 2 = 1296 / L ^ 10 := by
    field_simp [hLp.ne']
    ring
  have hpow : L ^ 10 ≤ L ^ 270 := pow_le_pow_right₀ hL (by norm_num)
  have hdiv : 9 / L ^ 270 ≤ 9 / L ^ 10 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLp 10) hpow
  rw [he] at hm
  change R + 4 * Real.pi * x * R ^ 2 ≤ 1305 / L ^ 10
  calc
    _ ≤ 9 / L ^ 10 + 1296 / L ^ 10 := add_le_add (hR.trans hdiv) hm
    _ = _ := by ring

theorem lemma53_small_contour_error_le_alpha {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 ≤ x)
    (hxhi : x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ)) :
    lemma53ContourErrorBound D x (lemma53SmallRadius D) ≤ lemma44PaperAlpha D ∧
      lemma44PaperAlpha D ≤ 1 := by
  let L := lemma23PaperL D
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have ha : lemma44PaperAlpha D = Real.pi / L ^ 9 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
  constructor
  · apply (lemma53_small_contour_error_bound hD hL1 hx hxhi).trans
    rw [ha]
    apply (div_le_div_iff₀ (pow_pos hLp 10) (pow_pos hLp 9)).mpr
    rw [show L ^ 10 = L ^ 9 * L by ring]
    have hconst : 1305 ≤ Real.pi * L := by nlinarith [Real.two_le_pi]
    nlinarith [mul_le_mul_of_nonneg_right hconst (pow_pos hLp 9).le]
  · rw [ha]
    apply (div_le_one (pow_pos hLp 9)).mpr
    have hp : L ≤ L ^ 9 := le_self_pow₀ hL1 (by norm_num)
    linarith [Real.pi_le_four]

end ZhangLS.Spec
