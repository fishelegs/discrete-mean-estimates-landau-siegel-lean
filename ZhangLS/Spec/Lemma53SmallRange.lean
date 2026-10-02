import ZhangLS.Spec.Lemma53SmallRangeParameters

/-! # The complete original small-x estimate in Lemma 5.3 -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma53SmallErrorConstant : ℝ := 4 * (Real.exp 1 + 1) + 2

theorem lemma53_error_central_bound {D : ℕ} (hD : 1 < D) {x r : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ r) (hη : lemma53ContourErrorBound D x r ≤ 1) :
    ‖∫ u : ℝ in -r..r, lemma53ErrorKernel D x (u : ℂ)‖ ≤
      lemma53ContourErrorBound D x r *
        ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
          2 * Real.exp (-(lemma53PaperScale D ^ 2 * r ^ 2)) := by
  have hη0 := lemma53_contour_error_nonneg D hx hr
  have hV : |lemma53StationaryHeight D x| ≤ 1 := by
    have hR : |lemma53StationaryHeight D x| ≤ lemma53ContourRadius D x r := by
      unfold lemma53ContourRadius
      linarith
    exact hR.trans ((lemma53_contour_radius_le_error D hx).trans hη)
  have hprod : lemma53ContourErrorBound D x r * |lemma53StationaryHeight D x| ≤ 1 := by
    nlinarith [mul_le_mul hη hV (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hleft := lemma53_error_vertical_bound hD hx hr
    (u := -r) (by simpa [abs_of_nonneg hr]) hη
  have hright := lemma53_error_vertical_bound hD hx hr
    (u := r) (by rw [abs_of_nonneg hr]) hη
  have hleft' : ‖I * (∫ v : ℝ in 0..lemma53StationaryHeight D x,
      lemma53ErrorKernel D x ((-r : ℝ) + (v : ℂ) * I))‖ ≤
        Real.exp (-(lemma53PaperScale D ^ 2 * r ^ 2)) := by
    rw [norm_mul, norm_I, one_mul]
    apply hleft.trans
    rw [neg_sq]
    have hh := mul_le_mul_of_nonneg_right hprod
      (Real.exp_pos (-(lemma53PaperScale D ^ 2 * r ^ 2))).le
    nlinarith only [hh]
  have hright' : ‖I * (∫ v : ℝ in 0..lemma53StationaryHeight D x,
      lemma53ErrorKernel D x ((r : ℂ) + (v : ℂ) * I))‖ ≤
        Real.exp (-(lemma53PaperScale D ^ 2 * r ^ 2)) := by
    rw [norm_mul, norm_I, one_mul]
    apply hright.trans
    have hh := mul_le_mul_of_nonneg_right hprod
      (Real.exp_pos (-(lemma53PaperScale D ^ 2 * r ^ 2))).le
    nlinarith only [hh]
  rw [lemma53_error_rectangle_shift D x (-r) r (lemma53StationaryHeight D x)]
  apply (norm_sub_le _ _).trans
  have hmid := lemma53_error_stationary_middle_bound hD hx hr hη
  have hn := norm_add_le
    (∫ u : ℝ in -r..r,
      lemma53ErrorKernel D x ((u : ℂ) + (lemma53StationaryHeight D x : ℂ) * I))
    (I * (∫ y : ℝ in 0..lemma53StationaryHeight D x,
      lemma53ErrorKernel D x ((-r : ℝ) + (y : ℂ) * I)))
  nlinarith only [hn, hmid, hleft', hright']

theorem lemma53_small_range_estimate {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x)
    (hxhi : x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ)) :
    ‖lemma53PaperDelta D x -
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ ≤
        lemma44PaperAlpha D *
          ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
            lemma53SmallErrorConstant * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hr : 0 ≤ lemma53SmallRadius D := by
    unfold lemma53SmallRadius
    have := lemma53_scale_pos hD
    have : 0 < lemma23PaperL D := by linarith
    positivity
  have hη := lemma53_small_contour_error_le_alpha hD hL hx.le hxhi
  have hc := lemma53_error_central_bound hD hx.le hr (hη.1.trans hη.2)
  have ht := lemma53_small_radius_tail hD hL1 hx
  rw [lemma53_small_radius_scale hD] at hc
  have hmid : ‖∫ u : ℝ in -lemma53SmallRadius D..lemma53SmallRadius D,
      lemma53ErrorKernel D x (u : ℂ)‖ ≤
      lemma44PaperAlpha D *
        ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
          2 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
    apply hc.trans
    have hh := mul_le_mul_of_nonneg_right hη.1 (norm_nonneg
      (lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))))
    have he : Real.exp (-(lemma23PaperL D ^ 10)) ≤ Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ lemma23PaperL D ^ 10 := pow_nonneg (by linarith) _
      linarith
    nlinarith
  let E := lemma53PaperDelta D x -
    lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))
  let M := ∫ u : ℝ in -lemma53SmallRadius D..lemma53SmallRadius D,
    lemma53ErrorKernel D x (u : ℂ)
  have hn : ‖E‖ ≤ ‖E - M‖ + ‖M‖ := by
    have hh := norm_add_le (E - M) M
    simpa only [sub_add_cancel] using hh
  unfold lemma53SmallErrorConstant
  change ‖E‖ ≤ _
  change ‖E - M‖ ≤ _ at ht
  change ‖M‖ ≤ _ at hmid
  nlinarith only [hn, ht, hmid]

theorem lemma53_small_range_uniform_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ x : ℝ, 0 < x →
      x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) →
      ‖lemma53PaperDelta D x -
        lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ ≤
        lemma53SmallErrorConstant * lemma44PaperAlpha D *
          ‖lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))‖ +
            lemma53SmallErrorConstant * Real.exp (-(1 / 2 : ℝ) * lemma23PaperL D ^ 10) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 2000))
  refine ⟨max N 2, ?_⟩
  intro D hD x hx hxhi
  have hD' : 1 < D := lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right N 2).trans hD)
  have hL := hN D ((le_max_left N 2).trans hD)
  have he := lemma53_small_range_estimate hD' hL hx hxhi
  apply he.trans
  have hC : 1 ≤ lemma53SmallErrorConstant := by
    unfold lemma53SmallErrorConstant
    have hh := Real.exp_pos 1
    linarith
  have ha : 0 ≤ lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity
  have hh := mul_le_mul_of_nonneg_right hC
    (mul_nonneg ha (norm_nonneg
      (lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)))))
  have hex : -(lemma23PaperL D ^ 10) / 2 = -(1 / 2 : ℝ) * lemma23PaperL D ^ 10 := by ring
  rw [hex] at he ⊢
  nlinarith only [hh]

end ZhangLS.Spec
