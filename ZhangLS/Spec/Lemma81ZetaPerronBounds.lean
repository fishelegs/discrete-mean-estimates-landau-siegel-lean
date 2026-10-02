import ZhangLS.Spec.Lemma81ZetaThinStrip
import ZhangLS.Spec.Lemma56PrincipalPerronContour

/-! # Unconditional actual zeta bounds on the paper-scale Perron rectangle -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma81ZetaContourDelta (D : ℕ) : ℝ :=
  1 / (20000000 * Real.log (D : ℝ))

noncomputable def lemma81ZetaContourBound (D : ℕ) : ℝ :=
  360000000 * Real.log (D : ℝ) ^ 2 + 20021600 * Real.log (D : ℝ)

lemma lemma81_zeta_contour_delta {D : ℕ} (hL : 2000 ≤ Real.log (D : ℝ)) :
    0 < lemma81ZetaContourDelta D ∧ lemma81ZetaContourDelta D ≤ (1 / 16 : ℝ) ∧
      1 / (10000000 * Real.log (D : ℝ)) = 2 * lemma81ZetaContourDelta D := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  refine ⟨by unfold lemma81ZetaContourDelta; positivity, ?_, ?_⟩
  · unfold lemma81ZetaContourDelta
    apply (div_le_div_iff₀ (by positivity : 0 < 20000000 * Real.log (D : ℝ))
      (by norm_num)).mpr
    linarith only [hL]
  · unfold lemma81ZetaContourDelta
    ring

lemma lemma81_zeta_removed_paper_rectangle_bound {D : ℕ}
    (hD : 4 ≤ D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hfree : ∀ ρ : ℂ, 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
      |ρ.im| ≤ D → zetaPoleRemoved ρ ≠ 0) {z : ℂ}
    (hσ : 1 - lemma81ZetaContourDelta D ≤ z.re) (hσ2 : z.re ≤ 2)
    (ht : |z.im| ≤ (D : ℝ) / 2) :
    zetaPoleRemoved z ≠ 0 ∧ ‖logDeriv zetaPoleRemoved z‖ ≤
      360000000 * Real.log (D : ℝ) ^ 2 + 21600 * Real.log (D : ℝ) := by
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast hD
  have hD1 : 1 < D := by omega
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  obtain ⟨hδ, hδsmall, hwidth⟩ := lemma81_zeta_contour_delta hL
  have hne : zetaPoleRemoved z ≠ 0 := hfree z
    (by rw [hwidth]; linarith only [hσ, hδ]) (by linarith only [ht, hD4])
  refine ⟨hne, ?_⟩
  have hdist : ‖z - lemma55JensenCenter z.im‖ ≤ (17 / 16 : ℝ) := by
    rw [norm_sub_rev, lemma55_jensen_center_at_zero_height z,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hσ2] : 0 ≤ 2 - z.re)]
    linarith only [hσ, hδsmall]
  have hgap : ∀ ρ ∈ lemma55ZetaLocalZeroFinset z.im,
      lemma81ZetaContourDelta D ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hm := (lemma55_mem_actual_zeta_local_zero_finset z.im ρ).mp hρ
    have hd := mem_closedBall_iff_norm.mp hm.1
    have hi := (Complex.abs_im_le_norm (ρ - lemma55JensenCenter z.im)).trans hd
    norm_num [lemma55JensenCenter, Complex.mul_im] at hi
    have htri := abs_add_le (ρ.im - z.im) z.im
    rw [sub_add_cancel] at htri
    have hheight : |ρ.im| ≤ D := by linarith only [hi, htri, ht, hD4]
    have hzero := (lemma55_actual_zeta_pole_removed_zero_iff
      (lemma55_zeta_disk_re_pos (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2) hm.1)).mpr hm.2
    have hre : ρ.re ≤ 1 - 2 * lemma81ZetaContourDelta D := by
      apply le_of_not_gt
      intro hn
      exact hfree ρ (by rwa [hwidth]) hheight hzero
    have hr := Complex.re_le_norm (z - ρ)
    rw [Complex.sub_re] at hr
    linarith only [hr, hre, hσ]
  have hb := lemma56_actual_zeta_logDeriv_bound_of_local_zero_gap hD1 hL
    (by linarith only [ht, hD4] : |z.im| ≤ 2 * (D : ℝ)) hδ hdist hne hgap
  apply hb.trans_eq
  unfold lemma81ZetaContourDelta
  field_simp [hLp.ne']
  ring

lemma lemma81_zeta_logDeriv_norm_from_removed {z : ℂ} (hz : 0 < z.re)
    (hz1 : z ≠ 1) (hR : zetaPoleRemoved z ≠ 0) {A R : ℝ}
    (ha : ‖logDeriv zetaPoleRemoved z‖ ≤ A) (hr : ‖1 / (z - 1)‖ ≤ R) :
    ‖logDeriv riemannZeta z‖ ≤ A + R := by
  have hζ : riemannZeta z ≠ 0 := by
    intro hh
    exact hR ((lemma55_actual_zeta_pole_removed_zero_iff hz).mpr hh)
  have he : logDeriv riemannZeta z = logDeriv zetaPoleRemoved z - 1 / (z - 1) := by
    rw [lemma55_actual_zeta_pole_removed_logDeriv hz hz1 hζ]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add ha hr)

lemma lemma81_zeta_paper_left_bound {D : ℕ}
    (hD : 4 ≤ D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hfree : ∀ ρ : ℂ, 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
      |ρ.im| ≤ D → zetaPoleRemoved ρ ≠ 0) {t : ℝ} (ht : |t| ≤ (D : ℝ) / 2) :
    ‖logDeriv riemannZeta (((1 - lemma81ZetaContourDelta D : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      lemma81ZetaContourBound D := by
  let z : ℂ := ((1 - lemma81ZetaContourDelta D : ℝ) : ℂ) + (t : ℂ) * I
  obtain ⟨hδ, hsmall, _⟩ := lemma81_zeta_contour_delta hL
  have hzpos : 0 < z.re := by dsimp [z]; simp only [ofReal_re, mul_re, ofReal_im, I_re, I_im]; linarith
  have hz1 : z ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp [z] at hh
    linarith only [hh, hδ]
  have hzre : 1 - lemma81ZetaContourDelta D ≤ z.re := by simp [z]
  have hz2 : z.re ≤ 2 := by simp [z]; linarith only [hδ]
  have hzt : |z.im| ≤ (D : ℝ) / 2 := by simpa [z] using ht
  obtain ⟨hR, hb⟩ := lemma81_zeta_removed_paper_rectangle_bound hD hL hfree hzre hz2 hzt
  have hnorm : lemma81ZetaContourDelta D ≤ ‖z - 1‖ := by
    have hh := Complex.re_le_norm (1 - z)
    have he : (1 - z).re = lemma81ZetaContourDelta D := by simp [z]
    rw [he, norm_sub_rev] at hh
    exact hh
  have hpole : ‖1 / (z - 1)‖ ≤ 1 / lemma81ZetaContourDelta D := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num) hδ hnorm
  apply (lemma81_zeta_logDeriv_norm_from_removed hzpos hz1 hR hb hpole).trans_eq
  unfold lemma81ZetaContourBound lemma81ZetaContourDelta
  field_simp
  ring

lemma lemma81_zeta_paper_horizontal_bound {D : ℕ}
    (hD : 4 ≤ D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hfree : ∀ ρ : ℂ, 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
      |ρ.im| ≤ D → zetaPoleRemoved ρ ≠ 0) {σ t : ℝ}
    (hσ : 1 - lemma81ZetaContourDelta D ≤ σ) (hσ2 : σ ≤ 2)
    (ht : |t| = (D : ℝ) / 2) :
    ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ lemma81ZetaContourBound D := by
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast hD
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  obtain ⟨_hδ, hsmall, _⟩ := lemma81_zeta_contour_delta hL
  have hzpos : 0 < z.re := by simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; linarith
  have hheight : 1 ≤ |z.im| := by simp [z, ht]; linarith only [hD4]
  have hz1 : z ≠ 1 := by intro he; norm_num [he] at hheight
  have hzre : 1 - lemma81ZetaContourDelta D ≤ z.re := by simpa [z] using hσ
  have hz2 : z.re ≤ 2 := by simpa [z] using hσ2
  have hzt : |z.im| ≤ (D : ℝ) / 2 := by simp [z, ht]
  obtain ⟨hR, hb⟩ := lemma81_zeta_removed_paper_rectangle_bound hD hL hfree hzre hz2 hzt
  have hnorm : 1 ≤ ‖z - 1‖ := hheight.trans (by simpa using Complex.abs_im_le_norm (z - 1))
  have hpole : ‖1 / (z - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith only [hnorm] : 0 < ‖z - 1‖)).mpr hnorm
  apply (lemma81_zeta_logDeriv_norm_from_removed hzpos hz1 hR hb hpole).trans
  unfold lemma81ZetaContourBound
  linarith only [hL]

end ZhangLS.Spec
