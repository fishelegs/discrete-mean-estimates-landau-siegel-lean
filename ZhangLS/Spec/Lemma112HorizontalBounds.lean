import ZhangLS.Spec.Lemma112ReciprocalBounds
import ZhangLS.Spec.Lemma112ErrorFloor
/-! # Actual full-L and Z-error horizontal edges for the variable cutoff -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_scale_log_bounds {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    0 ≤ Real.log (lemma23PaperP D ^ z) ∧
      Real.log (lemma23PaperP D ^ z) ≤ lemma23PaperL D ^ 9 := by
  rw [lemma23PaperP, Real.log_rpow (Real.exp_pos _), Real.log_exp]
  have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
  constructor
  · exact mul_nonneg (by linarith [hz.1]) hp
  · exact mul_le_of_le_one_left hp (by linarith [hz.2])

lemma lemma112_dual_scale_log_bounds {D : ℕ} (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    0 ≤ Real.log (lemma112DualScale D z) ∧
      Real.log (lemma112DualScale D z) ≤ lemma23PaperL D ^ 9 := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hDr : (0 : ℝ) < D := by exact_mod_cast lt_trans Nat.zero_lt_one hD
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have hT : 0 < lemma51PaperT0 D := pow_pos (by linarith : 0 < lemma23PaperL D) _
  constructor
  · unfold lemma112DualScale
    rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos hP _) hDr).ne' hT.ne',
      Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hDr.ne', Real.log_rpow hP,
      lemma23PaperP, Real.log_exp]
    exact add_nonneg (add_nonneg (mul_nonneg (by linarith [hz.2]) (by positivity))
      (Real.log_nonneg (by exact_mod_cast hD.le)))
      (Real.log_nonneg (one_le_pow₀ h1))
  · exact (lemma112_dual_scale_cutoff_gap hD hL hz.1).1.trans
      (by
        have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
        linarith only [hp])

lemma lemma112_scale_exponential_rectangle_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) {w : ℂ} (hw : w.re ≤ 2) :
    ‖exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ ≤ Real.exp (2 * lemma23PaperL D ^ 9) := by
  rw [norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  have hlog := lemma112_scale_log_bounds hL hz
  have hm := mul_le_mul_of_nonneg_right hw hlog.1
  linarith only [hm, hlog.2]

lemma lemma112_dual_scale_left_bound {D : ℕ} (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) {u : ℝ} (hu : -1 ≤ u) :
    Real.exp (-u * Real.log (lemma112DualScale D z)) ≤ Real.exp (lemma23PaperL D ^ 9) := by
  apply Real.exp_le_exp.mpr
  have hlog := lemma112_dual_scale_log_bounds hD hL hz
  have hm := mul_le_mul_of_nonneg_right (show -u ≤ 1 by linarith only [hu]) hlog.1
  linarith only [hm, hlog.2]

lemma lemma112_twist_modulus_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    ((D * p : ℕ) : ℝ) ≤ Real.exp (2 * lemma23PaperL D ^ 9) := by
  have hlog := (lemma51_family_conductor_logs χ ψ hL hψ).2
  exact Real.le_exp_of_log_le hlog

lemma lemma112_actual_L_scale_rectangle_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s w : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ ≤
      68 * Real.exp 1 * lemma23PaperL D ^ 519 * Real.exp (4 * lemma23PaperL D ^ 9) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have h0 : 0 < lemma23PaperL D := by linarith
  have hL3 : 3 ≤ lemma23PaperL D := by linarith
  have h61 := lemma112_region_subset_lemma61 hL3 hs
  have hnorm := lemma61_shifted_argument_norm_bounds hL3 h61 hwr hwi
  have hmod := lemma112_twist_modulus_bound χ ψ hL3 hψ
  have htw := lemma112_twist_family_data χ ψ hL3 hψ
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  by_cases hre : 1 / 4 ≤ (s + w).re
  · have hF := lemma61_actual_L_quarter_plane_bound (lemma44CharacterTwist χ ψ) htw.2.2.2 hre
    have hFb : ‖DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w)‖ ≤
        64 * Real.exp (2 * lemma23PaperL D ^ 9) * lemma23PaperL D ^ 519 := by
      apply hF.trans
      calc
        _ ≤ (4 * Real.exp (2 * lemma23PaperL D ^ 9)) * (16 * lemma23PaperL D ^ 519) := by
          gcongr
          exact hnorm.1
        _ = _ := by ring
    rw [norm_mul]
    calc
      _ ≤ (64 * Real.exp (2 * lemma23PaperL D ^ 9) * lemma23PaperL D ^ 519) *
          Real.exp (2 * lemma23PaperL D ^ 9) := by
        gcongr
        exact lemma112_scale_exponential_rectangle_bound hL3 hz hwr.2
      _ = 64 * lemma23PaperL D ^ 519 * Real.exp (4 * lemma23PaperL D ^ 9) := by
        rw [show 4 * lemma23PaperL D ^ 9 = 2 * lemma23PaperL D ^ 9 + 2 * lemma23PaperL D ^ 9 by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [he1] : (64 : ℝ) ≤ 68 * Real.exp 1) (by positivity)) (Real.exp_nonneg _)
  · have hri : 1 / 4 ≤ (1 - (s + w)).re := by simp only [sub_re, one_re]; linarith only [hre]
    have hF := lemma61_actual_L_quarter_plane_bound (lemma44CharacterTwist χ ψ)⁻¹
      (inv_ne_one.mpr htw.2.2.2) hri
    have hFb : ‖DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ⁻¹) (1 - (s + w))‖ ≤
        68 * Real.exp (2 * lemma23PaperL D ^ 9) * lemma23PaperL D ^ 519 := by
      rw [lemma44CharacterTwist_inv] at hF
      apply hF.trans
      calc
        _ ≤ (4 * Real.exp (2 * lemma23PaperL D ^ 9)) * (17 * lemma23PaperL D ^ 519) := by
          gcongr
          exact hnorm.2
        _ = _ := by ring
    have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := ⟨by linarith only [h9,hwr.1],hwr.2⟩
    have hd := lemma61_large_shift_rectangle_bounds hL3 h61 hwide hwi
    have him : 0 < (s + w).im := by linarith only [(lemma61_wide_height_data hL3 hd.2.1).2.1]
    have hZ := (lemma112_twist_Z_scale_cancellation χ ψ hψ hD hL3 hs hwide hwi z).trans
      (mul_le_mul_of_nonneg_left (lemma112_dual_scale_left_bound hD hL hz hwr.1) (Real.exp_nonneg _))
    rw [lemma112_actual_twist_functional_equation χ ψ hL3 hψ him]
    calc
      _ = ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) *
          exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ *
          ‖DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ⁻¹) (1 - (s + w))‖ := by
        simp only [norm_mul]; ring
      _ ≤ (Real.exp 1 * Real.exp (lemma23PaperL D ^ 9)) *
          (68 * Real.exp (2 * lemma23PaperL D ^ 9) * lemma23PaperL D ^ 519) := by gcongr
      _ = 68 * Real.exp 1 * lemma23PaperL D ^ 519 * Real.exp (3 * lemma23PaperL D ^ 9) := by
        rw [show 3 * lemma23PaperL D ^ 9 = lemma23PaperL D ^ 9 + 2 * lemma23PaperL D ^ 9 by ring, Real.exp_add]
        ring
      _ ≤ _ := by
        gcongr
        have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
        linarith only [hp]

lemma lemma112_actual_horizontal_L_integral_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ))
    {t : ℝ} (ht : |t| = lemma23PaperL D ^ 20) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x : ℝ in (-1 : ℝ)..2,
      lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s
        (lemma23PaperP D ^ z) ((x : ℂ) + (t : ℂ) * I) / ((x : ℂ) + (t : ℂ) * I))‖ ≤
      204 * Real.exp 2 * Real.exp (-(lemma23PaperL D ^ 10) / 8) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have h0 : 0 < lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ h1
  have h20 : 1 ≤ lemma23PaperL D ^ 20 := one_le_pow₀ h1
  have hp : ∀ x ∈ uIoc (-1 : ℝ) 2,
      ‖lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s
        (lemma23PaperP D ^ z) ((x : ℂ) + (t : ℂ) * I) / ((x : ℂ) + (t : ℂ) * I)‖ ≤
      68 * Real.exp 2 * lemma23PaperL D ^ 519 *
        Real.exp (4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4) := by
    intro x hx
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
    let w : ℂ := (x : ℂ) + (t : ℂ) * I
    have hwr : -1 ≤ w.re ∧ w.re ≤ 2 := by simpa [w] using And.intro hx.1.le hx.2
    have hwi : |w.im| = lemma23PaperL D ^ 20 := by simpa [w] using ht
    have hF := lemma112_actual_L_scale_rectangle_bound χ ψ hψ hD hL hs hwr hwi.le hz
    have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 := ⟨by linarith only [h9,hwr.1],hwr.2⟩
    have hG := lemma61_large_shift_gaussian_bound (by linarith : 3 ≤ lemma23PaperL D) hwide
    have hgauss : w.im ^ 2 / (4 * lemma23PaperL D ^ 30) = lemma23PaperL D ^ 10 / 4 := by
      rw [← sq_abs w.im, hwi]
      field_simp
    rw [neg_div, hgauss] at hG
    have hinv : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      have h := Complex.abs_im_le_norm w
      linarith only [h,hwi,h20])
    change ‖lemma61SingleMellinNumerator (D := D) (lemma44CharacterTwist χ ψ) s (lemma23PaperP D ^ z) w / w‖ ≤ _
    unfold lemma61SingleMellinNumerator
    rw [norm_div, norm_mul, div_eq_mul_inv]
    apply (mul_le_mul (mul_le_mul hF hG (norm_nonneg _) (by positivity)) hinv
      (inv_nonneg.mpr (norm_nonneg _)) (by positivity)).trans_eq
    rw [show 2 = (1 : ℝ) + 1 by norm_num,
      show 4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4 =
        4 * lemma23PaperL D ^ 9 + -(lemma23PaperL D ^ 10 / 4) by ring]
    simp only [Real.exp_add]
    ring
  apply (lemma112_normalized_integral_norm_le hp).trans
  calc
    _ = 204 * Real.exp 2 * (lemma23PaperL D ^ 519 *
        Real.exp (4 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by norm_num; ring
    _ ≤ 204 * Real.exp 2 * (lemma23PaperL D ^ 519 *
        Real.exp (5 * lemma23PaperL D ^ 9 - lemma23PaperL D ^ 10 / 4)) := by
      gcongr
      have h : 0 ≤ lemma23PaperL D ^ 9 := by positivity
      linarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma61_horizontal_L_exponent_absorption hL) (by positivity)

lemma lemma112_short_polynomial_norm_bound {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma112ShortPolynomial χ ψ s‖ ≤ 2 * Real.exp (lemma23PaperL D ^ 9) := by
  unfold lemma112ShortPolynomial
  exact (lemma112_finite_polynomial_norm_bound _ _
    (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1)
    (fun n hn => lemma112_coefficient_norm_le_one χ ψ n) hs).trans
    (lemma112_short_cutoff_card hL)

lemma lemma112_model_scale_identity {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (s w : ℂ) (z : ℝ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      (lemma112ConductorScale D : ℂ) ^ (-w) * exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) =
    lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      exp (-w * (Real.log (lemma112DualScale D z) : ℂ)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  rw [lemma61_positive_real_cpow_model (lemma112_conductor_scale_pos hD), mul_assoc, ← exp_add,
    lemma112_dual_scale_log hD]
  congr 2
  push_cast
  ring

lemma lemma112_error_horizontal_factor_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) {s w : ℂ}
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 0) (hwi : |w.im| = lemma23PaperL D ^ 20)
    {z : ℝ} (hz : z ∈ Icc (1 / 2 : ℝ) (63 / 125 : ℝ)) :
    ‖(lemma112ErrorDifferenceNumerator χ ψ s w / w) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ ≤
      2 * Real.exp 1 * Real.exp (lemma23PaperL D ^ 9) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL3 : 3 ≤ lemma23PaperL D := by linarith
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ h1
  have htw := lemma112_twist_family_data χ ψ hL3 hψ
  have hzn : ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s‖ = 1 :=
    lemma23DirichletZ_norm_eq_one_on_critical_line _ htw.1 htw.2.2.1 hs.1
  have hw : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 :=
    ⟨by linarith only [hwr.1,h9], by linarith only [hwr.2]⟩
  have hZ := (lemma112_twist_Z_scale_cancellation χ ψ hψ hD hL3 hs hw hwi.le z).trans
    (mul_le_mul_of_nonneg_left (lemma112_dual_scale_left_bound hD hL hz hwr.1) (Real.exp_nonneg _))
  have hmodel : ‖lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      (lemma112ConductorScale D : ℂ) ^ (-w) * exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ ≤
      Real.exp (lemma23PaperL D ^ 9) := by
    rw [lemma112_model_scale_identity χ ψ hD, norm_mul, hzn, one_mul, norm_exp]
    simpa only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero] using
      lemma112_dual_scale_left_bound hD hL hz hwr.1
  have hn : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    have hi := Complex.abs_im_le_norm w
    have h20 : 1 ≤ lemma23PaperL D ^ 20 := one_le_pow₀ h1
    linarith only [hi, hwi, h20])
  have he : (lemma112ErrorDifferenceNumerator χ ψ s w / w) * exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) =
      (lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) * exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) -
        lemma23DirichletZ (lemma44CharacterTwist χ ψ) s * (lemma112ConductorScale D : ℂ) ^ (-w) *
          exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ))) / w := by
    unfold lemma112ErrorDifferenceNumerator
    ring
  rw [he, norm_div, div_eq_mul_inv]
  apply (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (inv_nonneg.mpr (norm_nonneg _))).trans
  have hh := mul_le_mul (add_le_add hZ hmodel) hn (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
  apply hh.trans
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  nlinarith only [mul_le_mul_of_nonneg_right he1 (Real.exp_nonneg (lemma23PaperL D ^ 9))]

end ZhangLS.Spec
