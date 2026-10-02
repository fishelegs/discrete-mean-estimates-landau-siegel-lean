import ZhangLS.Spec.Lemma59ExtendedPolynomialBounds

/-! # Auxiliary inputs for Lemma 5.9

The actual original closed strip, actual coefficients and actual L-function
are retained. The full `Lemma59Target` quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric MeasureTheory Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma59_extended_F_two_sided {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 100 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma59InExtendedOmega1 D s) :
    (lemma23PaperL D ^ 88)⁻¹ ≤
        ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ∧
      ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ≤ lemma23PaperL D ^ 88 := by
  let L := lemma23PaperL D
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s
  let G := lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by dsimp [L]; linarith
  have h41 : ‖F‖ + ‖G‖ ≤ 2 * L ^ 79 :=
    lemma59_extended_FG_bound χ ψ s hL hgood hs
  have h42 : ‖F * G - 1‖ < 1 / 2 :=
    (lemma59_extended_product_bound χ ψ s hL hgood hs).trans_lt
      (lemma59_extended_L227_error_lt_half (by linarith only [hL] : 3 ≤ lemma23PaperL D))
  have hprod : 1 / 2 ≤ ‖F‖ * ‖G‖ := by
    have htriangle := norm_sub_norm_le (1 : ℂ) (F * G)
    rw [norm_one, norm_sub_rev, norm_mul] at htriangle
    linarith
  have hG : ‖G‖ ≤ 2 * L ^ 79 := by linarith [norm_nonneg F]
  have hF : ‖F‖ ≤ 2 * L ^ 79 := by linarith [norm_nonneg G]
  have hp9 : 4 ≤ L ^ 9 := by
    have hp2 : 9 ≤ L ^ 2 := by nlinarith
    have hp := pow_le_pow_right₀ hL1 (show 2 ≤ 9 by norm_num)
    linarith
  have hpower : 4 * L ^ 79 ≤ L ^ 88 := by
    calc
      4 * L ^ 79 ≤ L ^ 9 * L ^ 79 := mul_le_mul_of_nonneg_right hp9 (by positivity)
      _ = L ^ 88 := by rw [← pow_add]
  have hscaled : 1 ≤ ‖F‖ * L ^ 88 := by
    have hprod' : 1 / 2 ≤ ‖F‖ * (2 * L ^ 79) :=
      hprod.trans (mul_le_mul_of_nonneg_left hG (norm_nonneg F))
    have hmono := mul_le_mul_of_nonneg_left hpower (norm_nonneg F)
    nlinarith
  constructor
  · change (L ^ 88)⁻¹ ≤ ‖F‖
    rw [← one_div]
    exact (div_le_iff₀ (pow_pos hLpos _)).mpr hscaled
  · change ‖F‖ ≤ L ^ 88
    calc
      ‖F‖ ≤ 2 * L ^ 79 := hF
      _ ≤ 4 * L ^ 79 := by nlinarith [pow_nonneg hLpos.le 79]
      _ ≤ L ^ 88 := hpower

theorem lemma59_extended_F_ne_zero {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 100 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma59InExtendedOmega1 D s) :
    lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s ≠ 0 := by
  intro hzero
  have h := (lemma59_extended_F_two_sided χ ψ s hL hgood hs).1
  rw [hzero, norm_zero] at h
  have hpos : 0 < (lemma23PaperL D ^ 88)⁻¹ := by positivity
  linarith

theorem lemma59_extended_disk_subset_omega1 {D : ℕ} {s z : ℂ}
    (hL : 100 ≤ lemma23PaperL D) (hlogL : 200 ≤ Real.log (lemma23PaperL D))
    (hs : Lemma59InExtendedOmega2 D s)
    (hz : z ∈ Metric.ball s (lemma23LogDerivativeRadius D)) :
    Lemma59InExtendedOmega1 D z := by
  let L := lemma23PaperL D
  let R := lemma23LogDerivativeRadius D
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hRle : R ≤ 1 := by
    change Real.log L / (200 * L) ≤ 1
    apply (div_le_iff₀ (by positivity : 0 < 200 * L)).mpr
    nlinarith [Real.log_le_self hLpos.le]
  have hinv : L⁻¹ ≤ R := by
    change L⁻¹ ≤ Real.log L / (200 * L)
    apply (le_div_iff₀ (by positivity : 0 < 200 * L)).mpr
    have hcancel : L⁻¹ * (200 * L) = 200 := by field_simp
    rw [hcancel]
    exact hlogL
  have hdelta : Real.log L / (100 * L) = 2 * R := by
    dsimp [R, lemma23LogDerivativeRadius, L]
    ring
  have hnorm : ‖z - s‖ < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hrebound : |z.re - s.re| ≤ ‖z - s‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - s)
  have himbound : |z.im - s.im| ≤ ‖z - s‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - s)
  have hre : |z.re - s.re| < R := hrebound.trans_lt hnorm
  have him : |z.im - s.im| < R := himbound.trans_lt hnorm
  have hre' := abs_lt.mp hre
  have hs' := hs
  change 1 / 2 - L⁻¹ < s.re ∧ s.re < 1 + L⁻¹ ∧
    |s.im - (lemma23PaperCenter D).im| < L ^ 405 + 19 at hs'
  unfold Lemma59InExtendedOmega1
  change 1 / 2 - Real.log L / (100 * L) < z.re ∧
    z.re < 1 + Real.log L / (100 * L) ∧ _
  rw [hdelta]
  refine ⟨by linarith [hs'.1], by linarith [hs'.2.1], ?_⟩
  calc
    |z.im - (lemma23PaperCenter D).im| ≤
        |z.im - s.im| + |s.im - (lemma23PaperCenter D).im| := abs_sub_le _ _ _
    _ < R + (L ^ 405 + 19) := add_lt_add him hs'.2.2
    _ ≤ L ^ 405 + 20 := by linarith

theorem lemma59_extended_F_logDeriv_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 100 ≤ lemma23PaperL D) (hlogL : 200 ≤ Real.log (lemma23PaperL D))
    (hgood : Lemma23GoodPartialSums χ ψ) (hs : Lemma59InExtendedOmega2 D s) :
    ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N))) s‖ ≤
      140800 * lemma23PaperL D := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hlogpos : 0 < Real.log (lemma23PaperL D) := by linarith
  have hRpos : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    positivity
  have hbound := lemma23_actualSectionFourF_logDeriv_bound_of_two_sided_norm
    χ (fun n => ψ (n : ZMod N)) s hRpos (by linarith : 1 < lemma23PaperL D)
    (fun z hz => lemma59_extended_F_two_sided χ ψ z hL hgood
      (lemma59_extended_disk_subset_omega1 hL hlogL hs hz))
  calc
    _ ≤ 704 * Real.log (lemma23PaperL D) / lemma23LogDerivativeRadius D := hbound
    _ = 140800 * lemma23PaperL D := by
      unfold lemma23LogDerivativeRadius
      field_simp
      ring

end ZhangLS.Spec
