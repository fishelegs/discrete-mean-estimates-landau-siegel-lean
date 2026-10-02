import ZhangLS.Spec.Lemma23ProductApproximation
import ZhangLS.Spec.Lemma23BorelCaratheodory
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4.3 from genuine good-set membership

Lemmas 4.1 and 4.2 supply the two-sided bounds and zero-freeness required
by the already proved Borel--Carathéodory/Cauchy estimate.  Disk containment
is proved for the actual regions `Ω₂ ⊂ Ω₁`, not assumed.
-/

namespace ZhangLS.Spec

private theorem lemma23_L227_error_lt_half {L : ℝ} (hL : 3 ≤ L) :
    4 * L ^ (-227 : ℤ) < 1 / 2 := by
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hp2 : 9 ≤ L ^ 2 := by nlinarith
  have hp227 : 9 ≤ L ^ 227 := hp2.trans (pow_le_pow_right₀ hL1 (by norm_num))
  have hp227pos : 0 < L ^ 227 := pow_pos hLpos _
  have hinv : (L ^ 227)⁻¹ ≤ (9 : ℝ)⁻¹ :=
    (inv_le_inv₀ hp227pos (by norm_num : 0 < (9 : ℝ))).mpr hp227
  have hpow : L ^ (-227 : ℤ) = (L ^ 227)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  rw [hpow]
  norm_num at hinv
  linarith

/-- Genuine two-sided bounds on `F` in the entire region `Ω₁`. -/
theorem lemma23_omega1_F_two_sided {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma23InOmega1 D s) :
    (lemma23PaperL D ^ 88)⁻¹ ≤
        ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ∧
      ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ≤ lemma23PaperL D ^ 88 := by
  let L := lemma23PaperL D
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s
  let G := lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by dsimp [L]; linarith
  have h41 : ‖F‖ + ‖G‖ ≤ 2 * L ^ 79 :=
    lemma23_lemma41_of_good_partial_sums χ ψ s hL hgood hs
  have h42 : ‖F * G - 1‖ < 1 / 2 :=
    (lemma23_lemma42_of_good_partial_sums χ ψ s hL hgood hs).trans_lt
      (lemma23_L227_error_lt_half hL)
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

theorem lemma23_omega1_F_ne_zero {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma23InOmega1 D s) :
    lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s ≠ 0 := by
  intro hzero
  have h := (lemma23_omega1_F_two_sided χ ψ s hL hgood hs).1
  rw [hzero, norm_zero] at h
  have hpos : 0 < (lemma23PaperL D ^ 88)⁻¹ := by positivity
  linarith

/-- The actual region `Ω₂` of Lemma 4.3. -/
def Lemma23InOmega2 (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 - (lemma23PaperL D)⁻¹ < s.re ∧
    s.re < 1 + (lemma23PaperL D)⁻¹ ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 4

noncomputable def lemma23LogDerivativeRadius (D : ℕ) : ℝ :=
  Real.log (lemma23PaperL D) / (200 * lemma23PaperL D)

/-- Every Cauchy disk used in the paper is inside `Ω₁`; `log L ≥ 200` is an
explicit sufficient version of the paper's global sufficiently-large-modulus convention. -/
theorem lemma23_omega2_disk_subset_omega1 {D : ℕ} {s z : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hlogL : 200 ≤ Real.log (lemma23PaperL D))
    (hs : Lemma23InOmega2 D s)
    (hz : z ∈ Metric.ball s (lemma23LogDerivativeRadius D)) :
    Lemma23InOmega1 D z := by
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
    |s.im - (lemma23PaperCenter D).im| < L ^ 405 + 4 at hs'
  unfold Lemma23InOmega1
  change 1 / 2 - Real.log L / (100 * L) < z.re ∧
    z.re < 1 + Real.log L / (100 * L) ∧ _
  rw [hdelta]
  refine ⟨by linarith [hs'.1], by linarith [hs'.2.1], ?_⟩
  calc
    |z.im - (lemma23PaperCenter D).im| ≤
        |z.im - s.im| + |s.im - (lemma23PaperCenter D).im| := abs_sub_le _ _ _
    _ < R + (L ^ 405 + 4) := add_lt_add him hs'.2.2
    _ ≤ L ^ 405 + 5 := by linarith

/-- Lemma 4.3, now with all disk norm and zero-freeness hypotheses discharged
from true good-set membership.  The explicit absolute constant is `140800`. -/
theorem lemma23_lemma43_of_good_partial_sums {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hlogL : 200 ≤ Real.log (lemma23PaperL D))
    (hgood : Lemma23GoodPartialSums χ ψ) (hs : Lemma23InOmega2 D s) :
    ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N))) s‖ ≤
      140800 * lemma23PaperL D := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hlogpos : 0 < Real.log (lemma23PaperL D) := by linarith
  have hRpos : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    positivity
  have hbound := lemma23_actualSectionFourF_logDeriv_bound_of_two_sided_norm
    χ (fun n => ψ (n : ZMod N)) s hRpos (by linarith : 1 < lemma23PaperL D)
    (fun z hz => lemma23_omega1_F_two_sided χ ψ z hL hgood
      (lemma23_omega2_disk_subset_omega1 hL hlogL hs hz))
  calc
    _ ≤ 704 * Real.log (lemma23PaperL D) / lemma23LogDerivativeRadius D := hbound
    _ = 140800 * lemma23PaperL D := by
      unfold lemma23LogDerivativeRadius
      field_simp
      ring

theorem lemma23_lemma43 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hlogL : 200 ≤ Real.log (lemma23PaperL D))
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma23InOmega2 D s) :
    ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s‖ ≤
      140800 * lemma23PaperL D :=
  lemma23_lemma43_of_good_partial_sums χ ψ s hL hlogL hψ.2 hs

/-- A closed computable common threshold for Lemmas 4.1--4.3.  It is kept
factored: expanding the outer power would be computationally unreasonable. -/
def lemma23SectionFourModulusThreshold : ℕ := 3 ^ (3 ^ 200)

theorem lemma23_sectionFour_parameters_at_explicit_threshold {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) :
    3 ≤ lemma23PaperL D ∧ 200 ≤ Real.log (lemma23PaperL D) := by
  have hpow_real : (3 : ℝ) ^ (3 ^ 200 : ℕ) ≤ (D : ℝ) := by
    exact_mod_cast hD
  have hlogthree : (1 : ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr (le_of_lt Real.exp_one_lt_three)
  have hlogmono := Real.log_le_log (by positivity : 0 < (3 : ℝ) ^ (3 ^ 200 : ℕ)) hpow_real
  rw [Real.log_pow] at hlogmono
  have hLlarge : (3 : ℝ) ^ 200 ≤ lemma23PaperL D := by
    calc
      (3 : ℝ) ^ 200 ≤ (3 : ℝ) ^ 200 * Real.log 3 := by
        simpa using mul_le_mul_of_nonneg_left hlogthree (by positivity : 0 ≤ (3 : ℝ) ^ 200)
      _ = ((3 ^ 200 : ℕ) : ℝ) * Real.log 3 := by rw [Nat.cast_pow]; norm_num
      _ ≤ lemma23PaperL D := hlogmono
  constructor
  · have hthree : (3 : ℝ) ≤ (3 : ℝ) ^ 200 := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (show 1 ≤ 200 by norm_num)
    exact hthree.trans hLlarge
  · have hlog := Real.log_le_log (by positivity : 0 < (3 : ℝ) ^ 200) hLlarge
    rw [Real.log_pow] at hlog
    norm_num at hlog
    nlinarith

/-- Uniform paper-facing Lemma 4.3 above a closed modulus threshold. -/
theorem lemma23_lemma43_at_explicit_threshold {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma23InOmega2 D s) :
    ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s‖ ≤
      140800 * lemma23PaperL D := by
  have hparams := lemma23_sectionFour_parameters_at_explicit_threshold hD
  exact lemma23_lemma43 χ ψ s hparams.1 hparams.2 hψ hs

end ZhangLS.Spec
