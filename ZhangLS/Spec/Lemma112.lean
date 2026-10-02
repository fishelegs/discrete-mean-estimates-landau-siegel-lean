import ZhangLS.Spec.Lemma112Approximation
/-! # Original Lemma 11.2, with the actual integrated Gaussian cutoffs

One absolute constant and one threshold work for every real primitive χ,
every ψ in the original Ψ, and the paper's full strict critical-line height
window. Neither assumption (A) nor membership in Ψ₁ is used.

The p65 label `E` is interpreted as the `E₂` named in the statement and
subsequent proof; its exact displayed definition is `lemma112ActualE2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112GaussianDefect {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z : ℝ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s -
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s +
    lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      lemma112GaussianSeries χ ψ⁻¹ (lemma112DualScale D z) (1 - s)

lemma lemma112_dual_series_interval_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : 1 < D) (a b : ℝ) :
    IntervalIntegrable (fun z => lemma112GaussianSeries χ ψ (lemma112DualScale D z) s) volume a b := by
  have hA : 0 < (D : ℝ) * lemma51PaperT0 D := mul_pos
    (by exact_mod_cast lt_trans Nat.zero_lt_one hD)
    (pow_pos (Real.log_pos (by exact_mod_cast hD)) _)
  have h := (lemma112_gaussian_series_interval_integrable χ ψ s hD hA (1 - a) (1 - b)).comp_sub_left 1
  have ha : 1 - (1 - a) = a := by ring
  have hb : 1 - (1 - b) = b := by ring
  rw [ha, hb] at h
  simpa only [lemma112DualScale, mul_assoc] using h

lemma lemma112_defect_integral_identity {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : 1 < D) (a b : ℝ) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∫ z in a..b, lemma112GaussianDefect χ ψ s z) =
      (∫ z in a..b, lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s) -
        ((b - a : ℝ) : ℂ) * DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s +
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
        (∫ z in (1 - b)..(1 - a),
          lemma112GaussianSeries χ ψ⁻¹ (lemma23PaperP D ^ z * (D : ℝ) * lemma51PaperT0 D) (1 - s)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hfirst : IntervalIntegrable (fun z => lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s) volume a b := by
    simpa only [mul_one] using lemma112_gaussian_series_interval_integrable χ ψ s hD (A := 1) (by norm_num) a b
  have hdual := lemma112_dual_series_interval_integrable χ ψ⁻¹ (1 - s) hD a b
  have hconst : IntervalIntegrable (fun _z : ℝ => DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s) volume a b :=
    intervalIntegrable_const
  unfold lemma112GaussianDefect
  rw [intervalIntegral.integral_add (hfirst.sub hconst)
      (hdual.const_mul (lemma23DirichletZ (lemma44CharacterTwist χ ψ) s)),
    intervalIntegral.integral_sub hfirst hconst, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  congr 2
  exact intervalIntegral.integral_comp_sub_left
    (fun z => lemma112GaussianSeries χ ψ⁻¹ (lemma23PaperP D ^ z * (D : ℝ) * lemma51PaperT0 D) (1 - s)) 1

lemma lemma112_integrated_defect_eq {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (hD : 1 < D) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (-500 : ℂ) * (∫ z in (1 / 2 : ℝ)..(251 / 500 : ℝ), lemma112GaussianDefect χ ψ s z) +
      500 * (∫ z in (251 / 500 : ℝ)..(63 / 125 : ℝ), lemma112GaussianDefect χ ψ s z) =
      lemma112JtildeOne χ ψ s - lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
        lemma112JtildeTwo χ ψ⁻¹ (1 - s) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  rw [lemma112_defect_integral_identity χ ψ s hD, lemma112_defect_integral_identity χ ψ s hD,
    (lemma112_JtildeOne_integral χ ψ s hD).2, (lemma112_JtildeTwo_integral χ ψ⁻¹ (1 - s) hD).2]
  norm_num
  ring

lemma lemma112_approximation_constant_pos : 0 < lemma112ApproximationConstant := by
  have hm2 : 0 ≤ lemma44InverseSquareMass := tsum_nonneg (fun _ => by positivity)
  have hm4 : 0 ≤ lemma61QuarterSeriesMass := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hC := lemma51_error_constant_pos
  unfold lemma112ApproximationConstant lemma112LeftApproximationConstant
  positivity

lemma lemma112_integrated_approximation_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    (hthreshold : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma112InRegion D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖lemma112JtildeOne χ ψ s - lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      lemma112JtildeTwo χ ψ⁻¹ (1 - s)‖ ≤
      (2 * lemma112ApproximationConstant) * lemma112ActualE2 χ ψ s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hb (a b : ℝ) (hab : a ≤ b) (ha : 1 / 2 ≤ a) (hb : b ≤ 63 / 125) :
      ‖∫ z in a..b, lemma112GaussianDefect χ ψ s z‖ ≤
        (lemma112ApproximationConstant * lemma112ActualE2 χ ψ s) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro z hz
    rw [uIoc_of_le hab] at hz
    exact lemma112_actual_approximation_bound χ ψ hψ hD hL hthreshold hs
      ⟨ha.trans hz.1.le, hz.2.trans hb⟩
  have h₁ := hb (1 / 2) (251 / 500) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := hb (251 / 500) (63 / 125) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [show (251 / 500 : ℝ) - 1 / 2 = 1 / 500 by norm_num,
    show (63 / 125 : ℝ) - 251 / 500 = 1 / 500 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 500)] at h₁ h₂
  rw [← lemma112_integrated_defect_eq χ ψ s hD]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  norm_num only [norm_neg, norm_ofNat]
  nlinarith only [h₁, h₂]

/-- Original Lemma 11.2, with a single absolute constant and threshold. -/
theorem lemma112_proved : Lemma112Target := by
  refine ⟨2 * lemma112ApproximationConstant, mul_pos (by norm_num) lemma112_approximation_constant_pos,
    max lemma23SectionFourModulusThreshold 2, ?_⟩
  intro D p inst χ ψ hD hψ s hs
  have hthreshold : lemma23SectionFourModulusThreshold ≤ D := (le_max_left _ _).trans hD
  have hD1 : 1 < D := lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right _ _).trans hD)
  have hL : 64 ≤ lemma23PaperL D := by linarith only [lemma44_log_large_at_threshold hthreshold]
  exact lemma112_integrated_approximation_bound χ ψ hψ hD1 hL hthreshold hs

end ZhangLS.Spec
