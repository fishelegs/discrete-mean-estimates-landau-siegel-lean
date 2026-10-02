import ZhangLS.Spec.Lemma44ProductDirichletSeries
import ZhangLS.Spec.Lemma44FiniteGaussianMellin

/-!
# The full product Gaussian Mellin identity for Lemma 4.4

Absolute convergence at `Re(s)+σ>1` supplies a common Gaussian majorant
for the actual coefficients `ν(n)ψ(n)`. This proves vertical integrability,
summability of the smoothed series, and the infinite series/integral
exchange. No approximate functional equation is assumed.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

/-- One coefficient of a Gaussian Mellin integral, including `dw = i dt`. -/
noncomputable def lemma44MellinSeriesTerm (D : ℕ) (c : ℕ → ℂ)
    (s : ℂ) (B σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let w := (σ : ℂ) + (t : ℂ) * I
  LSeries.term c (s + w) n * exp (w * (Real.log B : ℂ)) *
    lemma57OmegaOne D w / w * I

theorem lemma44MellinSeriesTerm_norm (D : ℕ) (c : ℕ → ℂ)
    (s : ℂ) (B σ : ℝ) (n : ℕ) (t : ℝ) :
    ‖lemma44MellinSeriesTerm D c s B σ n t‖ =
      (Real.exp (σ * Real.log B) *
        ‖LSeries.term c ((s.re + σ : ℝ) : ℂ) n‖) *
          ‖lemma57GaussianKernelIntegrand D σ 1 t‖ := by
  have ht : ‖LSeries.term c (s + ((σ : ℂ) + (t : ℂ) * I)) n‖ =
      ‖LSeries.term c ((s.re + σ : ℝ) : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    simp
  simp only [lemma44MellinSeriesTerm, norm_mul, norm_div, ht, norm_exp,
    norm_I, mul_one, lemma57GaussianKernelIntegrand, ofReal_one, one_cpow, norm_one]
  simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, zero_mul, add_zero]
  ring

theorem lemma44MellinSeriesTerm_integrable {D : ℕ} (hD : 1 < D)
    (c : ℕ → ℂ) (s : ℂ) (B : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    Integrable (lemma44MellinSeriesTerm D c s B σ n) := by
  by_cases hn : n = 0
  · subst n
    have hz : lemma44MellinSeriesTerm D c s B σ 0 = 0 := by
      funext t
      simp [lemma44MellinSeriesTerm]
    rw [hz]
    exact integrable_zero ℝ ℂ volume
  let C := Real.exp (σ * Real.log B) *
    ‖LSeries.term c ((s.re + σ : ℝ) : ℂ) n‖
  have hK := lemma57GaussianKernel_integrable (σ := σ) (x := 1)
    hD hσ zero_lt_one
  apply (hK.norm.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    let w : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * I
    have hw : Continuous w := by dsimp [w]; fun_prop
    have hwne : ∀ t, w t ≠ 0 := by
      intro t ht
      apply hσ
      simpa [w] using congrArg Complex.re ht
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hc : Continuous (fun t : ℝ => LSeries.term c (s + w t) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      apply Continuous.div₀ continuous_const
        ((continuous_const.add hw).const_cpow (Or.inl hnC))
      intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hfactor : Continuous (fun t : ℝ => exp (w t * (Real.log B : ℂ)) *
        lemma57OmegaOne D (w t)) := by
      unfold lemma57OmegaOne
      fun_prop
    change Continuous (fun t : ℝ =>
      LSeries.term c (s + w t) n * exp (w t * (Real.log B : ℂ)) *
        lemma57OmegaOne D (w t) / w t * I)
    simpa only [mul_assoc] using
      ((hc.mul hfactor).div₀ hw hwne).mul continuous_const
  · filter_upwards [] with t
    exact (lemma44MellinSeriesTerm_norm D c s B σ n t).le

theorem lemma44MellinSeriesTerm_integral_norm_summable (D : ℕ)
    (c : ℕ → ℂ) (s : ℂ) (B σ : ℝ)
    (hseries : LSeriesSummable c ((s.re + σ : ℝ) : ℂ)) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖lemma44MellinSeriesTerm D c s B σ n t‖) := by
  have hL := summable_norm_iff.mpr hseries
  let K := Real.exp (σ * Real.log B) *
    ∫ t : ℝ, ‖lemma57GaussianKernelIntegrand D σ 1 t‖
  apply (hL.mul_left K).congr
  intro n
  simp_rw [lemma44MellinSeriesTerm_norm, integral_const_mul]
  dsimp [K]
  ring

theorem lemma44MellinSeriesTerm_tsum_integrable {D : ℕ} (hD : 1 < D)
    (c : ℕ → ℂ) (s : ℂ) (B : ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (hseries : LSeriesSummable c ((s.re + σ : ℝ) : ℂ)) :
    Integrable (fun t : ℝ => ∑' n : ℕ, lemma44MellinSeriesTerm D c s B σ n t) := by
  let A := ∑' n : ℕ, ‖LSeries.term c ((s.re + σ : ℝ) : ℂ) n‖
  let C := Real.exp (σ * Real.log B) * A
  have hL := summable_norm_iff.mpr hseries
  have hK := lemma57GaussianKernel_integrable (σ := σ) (x := 1)
    hD hσ zero_lt_one
  apply (hK.norm.const_mul C).mono'
  · exact AEStronglyMeasurable.tsum fun n =>
      (lemma44MellinSeriesTerm_integrable hD c s B hσ n).1
  · filter_upwards [] with t
    have hn : Summable (fun n : ℕ => ‖lemma44MellinSeriesTerm D c s B σ n t‖) := by
      apply (hL.mul_left (Real.exp (σ * Real.log B) *
        ‖lemma57GaussianKernelIntegrand D σ 1 t‖)).congr
      intro n
      rw [lemma44MellinSeriesTerm_norm]
      ring
    calc
      ‖∑' n : ℕ, lemma44MellinSeriesTerm D c s B σ n t‖ ≤
          ∑' n : ℕ, ‖lemma44MellinSeriesTerm D c s B σ n t‖ :=
        norm_tsum_le_tsum_norm hn
      _ = ∑' n : ℕ, (Real.exp (σ * Real.log B) *
          ‖lemma57GaussianKernelIntegrand D σ 1 t‖) *
            ‖LSeries.term c ((s.re + σ : ℝ) : ℂ) n‖ := by
        apply tsum_congr
        intro n
        rw [lemma44MellinSeriesTerm_norm]
        ring
      _ = C * ‖lemma57GaussianKernelIntegrand D σ 1 t‖ := by
        rw [tsum_mul_left]
        dsimp [A, C]
        ring

theorem lemma44MellinSeriesTerm_eq_kernel (D : ℕ) (c : ℕ → ℂ) (s : ℂ)
    {B : ℝ} (hB : 0 < B) (σ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    lemma44MellinSeriesTerm D c s B σ n t =
      LSeries.term c s n * (lemma57GaussianKernelIntegrand D σ (B / n) t * I) := by
  let w := (σ : ℂ) + (t : ℂ) * I
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hx := div_pos hB hnp
  have hlog : Complex.log ((B / n : ℝ) : ℂ) =
      (Real.log B : ℂ) - (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hx.le, Real.log_div hB.ne' hnp.ne', ofReal_sub]
  have hnlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hnp.le).symm
  have hpow : exp (w * (Real.log B : ℂ)) / (n : ℂ) ^ w =
      ((B / n : ℝ) : ℂ) ^ w := by
    rw [Complex.cpow_def_of_ne_zero hnC, hnlog,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), hlog,
      ← Complex.exp_sub]
    congr 1
    ring
  simp only [lemma44MellinSeriesTerm, LSeries.term_of_ne_zero hn,
    lemma57GaussianKernelIntegrand]
  change c n / (n : ℂ) ^ (s + w) * exp (w * (Real.log B : ℂ)) *
      lemma57OmegaOne D w / w * I =
    (c n / (n : ℂ) ^ s) * (((B / n : ℝ) : ℂ) ^ w * lemma57OmegaOne D w / w * I)
  rw [Complex.cpow_add _ _ hnC, ← hpow]
  ring

theorem lemma44MellinSeriesTerm_normalized_integral {D : ℕ} (hD : 1 < D)
    (c : ℕ → ℂ) (s : ℂ) {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ t : ℝ, lemma44MellinSeriesTerm D c s B σ n t) =
      LSeries.term c s n * (zhangGaussianWeight D (B / n) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [lemma44MellinSeriesTerm]
  simp_rw [lemma44MellinSeriesTerm_eq_kernel D c s hB σ _ hn, integral_const_mul]
  have hx : 0 < B / (n : ℝ) :=
    div_pos hB (by exact_mod_cast Nat.pos_of_ne_zero hn)
  calc
    _ = LSeries.term c s n * lemma57GaussianKernelVerticalIntegral D σ (B / n) := by
      unfold lemma57GaussianKernelVerticalIntegral
      ring
    _ = _ := by rw [lemma57GaussianKernelVerticalIntegral_eq_weight hD hσ hx]

/-- Generic Gaussian inversion for an absolutely convergent shifted L-series. -/
theorem lemma44_full_series_gaussian_mellin {D : ℕ} (hD : 1 < D)
    (c : ℕ → ℂ) (s : ℂ) {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hseries : LSeriesSummable c ((s.re + σ : ℝ) : ℂ)) :
    Summable (fun n : ℕ => LSeries.term c s n *
        (zhangGaussianWeight D (B / n) : ℂ)) ∧
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ t : ℝ, ∑' n : ℕ, lemma44MellinSeriesTerm D c s B σ n t) =
          ∑' n : ℕ, LSeries.term c s n * (zhangGaussianWeight D (B / n) : ℂ) := by
  have hi := hasSum_integral_of_summable_integral_norm
    (fun n => lemma44MellinSeriesTerm_integrable hD c s B hσ.ne' n)
    (lemma44MellinSeriesTerm_integral_norm_summable D c s B σ hseries)
  have hs := hi.mul_left ((2 * (Real.pi : ℂ) * I)⁻¹)
  simp_rw [lemma44MellinSeriesTerm_normalized_integral hD c s hB hσ] at hs
  exact ⟨hs.summable, hs.tsum_eq.symm⟩

/-- The actual product integrand on a right vertical line. -/
noncomputable def lemma44ProductMellinIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (B σ t : ℝ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let w := (σ : ℂ) + (t : ℂ) * I
  DirichletCharacter.LFunction ψ (s + w) *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w) *
      exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w / w

theorem lemma44ProductMellinIntegrand_eq_tsum {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (B : ℝ) {σ : ℝ} (hs : 1 < s.re + σ) (t : ℝ) :
    lemma44ProductMellinIntegrand χ ψ s B σ t * I =
      ∑' n : ℕ, lemma44MellinSeriesTerm D
        (fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)) s B σ n t := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hsr : 1 < (s + ((σ : ℂ) + (t : ℂ) * I)).re := by simpa using hs
  rw [lemma44ProductMellinIntegrand, lemma44_product_LFunction_eq_LSeries χ ψ hsr]
  unfold LSeries lemma44MellinSeriesTerm
  simp_rw [div_eq_mul_inv, mul_assoc]
  rw [tsum_mul_right]

/-- The full infinite Gaussian Mellin identity for the genuine product
`L(s,ψ)L(s,χψ)`, with the integrability and summability witnesses. -/
theorem lemma44_product_gaussian_mellin_identity {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : 1 < D) {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (hs : 1 < s.re + σ) :
    Integrable (lemma44ProductMellinIntegrand χ ψ s B σ) ∧
      Summable (fun n : ℕ =>
        LSeries.term (fun m => lemma23NuArithmeticFunction χ m * ψ (m : ZMod p)) s n *
          (zhangGaussianWeight D (B / n) : ℂ)) ∧
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ t : ℝ, lemma44ProductMellinIntegrand χ ψ s B σ t * I) =
        ∑' n : ℕ,
          LSeries.term (fun m => lemma23NuArithmeticFunction χ m * ψ (m : ZMod p)) s n *
            (zhangGaussianWeight D (B / n) : ℂ) := by
  let c : ℕ → ℂ := fun n => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)
  have habs : LSeriesSummable c ((s.re + σ : ℝ) : ℂ) :=
    lemma44_product_series_summable χ ψ (by simpa using hs)
  have ht := lemma44MellinSeriesTerm_tsum_integrable hD c s B hσ.ne' habs
  have hti : Integrable (fun t : ℝ => lemma44ProductMellinIntegrand χ ψ s B σ t * I) := by
    apply ht.congr
    filter_upwards [] with t
    exact (lemma44ProductMellinIntegrand_eq_tsum χ ψ s B hs t).symm
  have hi : Integrable (lemma44ProductMellinIntegrand χ ψ s B σ) := by
    simpa only [mul_assoc, I_mul_I, mul_neg, mul_one, neg_neg] using
      (hti.mul_const (-I))
  refine ⟨hi, (lemma44_full_series_gaussian_mellin hD c s hB hσ habs).1, ?_⟩
  simp_rw [lemma44ProductMellinIntegrand_eq_tsum χ ψ s B hs]
  exact (lemma44_full_series_gaussian_mellin hD c s hB hσ habs).2

end ZhangLS.Spec
