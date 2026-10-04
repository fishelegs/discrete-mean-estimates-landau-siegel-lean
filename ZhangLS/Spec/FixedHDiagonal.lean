import ZhangLS.Spec.FixedHDiagonalAlgebra
import ZhangLS.Spec.Lemma83Definitions

/-! The actual finite-D diagonal identity with the published shifts and log P. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHDiagonal
open Complex MeasureTheory

noncomputable def B (D : ℕ) : ℝ := Real.log (lemma23PaperP D)
noncomputable def delta (D : ℕ) (c : ℝ) : ℝ :=
  c * lemma44PaperAlpha D * lemma23PaperL D

lemma B_pos {D : ℕ} (hD : 2 ≤ D) : 0 < B D := by
  have hDn : (1 : ℕ) < D := by omega
  have hd : (1 : ℝ) < D := by exact_mod_cast hDn
  simpa [B, lemma23PaperP, Real.log_exp] using
    pow_pos (Real.log_pos hd) 9

lemma B_mul_alpha {D : ℕ} (hD : 2 ≤ D) : B D * lemma44PaperAlpha D = Real.pi := by
  change B D * (Real.pi / B D) = Real.pi
  exact mul_div_cancel₀ _ (ne_of_gt (B_pos hD))

lemma delta_eq {D : ℕ} (hD : 2 ≤ D) (c : ℝ) :
    delta D c = c * Real.pi * lemma23PaperL D ^ (-8 : ℤ) := by
  have hDn : (1 : ℕ) < D := by omega
  have hd : (1 : ℝ) < D := by exact_mod_cast hDn
  have hL := ne_of_gt (Real.log_pos hd)
  simp only [delta, lemma44PaperAlpha, lemma23PaperP, Real.log_exp,
    lemma23PaperL, zpow_neg]
  field_simp [hL]

/-- Literal cyclic indices and the published beta definition, with no limiting shifts. -/
theorem paper_scaled_shift {D : ℕ} (hD : 2 ≤ D) (c : ℝ) (j : Fin 3) :
    (B D : ℂ) * lemma83PaperBeta D c j = scaledShift (delta D c) j := by
  have hba := B_mul_alpha hD
  have h1 : B D * lemma23PaperOffsetOne D c = Real.pi*(1-5*delta D c) := by
    dsimp [lemma23PaperOffsetOne, delta]
    rw [← mul_assoc, hba]
    ring
  have h2 : B D * lemma23PaperOffsetTwo D c = Real.pi*(2*(1+delta D c)) := by
    dsimp [lemma23PaperOffsetTwo, delta]
    calc
      _ = 2*(B D*lemma44PaperAlpha D)*(1+c*lemma44PaperAlpha D*lemma23PaperL D) := by ring
      _ = _ := by rw [hba]; ring
  have h3 : B D * lemma23PaperOffsetThree D c = Real.pi*(3*(1-delta D c)) := by
    dsimp [lemma23PaperOffsetThree, delta]
    calc
      _ = 3*(B D*lemma44PaperAlpha D)*(1-c*lemma44PaperAlpha D*lemma23PaperL D) := by ring
      _ = _ := by rw [hba]; ring
  fin_cases j <;>
    simp [lemma83PaperBeta, lemma52PaperBetaOne, lemma52PaperBetaTwo,
      lemma52PaperBetaThree, scaledShift, Fin.ext_iff] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h1, h2, h3]

noncomputable def F (D : ℕ) (c : ℝ) (j : Fin 3) (f f' : ℝ → ℝ) (x : ℝ) : ℂ :=
  -(f' x : ℂ) - (B D : ℂ) * lemma83PaperBeta D c j * (f x : ℂ)

noncomputable def G (D : ℕ) (c : ℝ) (j : Fin 3) (f f' : ℝ → ℝ)
    (b x : ℝ) : ℂ :=
  -(f' x : ℂ) + ((B D : ℂ) * lemma83PaperBeta D c (j+1) +
    (B D : ℂ) * lemma83PaperBeta D c (j+2)) * (f x : ℂ) +
    (((B D : ℂ) * lemma83PaperBeta D c (j+1)) *
      ((B D : ℂ) * lemma83PaperBeta D c (j+2))) * (tail f b x : ℂ)

/-- Exact finite-D identity for a general real C¹ profile. Compact support and a
zero terminal value may be imposed by the caller; neither is needed by this identity. -/
theorem paper_diagonal {D : ℕ} (hD : 2 ≤ D) (c : ℝ) (j : Fin 3)
    {f f' : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt f (f' x) x) (ha : f a = 0) :
    (∫ x in a..b, (F D c j f f' x * G D c j f f' b x).re) =
      (∫ x in a..b, (f' x)^2) +
      Real.pi^2 * (11-26*delta D c-(delta D c)^2) * (∫ x in a..b, (f x)^2) := by
  simpa only [F, G, firstKernel, secondKernel, ← paper_scaled_shift hD c] using
    scaled_diagonal hf hf' hd ha (delta D c) j

/-- The requested C² compact-support interface, with both boundary values zero. -/
theorem paper_diagonal_c2 {D : ℕ} (hD : 2 ≤ D) (c : ℝ) (j : Fin 3)
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiff ℝ 2 f)
    (_hs : HasCompactSupport f) (ha : f a = 0) (_hb : f b = 0) :
    (∫ x in a..b, (F D c j f (deriv f) x * G D c j f (deriv f) b x).re) =
      (∫ x in a..b, (deriv f x)^2) +
      Real.pi^2 * (11-26*delta D c-(delta D c)^2) * (∫ x in a..b, (f x)^2) := by
  exact paper_diagonal hD c j hf.continuous (hf.continuous_deriv (by norm_num))
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt) ha

end ZhangLS.Spec.FixedHDiagonal
