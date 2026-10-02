import ZhangLS.Spec.Lemma53Kernels

/-! # Exact inverse Mellin transform of the original Gaussian weight -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma53_gaussian_inverse_integrable {B : ℝ} (hB : 0 < B)
    (s₀ : ℂ) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
      (((Real.sqrt Real.pi / B : ℝ) : ℂ) *
        Complex.exp ((((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2)))) := by
  let b : ℝ := 1 / (2 * B)
  let c : ℂ := 2 * I * ((σ : ℂ) - s₀) / (4 * (B : ℂ) ^ 2) - I * (Real.log x : ℂ)
  let d : ℂ := ((σ : ℂ) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2) - (σ : ℂ) * (Real.log x : ℂ)
  have hb : 0 < b := by dsimp [b]; positivity
  have he (t : ℝ) : (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
      (((Real.sqrt Real.pi / B : ℝ) : ℂ) *
        Complex.exp ((((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2))) =
      ((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp d *
        Complex.exp (c * (t : ℂ) - (b : ℂ) ^ 2 * (t : ℂ) ^ 2) := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    rw [mul_assoc, ← Complex.exp_add]
    have hr : Complex.exp ((Real.log x : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))) *
        (((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp
          ((((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2))) =
        ((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp
          ((Real.log x : ℂ) * (-((σ : ℂ) + (t : ℂ) * I)) +
            (((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2)) := by
      rw [Complex.exp_add]
      ring
    rw [hr]
    congr 1
    congr 1
    dsimp [b, c, d]
    push_cast
    field_simp [show (B : ℂ) ≠ 0 from ofReal_ne_zero.mpr hB.ne']
    ring_nf
    rw [I_sq]
    ring
  have hg := (lemma53_gaussian_laplace_integrable hb c).const_mul
    (((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp d)
  simpa only [he] using hg

theorem lemma53_gaussian_inverse {B : ℝ} (hB : 0 < B) (s₀ : ℂ) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s : ℂ => ((Real.sqrt Real.pi / B : ℝ) : ℂ) *
      Complex.exp ((s - s₀) ^ 2 / (4 * (B : ℂ) ^ 2))) x =
      Complex.exp (-s₀ * (Real.log x : ℂ) - (B : ℂ) ^ 2 * (Real.log x : ℂ) ^ 2) := by
  let b : ℝ := 1 / (2 * B)
  let c : ℂ := 2 * I * ((σ : ℂ) - s₀) / (4 * (B : ℂ) ^ 2) - I * (Real.log x : ℂ)
  let d : ℂ := ((σ : ℂ) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2) - (σ : ℂ) * (Real.log x : ℂ)
  have hb : 0 < b := by dsimp [b]; positivity
  have he (t : ℝ) : (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
      (((Real.sqrt Real.pi / B : ℝ) : ℂ) *
        Complex.exp ((((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2))) =
      ((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp d *
        Complex.exp (c * (t : ℂ) - (b : ℂ) ^ 2 * (t : ℂ) ^ 2) := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    have hr : Complex.exp ((Real.log x : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))) *
        (((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp
          ((((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2))) =
        ((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp
          ((Real.log x : ℂ) * (-((σ : ℂ) + (t : ℂ) * I)) +
            (((σ : ℂ) + (t : ℂ) * I) - s₀) ^ 2 / (4 * (B : ℂ) ^ 2)) := by
      rw [Complex.exp_add]
      ring
    rw [hr, mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    dsimp [b, c, d]
    push_cast
    field_simp [show (B : ℂ) ≠ 0 from ofReal_ne_zero.mpr hB.ne']
    ring_nf
    rw [I_sq]
    ring
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  simp_rw [he]
  rw [integral_const_mul, lemma53_gaussian_laplace hb c]
  have hsqrt : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hcoef : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((Real.sqrt Real.pi / B : ℝ) : ℂ) * ((Real.sqrt Real.pi / b : ℝ) : ℂ) = 1 := by
    dsimp [b]
    norm_cast
    field_simp [hB.ne', Real.pi_ne_zero]
    nlinarith only [hsqrt]
  have hexp : d + c ^ 2 / (4 * (b : ℂ) ^ 2) =
      -s₀ * (Real.log x : ℂ) - (B : ℂ) ^ 2 * (Real.log x : ℂ) ^ 2 := by
    dsimp [b, c, d]
    push_cast
    field_simp [show (B : ℂ) ≠ 0 from ofReal_ne_zero.mpr hB.ne']
    ring_nf
    rw [I_sq]
    ring
  have hproduct : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp d *
        (((Real.sqrt Real.pi / b : ℝ) : ℂ) * Complex.exp (c ^ 2 / (4 * (b : ℂ) ^ 2)))) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt Real.pi / B : ℝ) : ℂ) *
        ((Real.sqrt Real.pi / b : ℝ) : ℂ)) * Complex.exp (d + c ^ 2 / (4 * (b : ℂ) ^ 2)) := by
    rw [Complex.exp_add]
    ring
  rw [hproduct, hcoef, one_mul, hexp]

theorem lemma53_omega_inverse {D : ℕ} (hD : 1 < D) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (lemma53PaperOmega D) x =
      Complex.exp (-lemma23PaperCenter D * (Real.log x : ℂ) -
        (lemma53PaperScale D : ℂ) ^ 2 * (Real.log x : ℂ) ^ 2) :=
  lemma53_gaussian_inverse (lemma53_scale_pos hD) (lemma23PaperCenter D) σ hx

end ZhangLS.Spec
