import ZhangLS.Spec.Lemma51Parameters
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.MellinTransform

/-! # The original Mellin kernel and Gaussian phase in Lemma 5.3

The paper's Delta remains defined by its actual Mellin inverse integral.
The oscillatory integral is a separate object until their equality is proved.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

noncomputable def lemma53PaperScale (D : ℕ) : ℝ := lemma23PaperL D ^ 400

noncomputable def lemma53PaperOmega (D : ℕ) (s : ℂ) : ℂ :=
  ((Real.sqrt Real.pi / lemma53PaperScale D : ℝ) : ℂ) *
    Complex.exp ((s - lemma23PaperCenter D) ^ 2 / (4 * (lemma53PaperScale D : ℂ) ^ 2))

noncomputable def lemma53PaperThetaStar (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
    Complex.exp ((2 * Real.pi : ℂ) * I * (-s / 4))

noncomputable def lemma53PaperDeltaOne (D : ℕ) (x : ℝ) : ℂ :=
  mellinInv (3 / 2) (fun s => lemma53PaperThetaStar s * lemma53PaperOmega D s) x

noncomputable def lemma53PaperDelta (D : ℕ) (x : ℝ) : ℂ :=
  lemma53PaperDeltaOne D x * Complex.exp ((2 * Real.pi : ℂ) * I * (x : ℂ))

noncomputable def lemma53GaussianPhase (D : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((2 * Real.pi : ℂ) * I * ((lemma51PaperT0 D - x : ℝ) : ℂ) * w -
    (lemma53PaperScale D : ℂ) ^ 2 * w ^ 2)

noncomputable def lemma53Perturbation (x : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (w / 2 - (2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp w - 1 - w))

noncomputable def lemma53OscillatoryKernel (D : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (lemma23PaperCenter D * w - (lemma53PaperScale D : ℂ) ^ 2 * w ^ 2 -
    (2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp w - 1))

noncomputable def lemma53OscillatoryDelta (D : ℕ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, lemma53OscillatoryKernel D x (u : ℂ)

theorem lemma53_scale_pos {D : ℕ} (hD : 1 < D) : 0 < lemma53PaperScale D := by
  unfold lemma53PaperScale lemma23PaperL
  exact pow_pos (Real.log_pos (by exact_mod_cast hD)) 400

theorem lemma53_gaussian_laplace_integrable {B : ℝ} (hB : 0 < B) (s : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (s * (u : ℂ) - (B : ℂ) ^ 2 * (u : ℂ) ^ 2)) := by
  have hb : (-(B : ℂ) ^ 2).re < 0 := by
    rw [neg_re, pow_two, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact neg_lt_zero.mpr (mul_pos hB hB)
  convert integrable_cexp_quadratic' hb s 0 using 1
  funext u
  congr 1
  ring

theorem lemma53_gaussian_laplace {B : ℝ} (hB : 0 < B) (s : ℂ) :
    (∫ u : ℝ, Complex.exp (s * (u : ℂ) - (B : ℂ) ^ 2 * (u : ℂ) ^ 2)) =
      ((Real.sqrt Real.pi / B : ℝ) : ℂ) * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) := by
  have hb : (-(B : ℂ) ^ 2).re < 0 := by
    rw [neg_re, pow_two, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact neg_lt_zero.mpr (mul_pos hB hB)
  have hq := integral_cexp_quadratic hb s 0
  have he : (fun u : ℝ => Complex.exp (s * (u : ℂ) - (B : ℂ) ^ 2 * (u : ℂ) ^ 2)) =
      (fun u : ℝ => Complex.exp (-(B : ℂ) ^ 2 * u ^ 2 + s * u + 0)) := by
    funext u
    congr 1
    ring
  rw [he, hq]
  simp only [neg_neg, zero_sub, mul_neg, div_neg, neg_neg]
  have hroot : ((Real.pi : ℂ) / (B : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      ((Real.sqrt Real.pi / B : ℝ) : ℂ) := by
    have hbase : (Real.pi : ℂ) / (B : ℂ) ^ 2 = ((Real.pi / B ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    calc
      _ = (((Real.pi / B ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        rw [hbase]
        symm
        convert Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / B ^ 2) (1 / 2 : ℝ)
          using 1 <;> norm_num
      _ = (Real.sqrt (Real.pi / B ^ 2) : ℂ) := by rw [Real.sqrt_eq_rpow]
      _ = _ := by rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hB.le]
  rw [hroot]

theorem lemma53_gaussian_phase_integrable {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (fun u : ℝ => lemma53GaussianPhase D x (u : ℂ)) :=
  lemma53_gaussian_laplace_integrable (lemma53_scale_pos hD)
    ((2 * Real.pi : ℂ) * I * ((lemma51PaperT0 D - x : ℝ) : ℂ))

theorem lemma53_gaussian_main_term {D : ℕ} (hD : 1 < D) (x : ℝ) :
    (∫ u : ℝ, lemma53GaussianPhase D x (u : ℂ)) =
      lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) := by
  have h := lemma53_gaussian_laplace (lemma53_scale_pos hD)
    ((2 * Real.pi : ℂ) * I * ((lemma51PaperT0 D - x : ℝ) : ℂ))
  unfold lemma53GaussianPhase
  rw [h]
  unfold lemma53PaperOmega
  congr 2
  have hc : lemma23PaperCenter D = (1 / 2 : ℂ) +
      (2 * Real.pi : ℂ) * I * (lemma51PaperT0 D : ℂ) := by
    apply Complex.ext <;> simp [lemma23PaperCenter, lemma51PaperT0, ← Complex.ofReal_pow]
  rw [hc]
  push_cast
  ring

theorem lemma53_kernel_factorization (D : ℕ) (x : ℝ) (w : ℂ) :
    lemma53OscillatoryKernel D x w = lemma53GaussianPhase D x w * lemma53Perturbation x w := by
  unfold lemma53OscillatoryKernel lemma53GaussianPhase lemma53Perturbation
  rw [← Complex.exp_add]
  congr 1
  have hc : lemma23PaperCenter D = (1 / 2 : ℂ) +
      (2 * Real.pi : ℂ) * I * (lemma51PaperT0 D : ℂ) := by
    apply Complex.ext <;> simp [lemma23PaperCenter, lemma51PaperT0, ← Complex.ofReal_pow]
  rw [hc]
  push_cast
  ring

theorem lemma53_omega_critical_gaussian (D : ℕ) (x : ℝ) :
    lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ)) =
      ((Real.sqrt Real.pi / lemma53PaperScale D *
        Real.exp (-((Real.pi * (x - lemma51PaperT0 D) / lemma53PaperScale D) ^ 2)) : ℝ) : ℂ) := by
  unfold lemma53PaperOmega
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  have hc : lemma23PaperCenter D = (1 / 2 : ℂ) +
      (2 * Real.pi : ℂ) * I * (lemma51PaperT0 D : ℂ) := by
    apply Complex.ext <;> simp [lemma23PaperCenter, lemma51PaperT0, -Complex.ofReal_pow]
  rw [hc]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem lemma53_omega_critical_pos {D : ℕ} (hD : 1 < D) (x : ℝ) :
    0 < (lemma53PaperOmega D ((1 / 2 : ℂ) + (2 * Real.pi : ℂ) * I * (x : ℂ))).re := by
  rw [lemma53_omega_critical_gaussian, Complex.ofReal_re]
  exact mul_pos (div_pos (Real.sqrt_pos.mpr Real.pi_pos) (lemma53_scale_pos hD))
    (Real.exp_pos _)

end ZhangLS.Spec
