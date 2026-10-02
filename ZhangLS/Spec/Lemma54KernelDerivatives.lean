import ZhangLS.Spec.Lemma53
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Actual first and second oscillatory derivatives for Lemma 5.4 -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma54DerivativeFactor (u : ℝ) : ℂ :=
  -(2 * Real.pi : ℂ) * I * ((Real.exp u : ℂ) - 1)

noncomputable def lemma54FirstKernel (D : ℕ) (x u : ℝ) : ℂ :=
  lemma54DerivativeFactor u * lemma53OscillatoryKernel D x (u : ℂ)

noncomputable def lemma54SecondKernel (D : ℕ) (x u : ℝ) : ℂ :=
  lemma54DerivativeFactor u ^ 2 * lemma53OscillatoryKernel D x (u : ℂ)

noncomputable def lemma54FirstIntegral (D : ℕ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, lemma54FirstKernel D x u

noncomputable def lemma54SecondIntegral (D : ℕ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, lemma54SecondKernel D x u

theorem lemma54_real_gaussian_integrable {B : ℝ} (hB : 0 < B) (q : ℝ) :
    Integrable (fun u : ℝ => Real.exp (q * u - B ^ 2 * u ^ 2)) := by
  have hg := (lemma53_gaussian_laplace_integrable hB (q : ℂ)).norm
  convert hg using 1
  funext u
  rw [norm_exp]
  congr 1
  simp [mul_re, ← ofReal_pow]

theorem lemma54_derivative_factor_norm_bound (u : ℝ) :
    ‖lemma54DerivativeFactor u‖ ≤ 2 * Real.pi * (Real.exp u + 1) := by
  unfold lemma54DerivativeFactor
  rw [norm_mul, norm_mul, norm_neg, norm_I, mul_one]
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    simp [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (by simp [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)])

theorem lemma54_kernel_hasDerivAt (D : ℕ) (x u : ℝ) :
    HasDerivAt (fun y : ℝ => lemma53OscillatoryKernel D y (u : ℂ))
      (lemma54FirstKernel D x u) x := by
  have hc := Complex.hasDerivAt_exp
    (lemma23PaperCenter D * (u : ℂ) - (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2 -
      (2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp (u : ℂ) - 1))
  have hl := ((hasDerivAt_const (x : ℂ)
    (lemma23PaperCenter D * (u : ℂ) - (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2)).sub
    ((hasDerivAt_id (x : ℂ)).const_mul ((2 * Real.pi : ℂ) * I) |>.mul_const
      (Complex.exp (u : ℂ) - 1)))
  convert (hc.comp (x : ℂ) hl).comp_ofReal using 1
  simp only [lemma54FirstKernel, lemma54DerivativeFactor, lemma53OscillatoryKernel,
    Complex.ofReal_exp, zero_sub, mul_one]
  ring

theorem lemma54_first_kernel_hasDerivAt (D : ℕ) (x u : ℝ) :
    HasDerivAt (fun y : ℝ => lemma54FirstKernel D y u) (lemma54SecondKernel D x u) x := by
  have h := (lemma54_kernel_hasDerivAt D x u).const_mul (lemma54DerivativeFactor u)
  convert h using 1
  unfold lemma54FirstKernel lemma54SecondKernel
  ring

noncomputable def lemma54FirstMajorant (D : ℕ) (u : ℝ) : ℝ :=
  2 * Real.pi * (Real.exp ((3 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) +
    Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2))

noncomputable def lemma54SecondMajorant (D : ℕ) (u : ℝ) : ℝ :=
  8 * Real.pi ^ 2 * (Real.exp ((5 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) +
    Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2))

theorem lemma54_first_majorant_integrable {D : ℕ} (hD : 1 < D) :
    Integrable (lemma54FirstMajorant D) := by
  exact ((lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (3 / 2)).add
    (lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (1 / 2))).const_mul _

theorem lemma54_second_majorant_integrable {D : ℕ} (hD : 1 < D) :
    Integrable (lemma54SecondMajorant D) := by
  exact ((lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (5 / 2)).add
    (lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (1 / 2))).const_mul _

theorem lemma54_first_kernel_norm_bound (D : ℕ) (x u : ℝ) :
    ‖lemma54FirstKernel D x u‖ ≤ lemma54FirstMajorant D u := by
  unfold lemma54FirstKernel
  rw [norm_mul, lemma53_oscillatory_kernel_norm_real]
  apply (mul_le_mul_of_nonneg_right (lemma54_derivative_factor_norm_bound u) (Real.exp_nonneg _)).trans
  apply le_of_eq
  unfold lemma54FirstMajorant
  have he : Real.exp u * Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((3 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he0 : Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by congr 1; ring
  rw [mul_assoc, add_mul, one_mul, he, he0]

theorem lemma54_second_kernel_norm_bound (D : ℕ) (x u : ℝ) :
    ‖lemma54SecondKernel D x u‖ ≤ lemma54SecondMajorant D u := by
  have hf := lemma54_derivative_factor_norm_bound u
  have hsq : ‖lemma54DerivativeFactor u‖ ^ 2 ≤
      8 * Real.pi ^ 2 * (Real.exp (2 * u) + 1) := by
    have hp : 0 ≤ 2 * Real.pi * (Real.exp u + 1) := by positivity
    have hs := pow_le_pow_left₀ (norm_nonneg _) hf 2
    have he : Real.exp (2 * u) = Real.exp u ^ 2 := by
      rw [two_mul, Real.exp_add, pow_two]
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (sq_nonneg (Real.exp u - 1))]
  unfold lemma54SecondKernel
  rw [norm_mul, norm_pow, lemma53_oscillatory_kernel_norm_real]
  apply (mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)).trans
  apply le_of_eq
  unfold lemma54SecondMajorant
  have he : Real.exp (2 * u) * Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((5 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he0 : Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by congr 1; ring
  rw [mul_assoc, add_mul, one_mul, he, he0]

theorem lemma54_first_kernel_integrable {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (lemma54FirstKernel D x) := by
  apply (lemma54_first_majorant_integrable hD).mono'
  · apply Continuous.aestronglyMeasurable
    unfold lemma54FirstKernel lemma54DerivativeFactor lemma53OscillatoryKernel
    fun_prop
  · exact Eventually.of_forall (lemma54_first_kernel_norm_bound D x)

theorem lemma54_second_kernel_integrable {D : ℕ} (hD : 1 < D) (x : ℝ) :
    Integrable (lemma54SecondKernel D x) := by
  apply (lemma54_second_majorant_integrable hD).mono'
  · apply Continuous.aestronglyMeasurable
    unfold lemma54SecondKernel lemma54DerivativeFactor lemma53OscillatoryKernel
    fun_prop
  · exact Eventually.of_forall (lemma54_second_kernel_norm_bound D x)

theorem lemma54_oscillatory_hasDerivAt {D : ℕ} (hD : 1 < D) (x : ℝ) :
    HasDerivAt (lemma53OscillatoryDelta D) (lemma54FirstIntegral D x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y u : ℝ => lemma53OscillatoryKernel D y (u : ℂ))
    (F' := lemma54FirstKernel D) (bound := lemma54FirstMajorant D)
    (s := Set.univ) (by simp)
    (Eventually.of_forall fun y => (by unfold lemma53OscillatoryKernel; fun_prop :
      Continuous (fun u : ℝ => lemma53OscillatoryKernel D y (u : ℂ))).aestronglyMeasurable)
    (lemma53_oscillatory_kernel_integrable hD x)
    (lemma54_first_kernel_integrable hD x).aestronglyMeasurable
    (Eventually.of_forall fun u y _ => lemma54_first_kernel_norm_bound D y u)
    (lemma54_first_majorant_integrable hD)
    (Eventually.of_forall fun u y _ => lemma54_kernel_hasDerivAt D y u)
  exact h.2

theorem lemma54_first_integral_hasDerivAt {D : ℕ} (hD : 1 < D) (x : ℝ) :
    HasDerivAt (lemma54FirstIntegral D) (lemma54SecondIntegral D x) x := by
  have hcont (y : ℝ) : Continuous (lemma54FirstKernel D y) := by
    unfold lemma54FirstKernel lemma54DerivativeFactor lemma53OscillatoryKernel
    fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := lemma54FirstKernel D) (F' := lemma54SecondKernel D) (bound := lemma54SecondMajorant D)
    (s := Set.univ) (by simp)
    (Eventually.of_forall fun y => (hcont y).aestronglyMeasurable)
    (lemma54_first_kernel_integrable hD x)
    (lemma54_second_kernel_integrable hD x).aestronglyMeasurable
    (Eventually.of_forall fun u y _ => lemma54_second_kernel_norm_bound D y u)
    (lemma54_second_majorant_integrable hD)
    (Eventually.of_forall fun u y _ => lemma54_first_kernel_hasDerivAt D y u)
  exact h.2

theorem lemma54_oscillatory_continuous {D : ℕ} (hD : 1 < D) :
    Continuous (lemma53OscillatoryDelta D) := by
  have hd : Differentiable ℝ (lemma53OscillatoryDelta D) :=
    fun x => (lemma54_oscillatory_hasDerivAt hD x).differentiableAt
  exact hd.continuous

end ZhangLS.Spec
