import ZhangLS.Spec.Lemma53Kernels
import ZhangLS.Spec.Lemma57GaussianMellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

noncomputable def lemma171GaussianNumerator (c σ y t : ℝ) : ℂ :=
  Complex.exp ((y : ℂ)*((σ : ℂ)+(t : ℂ)*I) +
    ((σ : ℂ)+(t : ℂ)*I)^2/(4*(c : ℂ)^2))

lemma lemma171_gaussian_numerator_split {c : ℝ} (hc : 0 < c) (σ y t : ℝ) :
    lemma171GaussianNumerator c σ y t =
      Complex.exp ((y : ℂ)*(σ : ℂ)+(σ : ℂ)^2/(4*(c : ℂ)^2)) *
      Complex.exp ((I*((y : ℂ)+(σ : ℂ)/(2*(c : ℂ)^2)))*(t : ℂ) -
        ((1/(2*c) : ℝ) : ℂ)^2*(t : ℂ)^2) := by
  rw [← Complex.exp_add]
  unfold lemma171GaussianNumerator
  congr 1
  push_cast
  field_simp [show (c : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hc.ne']
  ring_nf
  rw [I_sq]
  ring

lemma lemma171_gaussian_numerator_integrable {c : ℝ} (hc : 0 < c) (σ y : ℝ) :
    Integrable (lemma171GaussianNumerator c σ y) := by
  have hb : 0 < 1/(2*c) := by positivity
  have hh := (lemma53_gaussian_laplace_integrable hb
    (I*((y : ℂ)+(σ : ℂ)/(2*(c : ℂ)^2)))).const_mul
    (Complex.exp ((y : ℂ)*(σ : ℂ)+(σ : ℂ)^2/(4*(c : ℂ)^2)))
  rw [funext (lemma171_gaussian_numerator_split hc σ y)]
  exact hh

lemma lemma171_gaussian_numerator_integral {c : ℝ} (hc : 0 < c) (σ y : ℝ) :
    (∫ t : ℝ, lemma171GaussianNumerator c σ y t) =
      ((2*c*Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-(c : ℂ)^2*(y : ℂ)^2) := by
  have hb : 0 < 1/(2*c) := by positivity
  simp_rw [lemma171_gaussian_numerator_split hc]
  rw [integral_const_mul, lemma53_gaussian_laplace hb]
  have hcoef : ((Real.sqrt Real.pi / (1/(2*c)) : ℝ) : ℂ) =
      ((2*c*Real.sqrt Real.pi : ℝ) : ℂ) := by
    congr 1
    field_simp
    <;> ring
  rw [hcoef]
  have hexp : (y : ℂ)*(σ : ℂ)+(σ : ℂ)^2/(4*(c : ℂ)^2) +
      (I*((y : ℂ)+(σ : ℂ)/(2*(c : ℂ)^2)))^2 /
        (4*((1/(2*c) : ℝ) : ℂ)^2) = -(c : ℂ)^2*(y : ℂ)^2 := by
    push_cast
    field_simp [show (c : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hc.ne']
    ring_nf
    rw [I_sq]
    ring
  calc
    _ = ((2*c*Real.sqrt Real.pi : ℝ) : ℂ) *
      Complex.exp ((y : ℂ)*(σ : ℂ)+(σ : ℂ)^2/(4*(c : ℂ)^2) +
        (I*((y : ℂ)+(σ : ℂ)/(2*(c : ℂ)^2)))^2 /
          (4*((1/(2*c) : ℝ) : ℂ)^2)) := by
      conv_rhs => rw [Complex.exp_add]
      ring
    _ = _ := by rw [hexp]

lemma lemma171_vertical_denominator_ne_zero {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    (σ : ℂ)+(t : ℂ)*I ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  exact hσ (by simpa using hh)

lemma lemma171_integrable_div_vertical {σ : ℝ} (hσ : σ ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => f t / ((σ : ℂ)+(t : ℂ)*I)) := by
  apply (hf.norm.div_const |σ|).mono'
  · exact hf.aestronglyMeasurable.div₀ (by fun_prop)
  · filter_upwards [] with t
    rw [norm_div]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (abs_pos.mpr hσ)
    simpa using Complex.abs_re_le_norm ((σ : ℂ)+(t : ℂ)*I)

lemma lemma171_gaussian_second_kernel_integrable {c σ : ℝ} (hc : 0 < c)
    (hσ : σ ≠ 0) (y : ℝ) :
    Integrable (fun t : ℝ => lemma171GaussianNumerator c σ y t /
      ((σ : ℂ)+(t : ℂ)*I)^2) := by
  have hh := lemma171_integrable_div_vertical hσ
    (lemma171_integrable_div_vertical hσ (lemma171_gaussian_numerator_integrable hc σ y))
  simpa only [div_div, ← pow_two] using hh

lemma lemma171_gaussian_first_kernel_hasDerivAt {c σ : ℝ} (hc : 0 < c)
    (hσ : σ ≠ 0) (y t : ℝ) :
    HasDerivAt
      (fun u : ℝ => lemma171GaussianNumerator c σ y u / ((σ : ℂ)+(u : ℂ)*I))
      (I*((y : ℂ)*(lemma171GaussianNumerator c σ y t / ((σ : ℂ)+(t : ℂ)*I)) +
        lemma171GaussianNumerator c σ y t/(2*(c : ℂ)^2) -
        lemma171GaussianNumerator c σ y t/((σ : ℂ)+(t : ℂ)*I)^2)) t := by
  have hz : HasDerivAt (fun u : ℝ => (σ : ℂ)+(u : ℂ)*I) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (σ : ℂ)
  have he := ((hz.const_mul (y : ℂ)).add ((hz.pow 2).div_const (4*(c : ℂ)^2))).cexp
  have hd := he.div hz (lemma171_vertical_denominator_ne_zero hσ t)
  apply hd.congr_deriv
  dsimp only [lemma171GaussianNumerator, Pi.add_apply, Pi.pow_apply, Pi.div_apply,
    Pi.mul_apply] 
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  field_simp [lemma171_vertical_denominator_ne_zero hσ t,
    show (c : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hc.ne']
  <;> ring

/-- Integration by parts on the actual Gaussian kernel raises the Perron pole
from order one to order two, with an explicit Gaussian density correction. -/
lemma lemma171_gaussian_second_kernel_integral {c σ : ℝ} (hc : 0 < c)
    (hσ : σ ≠ 0) (y : ℝ) :
    (∫ t : ℝ, lemma171GaussianNumerator c σ y t / ((σ : ℂ)+(t : ℂ)*I)^2) =
      (y : ℂ)*(∫ t : ℝ, lemma171GaussianNumerator c σ y t / ((σ : ℂ)+(t : ℂ)*I)) +
      ((Real.sqrt Real.pi / c : ℝ) : ℂ)*Complex.exp (-(c : ℂ)^2*(y : ℂ)^2) := by
  have hE := lemma171_gaussian_numerator_integrable hc σ y
  have hH := lemma171_integrable_div_vertical hσ hE
  have hK := lemma171_gaussian_second_kernel_integrable hc hσ y
  have hderint := ((hH.const_mul (y : ℂ)).add (hE.div_const (2*(c : ℂ)^2))).sub hK
  have hsum : Integrable (fun t : ℝ =>
      (y : ℂ) * (lemma171GaussianNumerator c σ y t / ((σ : ℂ)+(t : ℂ)*I)) +
        lemma171GaussianNumerator c σ y t / (2*(c : ℂ)^2)) :=
    (hH.const_mul (y : ℂ)).add (hE.div_const (2*(c : ℂ)^2))
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable
    (lemma171_gaussian_first_kernel_hasDerivAt hc hσ y) (hderint.const_mul I) hH
  rw [integral_const_mul, integral_sub hsum hK,
    integral_add (hH.const_mul (y : ℂ)) (hE.div_const (2*(c : ℂ)^2)),
    integral_const_mul, integral_div, lemma171_gaussian_numerator_integral hc] at hz
  have hh : (y : ℂ)*(∫ t : ℝ, lemma171GaussianNumerator c σ y t / ((σ : ℂ)+(t : ℂ)*I)) +
      ((2*c*Real.sqrt Real.pi : ℝ) : ℂ)*Complex.exp (-(c : ℂ)^2*(y : ℂ)^2)/(2*(c : ℂ)^2) -
      (∫ t : ℝ, lemma171GaussianNumerator c σ y t / ((σ : ℂ)+(t : ℂ)*I)^2) = 0 :=
    (mul_eq_zero.mp hz).resolve_left I_ne_zero
  have hcoef : ((2*c*Real.sqrt Real.pi : ℝ) : ℂ)/(2*(c : ℂ)^2) =
      ((Real.sqrt Real.pi / c : ℝ) : ℂ) := by
    push_cast
    field_simp [show (c : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hc.ne']
    <;> ring
  rw [mul_div_right_comm, hcoef] at hh
  linear_combination -hh

end ZhangLS.Spec
