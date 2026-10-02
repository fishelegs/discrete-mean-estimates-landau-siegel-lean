import ZhangLS.Spec.Lemma56GaussianRightTruncation
import ZhangLS.Spec.Lemma57GaussianMellinTransform

/-! # Actual cumulative Gaussian Perron kernel at arbitrary positive width

Its scalar inverse Mellin identity is obtained by rescaling the already
proved cumulative Gaussian formula at the fixed modulus two.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PerronBaseScale : ℝ := (Real.log (2 : ℝ)) ^ 15

noncomputable def lemma56PerronWeight (B x : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (Real.sqrt Real.pi)⁻¹ *
    ∫ v : ℝ in (0 : ℝ)..B * Real.log x, Real.exp (-(v ^ 2))

noncomputable def lemma56PerronKernel (B σ x t : ℝ) : ℂ :=
  (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) *
    Complex.exp (((σ : ℂ) + (t : ℂ) * I) ^ 2 / (4 * (B : ℂ) ^ 2)) /
      ((σ : ℂ) + (t : ℂ) * I)

lemma lemma56_perron_base_scale_pos : 0 < lemma56PerronBaseScale := by
  unfold lemma56PerronBaseScale
  exact pow_pos (Real.log_pos (by norm_num)) _

lemma lemma56_perron_weight_rescale {B x : ℝ} (hx : 0 < x) :
    lemma56PerronWeight B x = zhangGaussianWeight 2 (x ^ (B / lemma56PerronBaseScale)) := by
  unfold lemma56PerronWeight zhangGaussianWeight zhangGaussianEndpoint
  rw [Real.log_rpow hx]
  have he : (Real.log (2 : ℝ)) ^ 15 * (B / lemma56PerronBaseScale * Real.log x) =
      B * Real.log x := by
    unfold lemma56PerronBaseScale
    field_simp
  norm_num only [Nat.cast_ofNat]
  rw [he]

lemma lemma56_perron_kernel_rescale {B σ x : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hx : 0 < x) (t : ℝ) :
    let k := lemma56PerronBaseScale / B
    lemma56PerronKernel B σ x t = (k : ℂ) *
      lemma57GaussianKernelIntegrand 2 (k * σ) (x ^ (B / lemma56PerronBaseScale)) (k * t) := by
  let k := lemma56PerronBaseScale / B
  let y := x ^ (B / lemma56PerronBaseScale)
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hk : 0 < k := div_pos lemma56_perron_base_scale_pos hB
  have hBN : (B : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB.ne'
  have hbaseN : (lemma56PerronBaseScale : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr lemma56_perron_base_scale_pos.ne'
  have hkN : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have hy : 0 < y := Real.rpow_pos_of_pos hx _
  have hs : s ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    have hsz : σ = 0 := by simpa [s] using hh
    exact hσ.ne' hsz
  have hpoint : ((k * σ : ℝ) : ℂ) + ((k * t : ℝ) : ℂ) * I = (k : ℂ) * s := by
    dsimp [s]
    push_cast
    ring
  have hpower : (y : ℂ) ^ ((k : ℂ) * s) = (x : ℂ) ^ s := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hy.le, ← Complex.ofReal_log hx.le]
    dsimp [y]
    rw [Real.log_rpow hx]
    congr 1
    dsimp [k]
    push_cast
    field_simp [hBN, hbaseN]
  have hden : (Real.log (2 : ℝ) : ℂ) ^ 30 = (lemma56PerronBaseScale : ℂ) ^ 2 := by
    unfold lemma56PerronBaseScale
    norm_cast
    ring
  have hex : ((k : ℂ) * s) ^ 2 / (4 * (Real.log (2 : ℝ) : ℂ) ^ 30) =
      s ^ 2 / (4 * (B : ℂ) ^ 2) := by
    rw [hden]
    dsimp [k]
    push_cast
    field_simp [hBN, hbaseN]
  change lemma56PerronKernel B σ x t = (k : ℂ) *
    lemma57GaussianKernelIntegrand 2 (k * σ) y (k * t)
  unfold lemma56PerronKernel lemma57GaussianKernelIntegrand lemma57OmegaOne
  norm_num only [Nat.cast_ofNat]
  rw [hpoint, hpower, hex]
  change (x : ℂ) ^ s * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) / s = _
  field_simp [hkN, hs]

theorem lemma56_perron_kernel_integrable {B σ x : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hx : 0 < x) : Integrable (lemma56PerronKernel B σ x) := by
  let k := lemma56PerronBaseScale / B
  let y := x ^ (B / lemma56PerronBaseScale)
  have hk : 0 < k := div_pos lemma56_perron_base_scale_pos hB
  have hy : 0 < y := Real.rpow_pos_of_pos hx _
  have hσ' : 0 < k * σ := mul_pos hk hσ
  have hi := lemma57GaussianKernel_integrable (D := 2) (by norm_num) hσ'.ne' hy
  have hc : Integrable (fun t : ℝ => lemma57GaussianKernelIntegrand 2 (k * σ) y (k * t)) :=
    (MeasureTheory.integrable_comp_mul_left_iff _ hk.ne').mpr hi
  apply (hc.const_mul (k : ℂ)).congr
  filter_upwards [] with t
  exact (lemma56_perron_kernel_rescale hB hσ hx t).symm

theorem lemma56_perron_kernel_integral {B σ x : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, lemma56PerronKernel B σ x t =
      (lemma56PerronWeight B x : ℂ) := by
  let k := lemma56PerronBaseScale / B
  let y := x ^ (B / lemma56PerronBaseScale)
  have hk : 0 < k := div_pos lemma56_perron_base_scale_pos hB
  have hy : 0 < y := Real.rpow_pos_of_pos hx _
  have hσ' : 0 < k * σ := mul_pos hk hσ
  have hi := lemma57GaussianKernelVerticalIntegral_eq_weight (D := 2)
    (by norm_num) hσ' hy
  have hi' : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, lemma57GaussianKernelIntegrand 2 (k * σ) y t =
        (zhangGaussianWeight 2 y : ℂ) := by
    unfold lemma57GaussianKernelVerticalIntegral at hi
    rw [MeasureTheory.integral_mul_const] at hi
    convert hi using 1
    push_cast
    field_simp
  have heq (t : ℝ) : lemma56PerronKernel B σ x t =
      (k : ℂ) * lemma57GaussianKernelIntegrand 2 (k * σ) y (k * t) :=
    lemma56_perron_kernel_rescale hB hσ hx t
  simp_rw [heq]
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hk), Complex.real_smul]
  rw [← lemma56_perron_weight_rescale hx] at hi'
  convert hi' using 1
  push_cast
  field_simp [ofReal_ne_zero.mpr hk.ne']

end ZhangLS.Spec
