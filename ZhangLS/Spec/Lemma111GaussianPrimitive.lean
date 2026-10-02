import ZhangLS.Spec.Lemma57GaussianMellinTransform
import ZhangLS.Spec.Lemma23GoodSet

/-!
# The exact Gaussian primitive underlying Lemma 11.1

These are analytic facts for the actual smoothing weight from (4.1).
The coordinate `t` is the exponent of `P`, so the Gaussian scale is
`L^15 log P = L^24`. No character or good-set hypothesis is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZhangLS.Spec

open MeasureTheory
open scoped Real

noncomputable def lemma111Scale (D : ℕ) : ℝ := lemma23PaperL D ^ 24

noncomputable def lemma111Profile (D : ℕ) (t : ℝ) : ℝ :=
  zhangGaussianWeight D (Real.exp (lemma23PaperL D ^ 9 * t))

noncomputable def lemma111Primitive (D : ℕ) (t : ℝ) : ℝ :=
  t * lemma111Profile D t +
    Real.exp (-((lemma111Scale D * t) ^ 2)) /
      (2 * lemma111Scale D * Real.sqrt Real.pi)

lemma lemma111_scale_pos {D : ℕ} (hD : 1 < D) : 0 < lemma111Scale D := by
  exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _

lemma lemma111_endpoint (D : ℕ) (t : ℝ) :
    zhangGaussianEndpoint D (Real.exp (lemma23PaperL D ^ 9 * t)) =
      lemma111Scale D * t := by
  simp only [zhangGaussianEndpoint, Real.log_exp, lemma111Scale, lemma23PaperL]
  ring

lemma lemma111_profile_formula (D : ℕ) (t : ℝ) :
    lemma111Profile D t = 1 / 2 + (Real.sqrt Real.pi)⁻¹ *
      ∫ x in (0 : ℝ)..(lemma111Scale D * t), Real.exp (-(x ^ 2)) := by
  rw [lemma111Profile, zhangGaussianWeight, lemma111_endpoint]

lemma lemma111_profile_nonneg {D : ℕ} (hD : 1 < D) (t : ℝ) :
    0 ≤ lemma111Profile D t :=
  zhangGaussianWeight_nonneg hD (Real.exp_pos _)

lemma lemma111_profile_complement (D : ℕ) (t : ℝ) :
    lemma111Profile D t + lemma111Profile D (-t) = 1 := by
  simpa only [lemma111Profile, mul_neg] using
    zhangGaussianWeight_exp_add_neg (D := D) (lemma23PaperL D ^ 9 * t)

lemma lemma111_profile_le_one {D : ℕ} (hD : 1 < D) (t : ℝ) :
    lemma111Profile D t ≤ 1 := by
  linarith [lemma111_profile_complement D t, lemma111_profile_nonneg hD (-t)]

lemma lemma111_profile_hasDerivAt (D : ℕ) (t : ℝ) :
    HasDerivAt (lemma111Profile D)
      (lemma111Scale D / Real.sqrt Real.pi *
        Real.exp (-((lemma111Scale D * t) ^ 2))) t := by
  have hc : Continuous (fun x : ℝ => Real.exp (-(x ^ 2))) := by fun_prop
  have hi := (hc.integral_hasStrictDerivAt 0 (lemma111Scale D * t)).hasDerivAt
  have hs : HasDerivAt (fun x : ℝ => lemma111Scale D * x) (lemma111Scale D) t := by
    simpa using (hasDerivAt_id t).const_mul (lemma111Scale D)
  have hd := ((hi.comp t hs).const_mul (Real.sqrt Real.pi)⁻¹).const_add (1 / 2 : ℝ)
  convert hd using 1
  · ext x
    exact lemma111_profile_formula D x
  · dsimp
    ring

lemma lemma111_profile_continuous (D : ℕ) : Continuous (lemma111Profile D) :=
  continuous_iff_continuousAt.mpr fun t => (lemma111_profile_hasDerivAt D t).continuousAt

/-- An exact primitive; the Gaussian correction cancels the derivative of
`t * g(P^t)`. -/
lemma lemma111_primitive_hasDerivAt {D : ℕ} (hD : 1 < D) (t : ℝ) :
    HasDerivAt (lemma111Primitive D) (lemma111Profile D t) t := by
  have hA := (lemma111_scale_pos hD).ne'
  have hπ := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he : HasDerivAt
      (fun x : ℝ => Real.exp (-((lemma111Scale D * x) ^ 2)))
      (Real.exp (-((lemma111Scale D * t) ^ 2)) *
        (-(2 * (lemma111Scale D * t) * lemma111Scale D))) t := by
    convert ((((hasDerivAt_id t).const_mul (lemma111Scale D)).pow 2).neg).exp using 1
    simp
  have hd := ((hasDerivAt_id t).mul (lemma111_profile_hasDerivAt D t)).add
    (he.div_const (2 * lemma111Scale D * Real.sqrt Real.pi))
  convert hd using 1
  simp only [id_eq]
  field_simp
  ring

lemma lemma111_integral_profile {D : ℕ} (hD : 1 < D) (a b u : ℝ) :
    (∫ z in a..b, lemma111Profile D (z - u)) =
      lemma111Primitive D (b - u) - lemma111Primitive D (a - u) := by
  rw [intervalIntegral.integral_comp_sub_right]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => lemma111_primitive_hasDerivAt hD t)
    ((lemma111_profile_continuous D).intervalIntegrable _ _)

/-- The exact symmetric-interval cancellation used explicitly in the paper. -/
lemma lemma111_reflected_integral (D : ℕ) (a u : ℝ) :
    (∫ z in a..(2 * u - a), lemma111Profile D (z - u)) = u - a := by
  have hi : IntervalIntegrable (fun z => lemma111Profile D (z - u))
      volume a (2 * u - a) :=
    ((lemma111_profile_continuous D).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hr := intervalIntegral.integral_comp_sub_left
    (fun z => lemma111Profile D (z - u)) (a := a) (b := 2 * u - a) (2 * u)
  have hreflect : (∫ z in a..(2 * u - a), lemma111Profile D (-(z - u))) =
      ∫ z in a..(2 * u - a), lemma111Profile D (z - u) := by
    have hstart : 2 * u - (2 * u - a) = a := by ring
    rw [hstart] at hr
    convert hr using 1
    congr 1
    ext z
    congr 1
    ring
  have hi' : IntervalIntegrable (fun z => lemma111Profile D (-(z - u)))
      volume a (2 * u - a) :=
    ((lemma111_profile_continuous D).comp ((continuous_id.sub continuous_const).neg)).intervalIntegrable _ _
  have hadd := intervalIntegral.integral_add hi hi'
  have hc : (fun z => lemma111Profile D (z - u) + lemma111Profile D (-(z - u))) =
      fun _ : ℝ => (1 : ℝ) := by
    ext z
    exact lemma111_profile_complement D (z - u)
  rw [hc, intervalIntegral.integral_const, hreflect] at hadd
  simp only [smul_eq_mul, mul_one] at hadd
  linarith

end ZhangLS.Spec
