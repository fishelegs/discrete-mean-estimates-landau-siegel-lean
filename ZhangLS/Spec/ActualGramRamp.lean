import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact compact-interval ramp identities. Terminal values of both f and f'
are explicit; no discarded lower tail or approximate profile expansion occurs.
The shift ell is arbitrary, hence includes the genuine mu=6 smoothing shift. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Interval

noncomputable def actualGramRampDensity (ell : ℂ) (f f' f'' : ℝ → ℂ) (v : ℝ) : ℂ :=
  f'' v + 2*ell*f' v + ell^2*f v

lemma actualGram_ramp_antiderivative (ell : ℂ) (f f' f'' : ℝ → ℂ)
    (t v : ℝ) (hf : HasDerivAt f (f' v) v) (hf' : HasDerivAt f' (f'' v) v) :
    HasDerivAt (fun u : ℝ => Complex.exp (ell * (u-t : ℝ)) *
      ((u-t : ℝ)*f' u + (ell*(u-t : ℝ)-1)*f u))
      (actualGramRampDensity ell f f' f'' v * (v-t : ℝ) *
        Complex.exp (ell*(v-t : ℝ))) v := by
  have hx : HasDerivAt (fun u : ℝ => ((u-t : ℝ) : ℂ)) 1 v := by
    simpa using ((hasDerivAt_id v).sub_const t).ofReal_comp
  have he := (hx.const_mul ell).cexp
  convert he.mul ((hx.mul hf').add (((hx.const_mul ell).sub_const 1).mul hf)) using 1 <;>
    simp only [actualGramRampDensity, mul_one, sub_zero, Pi.add_apply, Pi.mul_apply] <;> push_cast <;> ring

/-- Exact exponential ramp, including the normalization and terminal traces. -/
theorem actualGram_ramp_identity (ell : ℂ) (f f' f'' : ℝ → ℂ) (t b : ℝ)
    (hf : ∀ v ∈ uIcc t b, HasDerivAt f (f' v) v)
    (hf' : ∀ v ∈ uIcc t b, HasDerivAt f' (f'' v) v)
    (hi : IntervalIntegrable (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      (v-t : ℝ) * Complex.exp (ell*(v-t : ℝ))) volume t b)
    (hfb : f b = 0) (hfpb : f' b = 0) :
    (∫ v in t..b, actualGramRampDensity ell f f' f'' v * (v-t : ℝ) *
      Complex.exp (ell*(v-t : ℝ))) = f t := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => actualGram_ramp_antiderivative ell f f' f'' t v (hf v hv) (hf' v hv)) hi
  simpa [hfb, hfpb] using he

lemma actualGram_exponential_antiderivative (ell : ℂ) (f f' f'' : ℝ → ℂ)
    (t v : ℝ) (hf : HasDerivAt f (f' v) v) (hf' : HasDerivAt f' (f'' v) v) :
    HasDerivAt (fun u : ℝ => Complex.exp (ell*(u-t : ℝ)) * (f' u + ell*f u))
      (actualGramRampDensity ell f f' f'' v * Complex.exp (ell*(v-t : ℝ))) v := by
  have hx : HasDerivAt (fun u : ℝ => ((u-t : ℝ) : ℂ)) 1 v := by
    simpa using ((hasDerivAt_id v).sub_const t).ofReal_comp
  convert (hx.const_mul ell).cexp.mul (hf'.add (hf.const_mul ell)) using 1 <;>
    simp only [actualGramRampDensity, mul_one, Pi.add_apply, Pi.mul_apply] <;> push_cast <;> ring

/-- Exact mass companion to the ramp identity. -/
theorem actualGram_exponential_identity (ell : ℂ) (f f' f'' : ℝ → ℂ) (t b : ℝ)
    (hf : ∀ v ∈ uIcc t b, HasDerivAt f (f' v) v)
    (hf' : ∀ v ∈ uIcc t b, HasDerivAt f' (f'' v) v)
    (hi : IntervalIntegrable (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      Complex.exp (ell*(v-t : ℝ))) volume t b)
    (hfb : f b = 0) (hfpb : f' b = 0) :
    (∫ v in t..b, actualGramRampDensity ell f f' f'' v *
      Complex.exp (ell*(v-t : ℝ))) = -f' t - ell*f t := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => actualGram_exponential_antiderivative ell f f' f'' t v (hf v hv) (hf' v hv)) hi
  simpa [hfb, hfpb, neg_add, sub_eq_add_neg, add_comm] using he

/-- Superposing the literal first smoothing main kernel gives -f'-beta*f.
Both interval-integrability inputs are independently checkable from a C2
profile. They are not hypotheses about any arithmetic or Gram error. -/
theorem actualGram_first_main_identity (ell beta : ℂ) (f f' f'' : ℝ → ℂ) (t b : ℝ)
    (hf : ∀ v ∈ uIcc t b, HasDerivAt f (f' v) v)
    (hf' : ∀ v ∈ uIcc t b, HasDerivAt f' (f'' v) v)
    (hi0 : IntervalIntegrable (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      Complex.exp (ell*(v-t : ℝ))) volume t b)
    (hi1 : IntervalIntegrable (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      (v-t : ℝ) * Complex.exp (ell*(v-t : ℝ))) volume t b)
    (hfb : f b = 0) (hfpb : f' b = 0) :
    (∫ v in t..b, actualGramRampDensity ell f f' f'' v *
      (1+(ell-beta)*(v-t : ℝ))*Complex.exp (ell*(v-t : ℝ))) = -f' t - beta*f t := by
  have he : (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      (1+(ell-beta)*(v-t : ℝ))*Complex.exp (ell*(v-t : ℝ))) =
      (fun v => actualGramRampDensity ell f f' f'' v * Complex.exp (ell*(v-t : ℝ)) +
        (ell-beta)*(actualGramRampDensity ell f f' f'' v * (v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)))) := by
    funext v
    ring
  rw [he, intervalIntegral.integral_add hi0 (hi1.const_mul (ell-beta)),
    intervalIntegral.integral_const_mul,
    actualGram_exponential_identity ell f f' f'' t b hf hf' hi0 hfb hfpb,
    actualGram_ramp_identity ell f f' f'' t b hf hf' hi1 hfb hfpb]
  ring

/-- The density has an exact unweighted integral; its Volterra part is kept. -/
theorem actualGram_density_integral (ell : ℂ) (f f' f'' : ℝ → ℂ) (t b : ℝ)
    (hf : ∀ v ∈ uIcc t b, HasDerivAt f (f' v) v)
    (hf' : ∀ v ∈ uIcc t b, HasDerivAt f' (f'' v) v)
    (hi : IntervalIntegrable (actualGramRampDensity ell f f' f'') volume t b)
    (hif : IntervalIntegrable f volume t b) (hfb : f b = 0) (hfpb : f' b = 0) :
    (∫ v in t..b, actualGramRampDensity ell f f' f'' v) =
      -f' t - 2*ell*f t + ell^2*(∫ v in t..b, f v) := by
  have hd (v : ℝ) (hv : v ∈ uIcc t b) :
      HasDerivAt (fun u => f' u + (2*ell)*f u)
        (actualGramRampDensity ell f f' f'' v - ell^2*f v) v := by
    convert (hf' v hv).add ((hf v hv).const_mul (2*ell)) using 1 <;>
      simp only [actualGramRampDensity] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.sub (hif.const_mul (ell^2)))
  rw [intervalIntegral.integral_sub hi (hif.const_mul (ell^2)),
    intervalIntegral.integral_const_mul] at he
  simp only [hfb, hfpb, mul_zero, add_zero, zero_sub] at he
  linear_combination he

/-- Superposing the second smoothing main kernel yields the exact derivative,
local, and positive Volterra terms. For the conjugate profile ell is the
opposite of the original smoothing shift. -/
theorem actualGram_second_main_identity (ell a₁ a₂ : ℂ) (hell : ell ≠ 0)
    (f f' f'' : ℝ → ℂ) (t b : ℝ)
    (hf : ∀ v ∈ uIcc t b, HasDerivAt f (f' v) v)
    (hf' : ∀ v ∈ uIcc t b, HasDerivAt f' (f'' v) v)
    (hi : IntervalIntegrable (actualGramRampDensity ell f f' f'') volume t b)
    (hif : IntervalIntegrable f volume t b)
    (hi0 : IntervalIntegrable (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      Complex.exp (ell*(v-t : ℝ))) volume t b)
    (hi1 : IntervalIntegrable (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      (v-t : ℝ) * Complex.exp (ell*(v-t : ℝ))) volume t b)
    (hfb : f b = 0) (hfpb : f' b = 0) :
    (∫ v in t..b, actualGramRampDensity ell f f' f'' v *
      (a₁*a₂/ell^2 + (1-a₁*a₂/ell^2 +
        (a₁+ell)*(a₂+ell)/ell*(v-t : ℝ))*Complex.exp (ell*(v-t : ℝ)))) =
      -f' t + (a₁+a₂)*f t + a₁*a₂*(∫ v in t..b, f v) := by
  let A : ℂ := a₁*a₂/ell^2
  let B : ℂ := (a₁+ell)*(a₂+ell)/ell
  have he : (fun v : ℝ => actualGramRampDensity ell f f' f'' v *
      (a₁*a₂/ell^2 + (1-a₁*a₂/ell^2 +
        (a₁+ell)*(a₂+ell)/ell*(v-t : ℝ))*Complex.exp (ell*(v-t : ℝ)))) =
      (fun v => A*actualGramRampDensity ell f f' f'' v +
        (1-A)*(actualGramRampDensity ell f f' f'' v*Complex.exp (ell*(v-t : ℝ))) +
        B*(actualGramRampDensity ell f f' f'' v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ)))) := by
    funext v
    dsimp [A, B]
    ring
  rw [he, intervalIntegral.integral_add ((hi.const_mul A).add (hi0.const_mul (1-A))) (hi1.const_mul B),
    intervalIntegral.integral_add (hi.const_mul A) (hi0.const_mul (1-A))]
  simp only [intervalIntegral.integral_const_mul]
  rw [actualGram_density_integral ell f f' f'' t b hf hf' hi hif hfb hfpb,
    actualGram_exponential_identity ell f f' f'' t b hf hf' hi0 hfb hfpb,
    actualGram_ramp_identity ell f f' f'' t b hf hf' hi1 hfb hfpb]
  dsimp [A, B]
  field_simp [hell] <;> ring

end ZhangLS.Spec
