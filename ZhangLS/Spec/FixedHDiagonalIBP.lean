import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! General real-profile identities on a finite interval. No arithmetic inputs. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHDiagonal
open MeasureTheory Set
open scoped Interval

noncomputable def tail (f : ℝ → ℝ) (b x : ℝ) : ℝ := ∫ y in x..b, f y

lemma tail_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (b x : ℝ) :
    HasDerivAt (tail f b) (-f x) x := by
  exact intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable x b)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

lemma tail_continuous {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ) :
    Continuous (tail f b) := by
  exact (show Differentiable ℝ (tail f b) from
    fun x => (tail_hasDerivAt hf b x).differentiableAt).continuous

/-- Exact sign: the terminal integral has derivative `-f`, so IBP gives `+∫f²`.
Only the value at the left endpoint is needed; the tail vanishes at the right. -/
theorem integral_deriv_tail {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt f (f' x) x) (ha : f a = 0) :
    (∫ x in a..b, f' x * tail f b x) = ∫ x in a..b, (f x)^2 := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf.continuousOn (tail_continuous hf b).continuousOn
    (fun x _ => hd x) (fun x _ => tail_hasDerivAt hf b x)
    (hf'.intervalIntegrable a b) (hf.neg.intervalIntegrable a b)
  have hn : (∫ x in a..b, f x * (-f x)) = -(∫ x in a..b, (f x)^2) := by
    simp only [mul_neg, ← pow_two, intervalIntegral.integral_neg]
  rw [hn] at h
  have h' : -(∫ x in a..b, (f x)^2) = -(∫ x in a..b, f' x * tail f b x) := by
    simpa [tail, ha] using h
  exact (neg_inj.mp h').symm

/-- A C² specialization, independent of any particular fixed profile. -/
theorem integral_deriv_tail_c2 {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ 2 f) (ha : f a = 0) :
    (∫ x in a..b, deriv f x * tail f b x) = ∫ x in a..b, (f x)^2 := by
  exact integral_deriv_tail hf.continuous (hf.continuous_deriv (by norm_num))
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt) ha

end ZhangLS.Spec.FixedHDiagonal
