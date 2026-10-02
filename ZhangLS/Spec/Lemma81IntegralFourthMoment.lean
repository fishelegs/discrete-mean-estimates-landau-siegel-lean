import ZhangLS.Spec.Lemma34WeightedCauchy
import ZhangLS.Spec.Lemma81SixOnePolynomialMoments

/-! # Fourth-power integral mean from two Cauchy inequalities

This is the real integral estimate used for the genuine Gaussian error in
Lemma 6.1. Actual continuity will discharge every integrability condition.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open MeasureTheory Set
open scoped Topology
set_option maxHeartbeats 2000000

lemma lemma81_interval_cauchy_square (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (uIcc a b)) :
    (∫ x in a..b, f x)^2 ≤ (b-a) * (∫ x in a..b, (f x)^2) := by
  let μ := volume.restrict (Ioc a b)
  have hw : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable a b).1
  have hfw : Integrable (fun x => f x*1) μ := by simpa only [mul_one] using hf.intervalIntegrable.1
  have hf2w : Integrable (fun x => f x^2*1) μ := by
    simpa only [mul_one] using (hf.pow 2).intervalIntegrable.1
  have hW : (∫ x, (1 : ℝ) ∂μ) = b-a := by
    rw [← intervalIntegral.integral_of_le hab.le]
    simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one]
  have hh := lemma34_weighted_integral_cauchy μ f (fun _ => 1) hw hfw hf2w
    (Filter.Eventually.of_forall (fun _ => by norm_num)) (by rw [hW]; exact sub_pos.mpr hab)
  rw [hW] at hh
  simpa only [mul_one,intervalIntegral.integral_of_le hab.le] using hh

lemma lemma81_interval_fourth_power (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (uIcc a b)) :
    (∫ x in a..b, f x)^4 ≤ (b-a)^3 * (∫ x in a..b, f x^4) := by
  have h₁ := lemma81_interval_cauchy_square f hab hf
  have h₂ := lemma81_interval_cauchy_square (fun x => f x^2) hab (hf.pow 2)
  simp only [← pow_mul] at h₂
  have hI : 0 ≤ ∫ x in a..b, f x^2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun x => sq_nonneg (f x))
  have hlen : 0 ≤ b-a := sub_nonneg.mpr hab.le
  have hsq := (sq_le_sq₀ (sq_nonneg (∫ x in a..b, f x)) (mul_nonneg hlen hI)).mpr h₁
  calc
    _ = ((∫ x in a..b, f x)^2)^2 := by ring
    _ ≤ ((b-a)*(∫ x in a..b, f x^2))^2 := hsq
    _ = (b-a)^2 * (∫ x in a..b, f x^2)^2 := by ring
    _ ≤ (b-a)^2 * ((b-a)*(∫ x in a..b, f x^4)) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring

/-- Summing the fourth-power integral inequality needs only a uniform actual
pointwise fourth moment, without interchanging an infinite series. -/
lemma lemma81_finite_family_integral_fourth {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℝ) {a b M : ℝ} (hab : a < b)
    (hf : ∀ i ∈ S, ContinuousOn (f i) (uIcc a b))
    (hm : ∀ x ∈ uIcc a b, (∑ i ∈ S, f i x^4) ≤ M) :
    (∑ i ∈ S, (∫ x in a..b, f i x)^4) ≤ (b-a)^4*M := by
  have hf4 : ∀ i ∈ S, IntervalIntegrable (fun x => f i x^4) volume a b :=
    fun i hi => ((hf i hi).pow 4).intervalIntegrable
  have hsumint : IntervalIntegrable (fun x => ∑ i ∈ S, f i x^4) volume a b := by
    have he : (∑ i ∈ S, fun x => f i x^4) = (fun x => ∑ i ∈ S, f i x^4) := by
      funext x
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum S hf4
  have hi : (∫ x in a..b, ∑ i ∈ S, f i x^4) ≤ (b-a)*M := by
    have hb := intervalIntegral.integral_mono_on hab.le hsumint
      ((continuous_const : Continuous (fun _ : ℝ => M)).intervalIntegrable a b)
      (fun x hx => hm x (by rwa [uIcc_of_le hab.le]))
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hb
  calc
    _ ≤ ∑ i ∈ S, (b-a)^3 * (∫ x in a..b, f i x^4) :=
      Finset.sum_le_sum (fun i hi => lemma81_interval_fourth_power (f i) hab (hf i hi))
    _ = (b-a)^3 * (∫ x in a..b, ∑ i ∈ S, f i x^4) := by
      rw [← Finset.mul_sum,intervalIntegral.integral_finsetSum hf4]
    _ ≤ (b-a)^3 * ((b-a)*M) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

end ZhangLS.Spec
