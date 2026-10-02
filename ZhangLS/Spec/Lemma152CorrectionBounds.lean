import ZhangLS.Spec.Lemma152LocalCorrection
import ZhangLS.Spec.Lemma83RegularProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma152CorrectionConstant : ℝ :=
  8/(1-lemma83RegularRadius)+32/(1-lemma83RegularRadius)^2

lemma lemma152_correction_constant_pos : 0 < lemma152CorrectionConstant := by
  unfold lemma152CorrectionConstant
  have h := sub_pos.mpr lemma83_regular_radius_lt_one
  positivity

lemma lemma152_one_sub_norm_lower {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    1-R ≤ ‖1-z‖ := by
  have h := norm_sub_norm_le (1:ℂ) z
  rw [norm_one] at h
  linarith

lemma lemma152_correction_norm_error (a b u v x : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1)
    (hx : ‖x‖ ≤ lemma83RegularRadius) :
    ‖lemma152LocalCorrection a b u v x-1‖ ≤ lemma152CorrectionConstant*‖u‖*‖x‖ := by
  have hR := sub_pos.mpr lemma83_regular_radius_lt_one
  have hvu : ‖v*u‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hu
  have hvx : ‖v*x‖ ≤ lemma83RegularRadius := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hx
  have hu' := lemma152_one_sub_norm_lower hu
  have hvu' := lemma152_one_sub_norm_lower hvu
  have hx' := lemma152_one_sub_norm_lower hx
  have hvx' := lemma152_one_sub_norm_lower hvx
  have ha' : ‖a-1‖ ≤ 2 := by have := norm_sub_le a (1:ℂ); simp only [norm_one] at this; linarith
  have hb' : ‖b-1‖ ≤ 2 := by have := norm_sub_le b (1:ℂ); simp only [norm_one] at this; linarith
  have hx1 : ‖x‖ ≤ 1 := hx.trans lemma83_regular_radius_lt_one.le
  have hux : ‖1-u*x‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul]
    nlinarith [norm_nonneg u,norm_nonneg x]
  have hab : ‖a+b-1‖ ≤ 3 := by
    apply (norm_sub_le _ _).trans
    have hh := norm_add_le a b
    rw [norm_one]
    linarith
  have hv2 : ‖v^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg v]
  have hcoef : ‖v^2*(a+b-1)-v‖ ≤ 4 := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    have hh := mul_le_mul hv2 hab (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith
  have hn1 : ‖u*x*(v^2*(a+b-1)-v)‖ ≤ 4*‖u‖*‖x‖ := by
    simp only [norm_mul]
    nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg x),
      mul_le_mul_of_nonneg_left hcoef (mul_nonneg (norm_nonneg u) (norm_nonneg x))]
  have hn2 : ‖v*u*x*(a-1)*(b-1)*(1-u*x)‖ ≤ 8*‖u‖*‖x‖ := by
    simp only [norm_mul]
    calc
      _ ≤ 1*‖u‖*‖x‖*2*2*2 := by gcongr
      _ = _ := by ring
  have hd1 : (1/2)*(1-lemma83RegularRadius) ≤ ‖(1-u)*(1-v*x)‖ := by
    rw [norm_mul]
    apply mul_le_mul (by linarith [hu']) hvx' hR.le (norm_nonneg _)
  have hd2 : (1/4)*(1-lemma83RegularRadius)^2 ≤ ‖(1-u)*(1-v*u)*(1-x)*(1-v*x)‖ := by
    simp only [norm_mul]
    calc
      _ = (1/2)*(1/2)*(1-lemma83RegularRadius)*(1-lemma83RegularRadius) := by ring
      _ ≤ _ := by gcongr <;> linarith
  have hh1 : ‖u*x*(v^2*(a+b-1)-v)/((1-u)*(1-v*x))‖ ≤
      (4*‖u‖*‖x‖)/((1/2)*(1-lemma83RegularRadius)) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hn1 (by positivity) hd1
  have hh2 : ‖v*u*x*(a-1)*(b-1)*(1-u*x)/((1-u)*(1-v*u)*(1-x)*(1-v*x))‖ ≤
      (8*‖u‖*‖x‖)/((1/4)*(1-lemma83RegularRadius)^2) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hn2 (by positivity) hd2
  unfold lemma152LocalCorrection
  rw [show 1+u*x*(v^2*(a+b-1)-v)/((1-u)*(1-v*x))-
      v*u*x*(a-1)*(b-1)*(1-u*x)/((1-u)*(1-v*u)*(1-x)*(1-v*x))-1 =
      u*x*(v^2*(a+b-1)-v)/((1-u)*(1-v*x))-
        v*u*x*(a-1)*(b-1)*(1-u*x)/((1-u)*(1-v*u)*(1-x)*(1-v*x)) by ring]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hh1 hh2).trans
  apply le_of_eq
  unfold lemma152CorrectionConstant
  field_simp
  ring

end ZhangLS.Spec
