import ZhangLS.Spec.Lemma152CorrectionBounds
import ZhangLS.Spec.Lemma152LocalSeries
import ZhangLS.Spec.Lemma83ProductPerturbation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma152_denominator_bounds (u v x : ℂ)
    (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1) (hx : ‖x‖ ≤ lemma83RegularRadius) :
    (1/2)*(1-lemma83RegularRadius) ≤ ‖(1-u)*(1-v*x)‖ ∧
    (1/4)*(1-lemma83RegularRadius)^2 ≤ ‖(1-u)*(1-v*u)*(1-x)*(1-v*x)‖ ∧
    (1/4)*(1-lemma83RegularRadius) ≤ ‖(1-u)*(1-v*x)*(1-v*u)‖ := by
  have hR := sub_pos.mpr lemma83_regular_radius_lt_one
  have hvu : ‖v*u‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hu
  have hvx : ‖v*x‖ ≤ lemma83RegularRadius := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hx
  have hu' := lemma152_one_sub_norm_lower hu
  have hvu' := lemma152_one_sub_norm_lower hvu
  have hx' := lemma152_one_sub_norm_lower hx
  have hvx' := lemma152_one_sub_norm_lower hvx
  constructor
  · rw [norm_mul]
    exact mul_le_mul (by linarith [hu']) hvx' hR.le (norm_nonneg _)
  constructor
  · simp only [norm_mul]
    calc
      _ = (1/2)*(1/2)*(1-lemma83RegularRadius)*(1-lemma83RegularRadius) := by ring
      _ ≤ _ := by gcongr <;> linarith
  · simp only [norm_mul]
    calc
      _ = (1/2)*(1-lemma83RegularRadius)*(1/2) := by ring
      _ ≤ _ := by gcongr <;> linarith

lemma lemma152_shift_variation_bound (a b u v x : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1)
    (hx : ‖x‖ ≤ lemma83RegularRadius) :
    ‖lemma152LocalCorrection a b u v x-lemma152LocalCorrection 1 1 u v x‖ ≤
      lemma152CorrectionConstant*‖u‖*‖x‖*(‖a-1‖+‖b-1‖) := by
  have hR := sub_pos.mpr lemma83_regular_radius_lt_one
  obtain ⟨hd1,hd2,hd3⟩ := lemma152_denominator_bounds u v x hu hv hx
  have hE : 0 ≤ ‖a-1‖+‖b-1‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have ha' : ‖a-1‖ ≤ 2 := by have := norm_sub_le a (1:ℂ); simp only [norm_one] at this; linarith
  have hb' : ‖b-1‖ ≤ 2 := by have := norm_sub_le b (1:ℂ); simp only [norm_one] at this; linarith
  have hx1 : ‖x‖ ≤ 1 := hx.trans lemma83_regular_radius_lt_one.le
  have hux : ‖1-u*x‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul]
    nlinarith [norm_nonneg u,norm_nonneg x]
  have hv2 : ‖v^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg v]
  have hn1 : ‖u*x*v^2*((a-1)+(b-1))‖ ≤ 4*‖u‖*‖x‖*(‖a-1‖+‖b-1‖) := by
    rw [norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖u‖*‖x‖*1*(‖a-1‖+‖b-1‖) := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg x)) hE]
  have hab : ‖a-1‖*‖b-1‖ ≤ 4*(‖a-1‖+‖b-1‖) := by
    nlinarith [norm_nonneg (a-1),norm_nonneg (b-1)]
  have hn2 : ‖v*u*x*(a-1)*(b-1)*(1-u*x)‖ ≤
      8*‖u‖*‖x‖*(‖a-1‖+‖b-1‖) := by
    simp only [norm_mul]
    calc
      _ = ‖v‖*‖u‖*‖x‖*(‖a-1‖*‖b-1‖)*‖1-u*x‖ := by ring
      _ ≤ 1*‖u‖*‖x‖*(4*(‖a-1‖+‖b-1‖))*2 := by gcongr
      _ = _ := by ring
  rw [lemma152_local_correction_shift_difference]
  apply (norm_sub_le _ _).trans
  rw [norm_div,norm_div]
  apply (add_le_add (div_le_div₀ (by positivity) hn1 (by positivity) hd1)
    (div_le_div₀ (by positivity) hn2 (by positivity) hd2)).trans
  apply le_of_eq
  unfold lemma152CorrectionConstant
  field_simp
  ring

lemma lemma152_variable_variation_bound (u v x : ℂ)
    (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1) (hx : ‖x‖ ≤ lemma83RegularRadius) :
    ‖lemma152LocalCorrection 1 1 u v x-lemma152LocalCorrection 1 1 u v u‖ ≤
      lemma152CorrectionConstant*‖u‖*‖x-u‖ := by
  have hR := sub_pos.mpr lemma83_regular_radius_lt_one
  obtain ⟨hd1,hd2,hd3⟩ := lemma152_denominator_bounds u v x hu hv hx
  have hu0 : 1-u ≠ 0 := lemma83_one_sub_ne_zero (by linarith)
  have hvu : 1-v*u ≠ 0 := lemma83_one_sub_ne_zero (by
    rw [norm_mul]
    have h := mul_le_of_le_one_left (norm_nonneg u) hv
    linarith)
  have hvx : 1-v*x ≠ 0 := lemma83_one_sub_ne_zero (by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg x) hv).trans_lt (hx.trans_lt lemma83_regular_radius_lt_one))
  have hv2 : ‖v^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg v]
  have hcoef : ‖v^2-v‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [lemma152_local_correction_variable_difference u v x hu0 hvx hvu,norm_div]
  have hn : ‖u*(v^2-v)*(x-u)‖ ≤ 2*‖u‖*‖x-u‖ := by
    simp only [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hcoef (norm_nonneg u),norm_nonneg (x-u),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (norm_nonneg u)) (norm_nonneg (x-u))]
  apply (div_le_div₀ (by positivity) hn (by positivity) hd3).trans
  have heq : (2*‖u‖*‖x-u‖)/((1/4)*(1-lemma83RegularRadius)) =
      (8/(1-lemma83RegularRadius))*‖u‖*‖x-u‖ := by field_simp; ring
  rw [heq]
  gcongr
  unfold lemma152CorrectionConstant
  exact le_add_of_nonneg_right (by positivity)

end ZhangLS.Spec
