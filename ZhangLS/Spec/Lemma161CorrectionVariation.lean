import ZhangLS.Spec.Lemma161EulerProduct
import ZhangLS.Spec.Lemma152CorrectionVariation

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma161_local_zero_shift (u v x : ℂ) :
    lemma152LocalCorrection 1 0 u v x = 1-v*u*x/((1-u)*(1-v*x)) := by
  unfold lemma152LocalCorrection
  simp only [add_zero,sub_self,mul_zero,zero_div,sub_zero,zero_sub]
  ring

lemma lemma161_local_shift_difference (a u v x : ℂ) :
    lemma152LocalCorrection a 0 u v x-lemma152LocalCorrection 1 0 u v x =
      u*x*v^2*(a-1)/((1-u)*(1-v*x)) +
        v*u*x*(a-1)*(1-u*x)/((1-u)*(1-v*u)*(1-x)*(1-v*x)) := by
  unfold lemma152LocalCorrection
  simp only [add_zero,sub_self,mul_zero,zero_div,sub_zero,zero_sub]
  ring

lemma lemma161_local_variable_difference (u v x : ℂ)
    (hu : 1-u ≠ 0) (hvx : 1-v*x ≠ 0) (hvu : 1-v*u ≠ 0) :
    lemma152LocalCorrection 1 0 u v x-lemma152LocalCorrection 1 0 u v u =
      -v*u*(x-u)/((1-u)*(1-v*x)*(1-v*u)) := by
  rw [lemma161_local_zero_shift,lemma161_local_zero_shift]
  have hxv : 1-x*v ≠ 0 := by simpa [mul_comm] using hvx
  have huv : 1-u*v ≠ 0 := by simpa [mul_comm] using hvu
  field_simp [hu,hvx,hvu,hxv,huv]
  all_goals ring

lemma lemma161_shift_variation_bound (a u v x : ℂ)
    (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1) (hx : ‖x‖ ≤ lemma83RegularRadius) :
    ‖lemma152LocalCorrection a 0 u v x-lemma152LocalCorrection 1 0 u v x‖ ≤
      lemma152CorrectionConstant*‖u‖*‖x‖*‖a-1‖ := by
  have hR := sub_pos.mpr lemma83_regular_radius_lt_one
  obtain ⟨hd1,hd2,hd3⟩ := lemma152_denominator_bounds u v x hu hv hx
  have hx1 : ‖x‖ ≤ 1 := hx.trans lemma83_regular_radius_lt_one.le
  have hux : ‖1-u*x‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul]
    nlinarith [norm_nonneg u,norm_nonneg x]
  have hv2 : ‖v^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg v]
  have hn1 : ‖u*x*v^2*(a-1)‖ ≤ 4*‖u‖*‖x‖*‖a-1‖ := by
    rw [norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖u‖*‖x‖*1*‖a-1‖ := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg x)) (norm_nonneg (a-1))]
  have hn2 : ‖v*u*x*(a-1)*(1-u*x)‖ ≤ 8*‖u‖*‖x‖*‖a-1‖ := by
    simp only [norm_mul]
    calc
      _ ≤ 1*‖u‖*‖x‖*‖a-1‖*2 := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg x)) (norm_nonneg (a-1))]
  rw [lemma161_local_shift_difference]
  apply (norm_add_le _ _).trans
  rw [norm_div,norm_div]
  apply (add_le_add (div_le_div₀ (by positivity) hn1 (by positivity) hd1)
    (div_le_div₀ (by positivity) hn2 (by positivity) hd2)).trans
  apply le_of_eq
  unfold lemma152CorrectionConstant
  field_simp
  ring

lemma lemma161_variable_variation_bound (u v x : ℂ)
    (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1) (hx : ‖x‖ ≤ lemma83RegularRadius) :
    ‖lemma152LocalCorrection 1 0 u v x-lemma152LocalCorrection 1 0 u v u‖ ≤
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
  rw [lemma161_local_variable_difference u v x hu0 hvx hvu,norm_div]
  have hn : ‖-v*u*(x-u)‖ ≤ 2*‖u‖*‖x-u‖ := by
    simp only [norm_mul,norm_neg]
    calc
      _ ≤ 1*‖u‖*‖x-u‖ := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg (x-u))]
  apply (div_le_div₀ (by positivity) hn (by positivity) hd3).trans
  have heq : (2*‖u‖*‖x-u‖)/((1/4)*(1-lemma83RegularRadius)) =
      (8/(1-lemma83RegularRadius))*‖u‖*‖x-u‖ := by field_simp; ring
  rw [heq]
  gcongr
  unfold lemma152CorrectionConstant
  exact le_add_of_nonneg_right (by positivity)

end ZhangLS.Spec
