import ZhangLS.Spec.Lemma162RawPolynomialTail
import ZhangLS.Spec.Lemma162LocalExtraction

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma lemma162_half_denominator_bound {x : ℂ} (hx : ‖x‖≤1/2) : 1/2≤‖1-x‖ := by
  have h := norm_sub_norm_le (1:ℂ) x
  rw [norm_one] at h
  linarith

lemma lemma162_four_denominator_bounds (u v b : ℂ)
    (hu : ‖u‖≤1/2) (hv : ‖v‖≤1) (hb : ‖b‖≤1) :
    1/2≤‖1-u‖ ∧ 1/2≤‖1-v*u‖ ∧ 1/2≤‖1-u*b‖ ∧ 1/2≤‖1-v*u*b‖ := by
  have hvu : ‖v*u‖≤1/2 := by
    rw [norm_mul]
    calc
      ‖v‖*‖u‖ ≤ 1*(1/2:ℝ) := by gcongr
      _ = 1/2 := by norm_num
  have hub : ‖u*b‖≤1/2 := by
    rw [norm_mul]
    calc
      ‖u‖*‖b‖ ≤ (1/2:ℝ)*1 := by gcongr
      _ = 1/2 := by norm_num
  have hvub : ‖v*u*b‖≤1/2 := by
    rw [norm_mul]
    calc
      ‖v*u‖*‖b‖ ≤ (1/2:ℝ)*1 := by gcongr
      _ = 1/2 := by norm_num
  exact ⟨lemma162_half_denominator_bound hu,lemma162_half_denominator_bound hvu,
    lemma162_half_denominator_bound hub,lemma162_half_denominator_bound hvub⟩

lemma lemma162_first_remainder_bound (a u v b : ℂ)
    (ha : ‖a‖≤1) (hu : ‖u‖≤1/2) (hv : ‖v‖≤1) (hb : ‖b‖≤1) :
    ‖lemma162FirstRemainder a u v b‖≤80 := by
  obtain ⟨hdu,hdvu,hdub,hdvub⟩ := lemma162_four_denominator_bounds u v b hu hv hb
  have hden : (1/16:ℝ) ≤ ‖(1-u)*(1-v*u)*(1-u*b)*(1-v*u*b)‖ := by
    simp only [norm_mul]
    calc
      (1/16:ℝ) = (1/2)*(1/2)*(1/2)*(1/2) := by norm_num
      _ ≤ _ := by gcongr
  have hsmall : ‖a*u^2*b-a-v*u*b‖≤2 := by
    calc
      _ ≤ ‖a*u^2*b-a‖+‖v*u*b‖ := norm_sub_le _ _
      _ ≤ ‖a*u^2*b‖+‖a‖+‖v*u*b‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖a‖*‖u‖^2*‖b‖+‖a‖+‖v‖*‖u‖*‖b‖ := by simp only [norm_mul,norm_pow]
      _ ≤ 1*(1/2:ℝ)^2*1+1+1*(1/2)*1 := by gcongr
      _ ≤ 2 := by norm_num
  have hpoly : ‖a*u^2*b-a-v*u*b+v-u+1‖≤5 := by
    have ht := lemma162_norm_sum_four (a*u^2*b-a-v*u*b) v (-u) 1
    simp only [← sub_eq_add_neg,norm_neg,norm_one] at ht
    linarith
  have hnum : ‖v*b*(a*u^2*b-a-v*u*b+v-u+1)‖≤5 := by
    simp only [norm_mul]
    calc
      ‖v‖*‖b‖*‖a*u^2*b-a-v*u*b+v-u+1‖ ≤ 1*1*5 := by gcongr
      _ = 5 := by norm_num
  unfold lemma162FirstRemainder
  rw [norm_div]
  calc
    _ ≤ 5/(1/16:ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hden
    _ = 80 := by norm_num

lemma lemma162_norm_one_add_twice (v : ℂ) (hv : ‖v‖≤1) : ‖1+2*v‖≤3 := by
  have h := norm_add_le (1:ℂ) (2*v)
  rw [norm_one,norm_mul] at h
  norm_num at h
  linarith

end ZhangLS.Spec
