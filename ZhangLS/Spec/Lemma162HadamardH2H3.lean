import ZhangLS.Spec.Lemma153WeightedKernel
import ZhangLS.Spec.Lemma83ShiftedTail

/-! Exact H₂ × H₃ Hadamard identity, including coincident shifts. The
six Euler denominators and cubic numerator are derived from convergent series.
This is a generic local tool, not an assumed global Euler identity. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma162_weighted_convolution_hasSum (f g : ℕ → ℂ) (x F FW G GW : ℂ)
    (hf : HasSum (fun n : ℕ => f n*x^n) F)
    (hwf : HasSum (fun n : ℕ => ((n:ℂ)+1)*f n*x^n) FW)
    (hg : HasSum (fun n : ℕ => g n*x^n) G)
    (hwg : HasSum (fun n : ℕ => ((n:ℂ)+1)*g n*x^n) GW) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*lemma83AddConvolution f g n*x^n)
      (FW*G+F*GW-F*G) := by
  have h1 := lemma83_add_convolution_power_series_hasSum hwf hg
  have h2 := lemma83_add_convolution_power_series_hasSum hf hwg
  have h3 := lemma83_add_convolution_power_series_hasSum hf hg
  convert (h1.add h2).sub h3 using 1
  funext n
  simp only [lemma83AddConvolution,mul_sum,sum_mul,← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro ij hij
  have hn : (n:ℂ) = (ij.1:ℂ)+(ij.2:ℂ) := by
    exact_mod_cast (mem_antidiagonal.mp hij).symm
  rw [hn]
  ring

lemma lemma162_weighted_h3_hasSum (a b c x : ℂ)
    (ha : ‖a*x‖ < 1) (hb : ‖b*x‖ < 1) (hc : ‖c*x‖ < 1) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*lemma83LocalH3 a b c n*x^n)
      ((1-(a*b+a*c+b*c)*x^2+2*a*b*c*x^3)/
        ((1-a*x)^2*(1-b*x)^2*(1-c*x)^2)) := by
  have hf := lemma83_local_h2_hasSum a b x ha hb
  have hwf := lemma153_weighted_h2_hasSum a b x ha hb
  have hg : HasSum (fun n : ℕ => c^n*x^n) (1-c*x)⁻¹ := by
    simpa only [mul_pow] using hasSum_geometric_of_norm_lt_one hc
  have hwg : HasSum (fun n : ℕ => ((n:ℂ)+1)*c^n*x^n) (1/(1-c*x)^2) := by
    simpa only [mul_pow,mul_assoc] using lemma153_weighted_geometric_hasSum (c*x) hc
  have hh := lemma162_weighted_convolution_hasSum (lemma83LocalH2 a b) (fun n : ℕ => c^n)
    x _ _ _ _ hf hwf hg hwg
  convert hh using 1
  have han := lemma83_one_sub_ne_zero ha
  have hbn := lemma83_one_sub_ne_zero hb
  have hcn := lemma83_one_sub_ne_zero hc
  field_simp
  ring

lemma lemma162_h2_diagonal (a : ℂ) (n : ℕ) :
    lemma83LocalH2 a a n = ((n:ℂ)+1)*a^n := by
  unfold lemma83LocalH2 lemma83AddConvolution
  have he : (∑ ij ∈ antidiagonal n, a^ij.1*a^ij.2) =
      ∑ _ij ∈ antidiagonal n, a^n := by
    apply sum_congr rfl
    intro ij hij
    rw [← pow_add,mem_antidiagonal.mp hij]
  rw [he]
  simp


lemma lemma162_hadamard_fraction_identity (a b P Q S : ℂ)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hab : a-b ≠ 0)
    (hS : (a-b)*S = a*Q-b*P) :
    S/(P*Q) = (a*(1/P)-b*(1/Q))/(a-b) := by
  field_simp
  linear_combination hS

/-- The classical 2-by-3 local identity. Equality of a and b is treated
by the independently proved weighted-H₃ formula, never totalized division. -/
lemma lemma162_h2_h3_hadamard_hasSum (a b c d e z : ℂ)
    (hca : ‖c*(a*z)‖ < 1) (hda : ‖d*(a*z)‖ < 1) (hea : ‖e*(a*z)‖ < 1)
    (hcb : ‖c*(b*z)‖ < 1) (hdb : ‖d*(b*z)‖ < 1) (heb : ‖e*(b*z)‖ < 1) :
    HasSum (fun n : ℕ => lemma83LocalH2 a b n*lemma83LocalH3 c d e n*z^n)
      ((1-a*b*(c*d+c*e+d*e)*z^2+a*b*(a+b)*c*d*e*z^3)/
        ((1-c*(a*z))*(1-d*(a*z))*(1-e*(a*z))*
          ((1-c*(b*z))*(1-d*(b*z))*(1-e*(b*z))))) := by
  have hcan := lemma83_one_sub_ne_zero hca
  have hdan := lemma83_one_sub_ne_zero hda
  have hean := lemma83_one_sub_ne_zero hea
  have hcbn := lemma83_one_sub_ne_zero hcb
  have hdbn := lemma83_one_sub_ne_zero hdb
  have hebn := lemma83_one_sub_ne_zero heb
  by_cases hab : a = b
  · subst b
    have hh := lemma162_weighted_h3_hasSum c d e (a*z) hca hda hea
    convert hh using 1
    · funext n
      rw [lemma162_h2_diagonal,mul_pow]
      ring
    · field_simp
      ring
  · have ha := lemma83_local_h3_hasSum c d e (a*z) hca hda hea
    have hb := lemma83_local_h3_hasSum c d e (b*z) hcb hdb heb
    have hn : a-b ≠ 0 := sub_ne_zero.mpr hab
    convert ((ha.mul_left a).sub (hb.mul_left b)).div_const (a-b) using 1
    · funext n
      rw [lemma83LocalH2,lemma83AddConvolution,lemma83_antidiagonal_geometric a b hab]
      simp only [mul_pow,pow_succ]
      ring
    · let P := (1-c*(a*z))*(1-d*(a*z))*(1-e*(a*z))
      let Q := (1-c*(b*z))*(1-d*(b*z))*(1-e*(b*z))
      have hP : P ≠ 0 := mul_ne_zero (mul_ne_zero hcan hdan) hean
      have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hcbn hdbn) hebn
      have heP : (1-c*(a*z))⁻¹*(1-d*(a*z))⁻¹*(1-e*(a*z))⁻¹ = 1/P := by
        simp [P,div_eq_mul_inv,mul_inv_rev,mul_comm,mul_assoc]
      have heQ : (1-c*(b*z))⁻¹*(1-d*(b*z))⁻¹*(1-e*(b*z))⁻¹ = 1/Q := by
        simp [Q,div_eq_mul_inv,mul_inv_rev,mul_comm,mul_assoc]
      rw [heP,heQ]
      apply lemma162_hadamard_fraction_identity a b P Q _ hP hQ hn
      dsimp [P,Q]
      ring

end ZhangLS.Spec
