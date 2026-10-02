import ZhangLS.Spec.Lemma32PrimeCoefficients
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_rising_choose_two (e : ℕ) :
    2*((e+2).choose 2 : ℂ) = (e+1 : ℂ)*(e+2 : ℂ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (e+2) 2
  simp [Nat.descFactorial_succ,show e+2-1=e+1 by omega] at h
  norm_num [Nat.factorial] at h
  norm_cast
  nlinarith [h]

lemma lemma32_rising_choose_three (e : ℕ) :
    6*((e+3).choose 3 : ℂ) = (e+1 : ℂ)*(e+2 : ℂ)*(e+3 : ℂ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (e+3) 3
  simp [Nat.descFactorial_succ,show e+3-2=e+1 by omega,show e+3-1=e+2 by omega] at h
  norm_num [Nat.factorial] at h
  norm_cast
  nlinarith [h]

lemma lemma32_rising_choose_four (e : ℕ) :
    24*((e+4).choose 4 : ℂ) = (e+1 : ℂ)*(e+2 : ℂ)*(e+3 : ℂ)*(e+4 : ℂ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (e+4) 4
  simp [Nat.descFactorial_succ,show e+4-3=e+1 by omega,show e+4-2=e+2 by omega,
    show e+4-1=e+3 by omega] at h
  norm_num [Nat.factorial] at h
  norm_cast
  nlinarith [h]

lemma lemma32_fourth_power_choose (e : ℕ) :
    (e+1 : ℂ)^4 = 24*((e+4).choose 4 : ℂ)-36*((e+3).choose 3 : ℂ)+
      14*((e+2).choose 2 : ℂ)-((e+1).choose 1 : ℂ) := by
  have h2 := lemma32_rising_choose_two e
  have h3 := lemma32_rising_choose_three e
  have h4 := lemma32_rising_choose_four e
  simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one]
  linear_combination -h4 + 6*h3 - 7*h2

lemma lemma32_fourth_geometric_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun e : ℕ => (e+1 : ℂ)^4*z^e)
      ((1+11*z+11*z^2+z^3)/(1-z)^5) := by
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hz
  have h2 := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hz).mul_left (14 : ℂ)
  have h3 := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hz).mul_left (36 : ℂ)
  have h4 := (hasSum_choose_mul_geometric_of_norm_lt_one 4 hz).mul_left (24 : ℂ)
  have hh := ((h4.sub h3).add h2).sub h1
  have hn : 1-z ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h] at hz; norm_num at hz)
  convert hh using 1
  · funext e
    rw [lemma32_fourth_power_choose]
    ring
  · field_simp
    ring

end ZhangLS.Spec
