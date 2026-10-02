import ZhangLS.Spec.Lemma152EulerProduct
import ZhangLS.Spec.Lemma152CorrectionVariation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma152_log_exp_bound {p : ℕ} (hp : 0 < p) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1/10) :
    Real.log (p:ℝ)*Real.exp (r*Real.log (p:ℝ)) ≤ 10*(p:ℝ)^(1/5:ℝ) := by
  have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
  have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hlog : Real.log (p:ℝ) ≤ 10*(p:ℝ)^(1/10:ℝ) := by
    have hh := Real.log_le_rpow_div hp0.le (by norm_num : (0:ℝ)<1/10)
    convert hh using 1 <;> ring
  have he : Real.exp (r*Real.log (p:ℝ)) ≤ (p:ℝ)^(1/10:ℝ) := by
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (10*(p:ℝ)^(1/10:ℝ))*(p:ℝ)^(1/10:ℝ) :=
      mul_le_mul hlog he (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hp0]
      norm_num

lemma lemma152_shift_monomial_variation {p : ℕ} (hp : 0 < p) (z : ℂ)
    (hz : ‖z‖ ≤ 1/10) :
    ‖lemma32PrimeMonomial p z-1‖ ≤ 10*‖z‖*(p:ℝ)^(1/5:ℝ) := by
  have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hn : ‖-(z*(Real.log p:ℂ))‖ = ‖z‖*Real.log p := by
    rw [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
  have he := lemma83_exp_sub_one_bound (-(z*(Real.log p:ℂ)))
  rw [hn] at he
  have he' : ‖lemma32PrimeMonomial p z-1‖ ≤ ‖z‖*Real.log p*Real.exp (‖z‖*Real.log p) := by
    simpa only [lemma32PrimeMonomial,neg_mul] using he
  apply he'.trans
  have hb := lemma152_log_exp_bound hp (norm_nonneg z) hz
  nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg z)]

lemma lemma152_center_monomial_variation {p : ℕ} (hp : 0 < p) (s : ℂ)
    (hs : ‖s-1‖ ≤ 1/10) :
    ‖lemma32PrimeMonomial p s-(p:ℂ)⁻¹‖ ≤ 10*‖s-1‖*(p:ℝ)^(-(4/5:ℝ)) := by
  have he := lemma83_monomial_near_one hp (s-1)
  rw [add_sub_cancel] at he
  have hh := lemma152_log_exp_bound hp (norm_nonneg (s-1)) hs
  calc
    _ ≤ (p:ℝ)⁻¹*(‖s-1‖*Real.log p)*Real.exp (‖s-1‖*Real.log p) := he
    _ ≤ (p:ℝ)⁻¹*‖s-1‖*(10*(p:ℝ)^(1/5:ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (by positivity : 0≤(p:ℝ)⁻¹) (norm_nonneg (s-1)))]
    _ = _ := by
      rw [← Real.rpow_neg_one]
      calc
        _ = (10*‖s-1‖)*((p:ℝ)^(-1:ℝ)*(p:ℝ)^(1/5:ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add (Nat.cast_pos.mpr hp)]; norm_num

end ZhangLS.Spec
