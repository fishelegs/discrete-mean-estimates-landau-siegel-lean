import ZhangLS.Spec.Proposition26ProfileBV
import ZhangLS.Spec.Lemma83
import ZhangLS.Spec.Lemma83FiniteShiftLambda
import ZhangLS.Spec.Lemma81ActualPolynomialMoments

/-! Finite-shift Euler exponents and frequency budgets for the original
parameters. The logarithms are not absorbed into a prime-mass surrogate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical Topology

lemma proposition26_alpha_log_identity {D : ℕ} (hL : 0<lemma23PaperL D) :
    lemma44PaperAlpha D*lemma23PaperL D^9=Real.pi := by
  rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hL.ne')

lemma proposition26_small_shift_log_budget {D : ℕ} (hL : 1≤lemma23PaperL D)
    {x : ℝ} (_hx : 0<x) (hlog : Real.log x≤2*lemma23PaperL D^9) :
    (3*lemma44PaperAlpha D)*(2+Real.log x)≤12*Real.pi := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hα : 0<lemma44PaperAlpha D := by
    rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    positivity
  have ha := proposition26_alpha_log_identity hLp
  have hpow : 1≤lemma23PaperL D^9 := one_le_pow₀ hL
  have hap : lemma44PaperAlpha D≤Real.pi := by
    nlinarith only [mul_le_mul_of_nonneg_left hpow hα.le,ha]
  have hb := mul_le_mul_of_nonneg_left hlog hα.le
  nlinarith only [hb,ha,hap]

noncomputable def proposition26LambdaConstant : ℝ :=
  Real.exp (384*Real.pi*Real.log 4)

lemma proposition26_lambda_constant_pos : 0<proposition26LambdaConstant := Real.exp_pos _

/-- The finite Λ bound becomes an absolute constant on the actual d,r box,
with the same original shifts c and no assumption on χ. -/
theorem proposition26_actual_lambda_uniform {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {d r : ℕ}
    (hd : d∈lemma81PolynomialIndices D) (hr : r∈lemma81PolynomialIndices D) :
    ‖lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)‖≤
      proposition26LambdaConstant := by
  have hd' := (proposition71_mem_indices D d).mp hd
  have hr' := (proposition71_mem_indices D r).mp hr
  have hdp : (0:ℝ)<d := by exact_mod_cast hd'.1
  have hrp : (0:ℝ)<r := by exact_mod_cast hr'.1
  have hdP := hd'.2.le.trans (lemma81_cutoff_le_P hL)
  have hrP := hr'.2.le.trans (lemma81_cutoff_le_P hL)
  have hdl : Real.log (d:ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using Real.log_le_log hdp hdP
  have hrl : Real.log (r:ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using Real.log_le_log hrp hrP
  have hlog : Real.log ((d*r:ℕ):ℝ)≤2*lemma23PaperL D^9 := by
    rw [Nat.cast_mul,Real.log_mul hdp.ne' hrp.ne']
    linarith
  have hα := (lemma44_alpha_pos_le_one hL).1
  have hb := lemma83_lambda_finite_shift_bound (lemma83PaperBeta D c)
    (lemma83_beta_re D c) (3*lemma44PaperAlpha D) (by positivity)
    (lemma83_paper_beta_norm hL hc hsmall) j (d*r) (Nat.mul_pos hd'.1 hr'.1)
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hh := proposition26_small_shift_log_budget (by linarith : 1≤lemma23PaperL D)
    (show 0<((d*r:ℕ):ℝ) by exact_mod_cast Nat.mul_pos hd'.1 hr'.1) hlog
  have hlog4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0:ℝ)≤32) hlog4)
  nlinarith only [hm]

lemma proposition26_frequency_point_budget {D : ℕ} {c v : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hfreq : lemma23PaperL D^20+4≤(D:ℝ)) (hv : |v|≤lemma23PaperL D^20)
    (j : Fin 3) :
    ‖1-lemma83PaperBeta D c j+I*(v:ℂ)‖≤(D:ℝ) ∧
      ‖1+I*((-v:ℝ):ℂ)‖≤(D:ℝ) := by
  have hβ := lemma83_paper_beta_norm hL hc hsmall j
  have hα := (lemma44_alpha_pos_le_one hL).2
  have hI : ‖I*(v:ℂ)‖=|v| := by simp only [norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  constructor
  · have ht := norm_add_le (1-lemma83PaperBeta D c j) (I*(v:ℂ))
    have ht' := norm_sub_le (1:ℂ) (lemma83PaperBeta D c j)
    rw [norm_one] at ht'
    rw [hI] at ht
    linarith only [ht,ht',hβ,hα,hfreq,hv]
  · have ht := norm_add_le (1:ℂ) (I*((-v:ℝ):ℂ))
    simp only [norm_one,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_neg] at ht
    linarith only [ht,hv,hfreq]

/-- An explicit exponential-series inequality supplies the needed conductor
height, rather than postulating uniformity over logarithmically growing v. -/
lemma proposition26_frequency_size {D : ℕ} (hD : 0<D)
    (hL : 2*(Nat.factorial 21:ℝ)+4≤lemma23PaperL D) :
    lemma23PaperL D^20+4≤(D:ℝ) := by
  have hF : 0<(Nat.factorial 21:ℝ) := by positivity
  have hLp : 0<lemma23PaperL D := by linarith
  have he := Real.pow_div_factorial_le_exp (lemma23PaperL D) hLp.le 21
  rw [lemma23PaperL,Real.exp_log (by exact_mod_cast hD)] at he
  change lemma23PaperL D^21/(Nat.factorial 21:ℝ)≤(D:ℝ) at he
  have hmul := mul_le_mul_of_nonneg_right (show 2*(Nat.factorial 21:ℝ)≤lemma23PaperL D by linarith)
    (pow_nonneg hLp.le 20)
  have ht : 2*lemma23PaperL D^20≤lemma23PaperL D^21/(Nat.factorial 21:ℝ) := by
    apply (le_div_iff₀ hF).mpr
    nlinarith only [hmul]
  have hpow : 4≤lemma23PaperL D^20 := by
    have hL4 : 4≤lemma23PaperL D := by linarith
    exact hL4.trans (le_self_pow₀ (by linarith : 1≤lemma23PaperL D) (by norm_num : 20≠0))
  linarith only [he,ht,hpow]

end ZhangLS.Spec
