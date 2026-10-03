import ZhangLS.Spec.Proposition71PrincipalEulerBounds
import ZhangLS.Spec.Lemma34TauProduct

/-! Fixed-order divisor majorants for every actual finite-prime envelope.
The d and d*m dependence is retained until the genuine outer harmonic sums. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 3000000

lemma proposition71_multichoose_degree_mono {k : ℕ} (hk : 0<k) :
    Monotone (Nat.multichoose k) := by
  apply monotone_nat_of_le_succ
  intro e
  have hr := lemma34_multichoose_recurrence k e hk
  have hm := Nat.mul_le_mul_right (Nat.multichoose k e) (show e+1≤e+k by omega)
  rw [←hr] at hm
  exact (mul_le_mul_iff_right₀ (by positivity : 0<e+1)).mp hm

/-- A constant factor for each distinct supporting prime is paid by the
actual tau order, including prime powers and n=1. -/
theorem proposition71_prime_factor_constant_le_tau {K n : ℕ} (hK : 0<K) (hn : n≠0) :
    (∏p∈n.primeFactors,(K : ℝ))≤(lemma34Tau K n : ℝ) := by
  have he : (lemma34Tau K n : ℝ)=∏p∈n.primeFactors,(lemma34Tau K (p^(n.factorization p)) : ℝ) := by
    have hh := (lemma34_tau_multiplicative K).multiplicative_factorization (ArithmeticFunction.zeta^K) hn
    rw [Nat.prod_factorization_eq_prod_primeFactors] at hh
    exact_mod_cast hh
  rw [he]
  apply prod_le_prod (fun _ _ => Nat.cast_nonneg _)
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hepos : 0<n.factorization p := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  have hτ := lemma34_tau_prime_power hprime (K-1) (n.factorization p)
  rw [Nat.sub_add_cancel hK] at hτ
  rw [hτ]
  have hm := proposition71_multichoose_degree_mono hK (show 1≤n.factorization p by omega)
  simpa only [Nat.multichoose_one_right] using (show (Nat.multichoose K 1 : ℝ)≤(Nat.multichoose K (n.factorization p) : ℝ) by exact_mod_cast hm)

lemma proposition71_prime_inverse_rpow_le_three_quarters {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1/2≤σ) : (p : ℝ)^(-σ)≤3/4 := by
  have hp1 : 1≤(p : ℝ) := by exact_mod_cast hp.one_le
  have hp2 : 2≤(p : ℝ) := by exact_mod_cast hp.two_le
  have h1 := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ≤-(1/2 : ℝ) by linarith)
  have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ)<2) hp2 (by norm_num : -(1/2 : ℝ)≤0)
  have hs : ((2 : ℝ)^(-(1/2 : ℝ)))^2=1/2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
    norm_num
  have hsmall : (2 : ℝ)^(-(1/2 : ℝ))≤3/4 := by
    have hn := Real.rpow_nonneg (by norm_num : (0 : ℝ)≤2) (-(1/2 : ℝ))
    nlinarith
  exact h1.trans (h2.trans hsmall)

lemma proposition71_kappa_envelope_factor_le {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1/2≤σ) : 1/(1-(p : ℝ)^(-σ))^5≤1024 := by
  have hx := proposition71_prime_inverse_rpow_le_three_quarters hp hσ
  have hd : (1/4 : ℝ)≤1-(p : ℝ)^(-σ) := by linarith
  have hp5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/4) hd 5
  have hden : 0<(1-(p : ℝ)^(-σ))^5 := by positivity
  apply (div_le_iff₀ hden).mpr
  norm_num at hp5
  linarith

lemma proposition71_lambda_envelope_factor_le {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1/2≤σ) : (1+(p : ℝ)^(-σ))^3/(1-(p : ℝ)^(-σ))≤32 := by
  have hx := proposition71_prime_inverse_rpow_le_three_quarters hp hσ
  have hx0 := Real.rpow_nonneg (Nat.cast_nonneg p) (-σ)
  have hd : (1/4 : ℝ)≤1-(p : ℝ)^(-σ) := by linarith
  have hnum := pow_le_pow_left₀ (show 0≤1+(p : ℝ)^(-σ) by linarith)
    (show 1+(p : ℝ)^(-σ)≤(7/4 : ℝ) by linarith) 3
  apply (div_le_iff₀ (show 0<1-(p : ℝ)^(-σ) by linarith)).mpr
  norm_num at hnum
  linarith

/-- The complete modified-kappa finite-prime envelope has a fixed tau1024
majorant, with no hidden dependence on d or the contour height. -/
theorem proposition71_kappa_euler_envelope_le_tau {d : ℕ} (hd : d≠0)
    {σ : ℝ} (hσ : 1/2≤σ) : proposition71KappaEulerEnvelope d σ≤(lemma34Tau 1024 d : ℝ) := by
  unfold proposition71KappaEulerEnvelope
  apply le_trans ?_ (proposition71_prime_factor_constant_le_tau (by norm_num : 0<(1024 : ℕ)) hd)
  apply prod_le_prod
  · intro p hp
    have hx := proposition71_prime_inverse_rpow_le_three_quarters (Nat.prime_of_mem_primeFactors hp) hσ
    have hden : 0<1-(p : ℝ)^(-σ) := by linarith
    positivity
  · exact fun p hp => proposition71_kappa_envelope_factor_le (Nat.prime_of_mem_primeFactors hp) hσ

/-- The complete lambda finite-prime envelope is paid by tau32 at its actual
modulus, including every prime common with the modified-kappa modulus. -/
theorem proposition71_lambda_euler_envelope_le_tau {m : ℕ} (hm : m≠0)
    {σ : ℝ} (hσ : 1/2≤σ) : proposition71LambdaEulerEnvelope m σ≤(lemma34Tau 32 m : ℝ) := by
  unfold proposition71LambdaEulerEnvelope
  apply le_trans ?_ (proposition71_prime_factor_constant_le_tau (by norm_num : 0<(32 : ℕ)) hm)
  apply prod_le_prod
  · intro p hp
    have hx := proposition71_prime_inverse_rpow_le_three_quarters (Nat.prime_of_mem_primeFactors hp) hσ
    have hden : 0<1-(p : ℝ)^(-σ) := by linarith
    positivity
  · exact fun p hp => proposition71_lambda_envelope_factor_le (Nat.prime_of_mem_primeFactors hp) hσ

lemma proposition71_kappa_half_strip_envelope_nonneg (d : ℕ) {σ : ℝ} (hσ : 1/2≤σ) :
    0≤proposition71KappaEulerEnvelope d σ := by
  unfold proposition71KappaEulerEnvelope
  apply prod_nonneg
  intro p hp
  have hx := proposition71_prime_inverse_rpow_le_three_quarters (Nat.prime_of_mem_primeFactors hp) hσ
  have hden : 0<1-(p : ℝ)^(-σ) := by linarith
  positivity

lemma proposition71_lambda_half_strip_envelope_nonneg (m : ℕ) {σ : ℝ} (hσ : 1/2≤σ) :
    0≤proposition71LambdaEulerEnvelope m σ := by
  unfold proposition71LambdaEulerEnvelope
  apply prod_nonneg
  intro p hp
  have hx := proposition71_prime_inverse_rpow_le_three_quarters (Nat.prime_of_mem_primeFactors hp) hσ
  have hden : 0<1-(p : ℝ)^(-σ) := by linarith
  positivity

end ZhangLS.Spec
