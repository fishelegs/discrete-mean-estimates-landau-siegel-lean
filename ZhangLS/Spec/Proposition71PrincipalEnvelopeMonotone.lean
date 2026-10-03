import ZhangLS.Spec.Proposition71PrincipalEulerBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_prime_negative_rpow_lt_one {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 0<σ) : (p : ℝ)^(-σ)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)

lemma proposition71_kappa_euler_envelope_nonneg (d : ℕ) {σ : ℝ} (hσ : 0<σ) :
    0≤proposition71KappaEulerEnvelope d σ := by
  unfold proposition71KappaEulerEnvelope
  apply prod_nonneg
  intro p hp
  have ht := proposition71_prime_negative_rpow_lt_one (Nat.prime_of_mem_primeFactors hp) hσ
  positivity

lemma proposition71_lambda_euler_envelope_nonneg (m : ℕ) {σ : ℝ} (hσ : 0<σ) :
    0≤proposition71LambdaEulerEnvelope m σ := by
  unfold proposition71LambdaEulerEnvelope
  apply prod_nonneg
  intro p hp
  have ht := proposition71_prime_negative_rpow_lt_one (Nat.prime_of_mem_primeFactors hp) hσ
  positivity

lemma proposition71_kappa_euler_envelope_antitone (d : ℕ) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    proposition71KappaEulerEnvelope d b≤proposition71KappaEulerEnvelope d a := by
  unfold proposition71KappaEulerEnvelope
  apply prod_le_prod
  · intro p hp
    have ht := proposition71_prime_negative_rpow_lt_one (Nat.prime_of_mem_primeFactors hp) (ha.trans_le hab)
    positivity
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hr : (p : ℝ)^(-b)≤(p : ℝ)^(-a) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp'.one_le) (neg_le_neg hab)
    have ht := proposition71_prime_negative_rpow_lt_one hp' ha
    apply one_div_le_one_div_of_le (pow_pos (sub_pos.mpr ht) 5)
    exact pow_le_pow_left₀ (sub_nonneg.mpr ht.le) (by linarith) 5

lemma proposition71_lambda_euler_envelope_antitone (m : ℕ) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    proposition71LambdaEulerEnvelope m b≤proposition71LambdaEulerEnvelope m a := by
  unfold proposition71LambdaEulerEnvelope
  apply prod_le_prod
  · intro p hp
    have ht := proposition71_prime_negative_rpow_lt_one (Nat.prime_of_mem_primeFactors hp) (ha.trans_le hab)
    positivity
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hr : (p : ℝ)^(-b)≤(p : ℝ)^(-a) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp'.one_le) (neg_le_neg hab)
    have ht := proposition71_prime_negative_rpow_lt_one hp' ha
    apply div_le_div₀ (by positivity) _ (sub_pos.mpr ht) (by linarith)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3

/-- A common left-edge arithmetic envelope controls all points to its right,
without removing τ₅(d) or either finite-prime loss. -/
theorem proposition71_principal_integrand_norm_uniform_euler (D : ℕ) (β : Fin 3 → ℂ)
    (hβ : ∀j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ)
    {q a : ℝ} (hq : 0<q) (ha : 0<a) {s : ℂ} (hs : a≤s.re) :
    ‖proposition71PrincipalMellinIntegrand D β d m q s‖≤
      (lemma34Tau 5 d : ℝ)*proposition71KappaEulerEnvelope d a*
        proposition71LambdaEulerEnvelope (d*m) a*
        ‖riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s‖*
        q^s.re*‖lemma54PaperDeltaMellin D s‖ := by
  apply (proposition71_principal_integrand_norm_euler_bound D β hβ hd m hq (ha.trans_le hs)).trans
  have hκ := proposition71_kappa_euler_envelope_antitone d ha hs
  have hlam := proposition71_lambda_euler_envelope_antitone (d*m) ha hs
  have hκ₀ := proposition71_kappa_euler_envelope_nonneg d ha
  have hlam0 := proposition71_lambda_euler_envelope_nonneg (d*m) (ha.trans_le hs)
  gcongr

end ZhangLS.Spec
