import ZhangLS.Spec.Proposition71PrincipalFiniteAnalytic
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

lemma proposition71_tau_order_mono_succ (k n : ℕ) :
    lemma34Tau k n≤lemma34Tau (k+1) n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  change (ArithmeticFunction.zeta^k) n ≤ (ArithmeticFunction.zeta^(k+1)) n
  rw [pow_succ,ArithmeticFunction.mul_zeta_apply]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn)

lemma proposition71_kappa_le_tau_five (β : Fin 3 → ℂ) (hβ : ∀ j, (β j).re=0) (n : ℕ) :
    ‖lemma83Kappa β n‖≤(lemma34Tau 5 n : ℝ) :=
  (proposition71_actual_kappa_le_tau_four β hβ n).trans
    (by exact_mod_cast proposition71_tau_order_mono_succ 4 n)

lemma proposition71_tau_five_local_hasSum {p : ℕ} (hp : p.Prime)
    {r : ℝ} (hr₀ : 0≤r) (hr : r<1) :
    HasSum (fun e : ℕ => (lemma34Tau 5 (p^e) : ℝ)*r^e) (1/(1-r)^5) := by
  have he (e : ℕ) : lemma34Tau 5 (p^e)=(e+4).choose 4 := by
    rw [lemma34_tau_prime_power hp 4,Nat.multichoose_eq,
      show 5+e-1=e+4 by omega,Nat.choose_symm_add]
  simpa only [he] using hasSum_choose_mul_geometric_of_norm_lt_one 4
    (show ‖r‖<1 by rwa [Real.norm_eq_abs,abs_of_nonneg hr₀])

lemma proposition71_modified_local_norm_bound (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) (d m : ℕ) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0<s.re) :
    ‖∑' e : ℕ, lemma83ModifiedLocal (lemma83Kappa β) d m s p e‖≤
      (lemma34Tau 5 (p^(d.factorization p)) : ℝ)/(1-‖(p : ℂ)^(-s)‖)^5 := by
  let r := ‖(p : ℂ)^(-s)‖
  have hr : r<1 := by
    dsimp [r]
    rw [←lemma32_prime_monomial_eq_cpow hp.pos]
    exact lemma32_prime_monomial_norm_lt_one hp.one_lt s hs
  have hg := (proposition71_tau_five_local_hasSum hp (norm_nonneg _) hr).mul_left
    (lemma34Tau 5 (p^(d.factorization p)) : ℝ)
  have hb (e : ℕ) : ‖lemma83ModifiedLocal (lemma83Kappa β) d m s p e‖≤
      (lemma34Tau 5 (p^(d.factorization p)) : ℝ)*((lemma34Tau 5 (p^e) : ℝ)*r^e) := by
    unfold lemma83ModifiedLocal
    split_ifs
    · simp only [norm_zero]; positivity
    · rw [norm_mul,norm_pow]
      have hk := proposition71_kappa_le_tau_five β hβ (p^(d.factorization p+e))
      have ht : (lemma34Tau 5 (p^(d.factorization p+e)) : ℝ)≤
          (lemma34Tau 5 (p^(d.factorization p)) : ℝ)*(lemma34Tau 5 (p^e) : ℝ) := by
        rw [pow_add]
        exact_mod_cast proposition71_tau_submultiplicative 5 (p^(d.factorization p)) (p^e)
      exact (mul_le_mul_of_nonneg_right (hk.trans ht) (pow_nonneg (norm_nonneg _) e)).trans_eq (by dsimp [r]; ring)
  have hh := (lemma83_modified_local_kappa_summable β hβ d m s hs hp).of_norm.hasSum.norm_le_of_bounded hg hb
  simpa only [mul_one_div] using hh

/-- A finite Euler envelope with every supporting prime retained. -/
noncomputable def proposition71KappaEulerEnvelope (d : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ d.primeFactors, 1/(1-(p : ℝ)^(-σ))^5

/-- The source τ₅(d) dilation factor is explicit; this bound is valid at every
height throughout the full half-plane Re(s)>0. -/
theorem proposition71_modified_kappa_norm_euler_bound (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ)
    {s : ℂ} (hs : 0<s.re) :
    ‖lemma83ModifiedKappa β d m s‖≤
      (lemma34Tau 5 d : ℝ)*proposition71KappaEulerEnvelope d s.re := by
  rw [lemma83ModifiedKappa,(lemma83_modified_kappa_hasSum β hβ d m hd s hs).tsum_eq,norm_prod]
  have ht : (lemma34Tau 5 d : ℝ)=∏p∈d.primeFactors, (lemma34Tau 5 (p^(d.factorization p)) : ℝ) := by
    have hh := (lemma34_tau_multiplicative 5).multiplicative_factorization (ArithmeticFunction.zeta^5) hd
    rw [Nat.prod_factorization_eq_prod_primeFactors] at hh
    exact_mod_cast hh
  rw [ht,proposition71KappaEulerEnvelope,←prod_mul_distrib]
  apply prod_le_prod (fun p _ => norm_nonneg _)
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hn : ‖(p : ℂ)^(-s)‖=(p : ℝ)^(-s.re) := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp'.pos),neg_re]
  simpa only [hn,mul_one_div] using proposition71_modified_local_norm_bound β hβ d m hp' hs

/-- The exact shape of the finite λ-envelope, without suppressing its modulus. -/
noncomputable def proposition71LambdaEulerEnvelope (m : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ m.primeFactors, (1+(p : ℝ)^(-σ))^3/(1-(p : ℝ)^(-σ))

lemma proposition71_lambda_factor_norm_bound (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0<s.re) :
    ‖lemma83LambdaFactor β p s‖≤(1+(p : ℝ)^(-s.re))^3/(1-(p : ℝ)^(-s.re)) := by
  let r := (p : ℝ)^(-s.re)
  have hr₀ : 0≤r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hn : ‖(p : ℂ)^(-s)‖=r := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos),neg_re]
  have hr : r<1 := by
    rw [←hn,←lemma32_prime_monomial_eq_cpow hp.pos]
    exact lemma32_prime_monomial_norm_lt_one hp.one_lt s hs
  have hnorm (j : Fin 3) : ‖(p : ℂ)^(-s-β j)‖=r := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos)]
    simp only [sub_re,neg_re,hβ j,sub_zero]
    rfl
  have hnum (j : Fin 3) : ‖1-(p : ℂ)^(-s-β j)‖≤1+r := by
    simpa only [norm_one,hnorm j] using norm_sub_le (1 : ℂ) ((p : ℂ)^(-s-β j))
  have hden : 1-r≤‖1-(p : ℂ)^(-s)‖ := by
    simpa only [norm_one,hn] using norm_sub_norm_le (1 : ℂ) ((p : ℂ)^(-s))
  unfold lemma83LambdaFactor
  rw [norm_div,norm_mul,norm_mul]
  apply (div_le_div₀ (by positivity) (show
    ‖1-(p : ℂ)^(-s-β 0)‖*‖1-(p : ℂ)^(-s-β 1)‖*‖1-(p : ℂ)^(-s-β 2)‖≤(1+r)^3 from by
      calc
        _≤(1+r)*(1+r)*(1+r) := by gcongr; exacts [hnum 0,hnum 1,hnum 2]
        _=_ := by ring) (sub_pos.mpr hr) hden)

theorem proposition71_lambda_norm_euler_bound (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) (m : ℕ) {s : ℂ} (hs : 0<s.re) :
    ‖lemma83Lambda β m s‖≤proposition71LambdaEulerEnvelope m s.re := by
  rw [lemma83Lambda,norm_prod,proposition71LambdaEulerEnvelope]
  exact prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp =>
    proposition71_lambda_factor_norm_bound β hβ (Nat.prime_of_mem_primeFactors hp) hs)

/-- A proved pointwise envelope for the actual source integrand, valid at all
heights and retaining q, τ₅(d), both finite-prime envelopes, every zeta factor,
and the actual Mellin transform. It is a prerequisite, not the desired mean bound. -/
theorem proposition71_principal_integrand_norm_euler_bound (D : ℕ) (β : Fin 3 → ℂ)
    (hβ : ∀ j, (β j).re=0) {d : ℕ} (hd : d≠0) (m : ℕ)
    {q : ℝ} (hq : 0<q) {s : ℂ} (hs : 0<s.re) :
    ‖proposition71PrincipalMellinIntegrand D β d m q s‖≤
      (lemma34Tau 5 d : ℝ)*proposition71KappaEulerEnvelope d s.re*
        proposition71LambdaEulerEnvelope (d*m) s.re*
        ‖riemannZeta (s+β 0)*riemannZeta (s+β 1)*riemannZeta (s+β 2)/riemannZeta s‖*
        q^s.re*‖lemma54PaperDeltaMellin D s‖ := by
  unfold proposition71PrincipalMellinIntegrand
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hq]
  gcongr
  · exact (norm_nonneg _).trans (proposition71_modified_kappa_norm_euler_bound β hβ hd m hs)
  · exact proposition71_modified_kappa_norm_euler_bound β hβ hd m hs
  · exact proposition71_lambda_norm_euler_bound β hβ (d*m) hs

end ZhangLS.Spec
