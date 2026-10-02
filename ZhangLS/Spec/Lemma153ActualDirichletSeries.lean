import ZhangLS.Spec.Lemma153ActualNorm
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma153_actual_term_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (s : ℂ) (h : m.Coprime n) :
    LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s (m*n) =
      LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s m *
        LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s n := by
  by_cases hm : m = 0
  · subst m; simp
  by_cases hn : n = 0
  · subst n; simp
  have hc := (lemma153_actual_coefficient_multiplicative χ β hpar.beta_re γ hpar.gamma_re hM).map_mul_of_coprime h
  change lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (m*n) =
    lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) m *
      lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) n at hc
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,hc,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  exact mul_div_mul_comm _ _ _ _

lemma lemma153_actual_prime_power_term {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hp : 0<p) (s : ℂ) (n : ℕ) :
    LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s (p^n) =
      lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (p^n)*lemma32PrimeMonomial p s^n := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero n hp.ne'),Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p n s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s]

/-- Absolute convergence of the original χτ₂varpi Dirichlet series on Re s>1. -/
lemma lemma153_actual_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    LSeriesSummable (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s := by
  apply summable_norm_iff.mp
  apply EulerProduct.summable_norm_of_prime_power_tsum_le
    (LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s) (by simp)
    (by simp [LSeries.term,lemma153_coefficient_one χ β γ (lemma153GeneralMEulerProduct χ β) (by simpa using hM)])
    (fun h => lemma153_actual_term_mul χ β γ hpar hM s h)
    (fun hp => by
      simpa only [lemma153_actual_prime_power_term χ β γ hp.pos s] using
        (lemma153_actual_local_norm_series χ β γ hpar hM ⟨_,hp⟩
          (lemma32PrimeMonomial _ s) (lemma152_monomial_norm_half hp s hs.le)).1)
    (fun p => lemma153LocalNormConstant*(p:ℝ)^(-s.re))
    (fun p => mul_nonneg lemma153_local_norm_constant_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (((Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)).subtype Nat.Prime).mul_left lemma153LocalNormConstant)
  intro p hp
  simpa only [lemma153_actual_prime_power_term χ β γ hp.pos s,lemma83_prime_monomial_norm_rpow hp.pos] using
    (lemma153_actual_local_norm_series χ β γ hpar hM ⟨p,hp⟩
      (lemma32PrimeMonomial p s) (lemma152_monomial_norm_half hp s hs.le)).2

lemma lemma153_actual_dirichlet_series_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun q : Nat.Primes => ∑' n : ℕ,
      lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*lemma32PrimeMonomial q.val s^n)
      (lemma153DirichletSeries χ β γ (lemma153GeneralMEulerProduct χ β) s) := by
  have hh := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s)
    (by simp [LSeries.term,lemma153_coefficient_one χ β γ (lemma153GeneralMEulerProduct χ β) (by simpa using hM)])
    (fun {m n} h => lemma153_actual_term_mul χ β γ hpar hM s h)
    (lemma153_actual_lseries_summable χ β γ hpar hM s hs).norm (LSeries.term_zero _ s)
  change HasProd _ (∑' n : ℕ, LSeries.term (lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β)) s n)
  apply hh.congr_fun
  intro q
  apply tsum_congr
  intro n
  exact (lemma153_actual_prime_power_term χ β γ q.property.pos s n).symm

end ZhangLS.Spec
