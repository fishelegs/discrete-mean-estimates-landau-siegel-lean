import ZhangLS.Spec.Lemma83Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma83_supported_eq_one {d m : ℕ}
    (hdm : ∀ p ∈ d.primeFactors, p ∣ m) (h : Lemma83SupportedIndex d m) : h.val = 1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hph
  have hpd : p ∈ d.primeFactors := h.property.2.1
    (Nat.mem_primeFactors.mpr ⟨hp,hph,h.property.1⟩)
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes h.property.2.2 hph (hdm p hpd))

/-- When every supporting prime is excluded by coprimality, only h=1 remains. -/
lemma lemma83_modified_kappa_excluded (β : Fin 3 → ℂ) (d m : ℕ) (s : ℂ)
    (hdm : ∀ p ∈ d.primeFactors, p ∣ m) :
    lemma83ModifiedKappa β d m s = lemma83Kappa β d := by
  let oneIndex : Lemma83SupportedIndex d m := ⟨1,by simp⟩
  have hone (h : Lemma83SupportedIndex d m) : h = oneIndex := by
    apply Subtype.ext
    exact lemma83_supported_eq_one hdm h
  unfold lemma83ModifiedKappa
  rw [tsum_eq_single oneIndex (by intro h hne; exact False.elim (hne (hone h)))]
  simp [oneIndex]

@[simp] lemma lemma83_modified_kappa_one (β : Fin 3 → ℂ) (m : ℕ) (s : ℂ) :
    lemma83ModifiedKappa β 1 m s = 1 := by
  rw [lemma83_modified_kappa_excluded β 1 m s (by simp)]
  simp

lemma lemma83_modified_kappa_prime_power_excluded (β : Fin 3 → ℂ)
    {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) (e : ℕ) (s : ℂ) :
    lemma83ModifiedKappa β (p^e) m s = lemma83Kappa β (p^e) := by
  apply lemma83_modified_kappa_excluded
  intro q hq
  have hqp : q ∣ p := (Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow
    (Nat.dvd_of_mem_primeFactors hq)
  exact hqp.trans hpm

@[simp] lemma lemma83_modified_lambda_one (β : Fin 3 → ℂ) (j : Fin 3) (m : ℕ) :
    lemma83ModifiedLambda β j 1 m = 1 := by simp [lemma83ModifiedLambda]

@[simp] lemma lemma83_xi_one (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    lemma83Xi β j 1 d r = 1 := by
  simp [lemma83Xi,Finset.filter_singleton]

@[simp] lemma lemma83_xi_zero (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    lemma83Xi β j 0 d r = 0 := by simp [lemma83Xi]

end ZhangLS.Spec
