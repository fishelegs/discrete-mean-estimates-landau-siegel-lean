import ZhangLS.Spec.Lemma153Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma153_coefficient_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hM : M 1 1 (1-γ) ≠ 0) : lemma153Coefficient χ β γ M 1 = 1 := by
  simp [lemma153Coefficient,lemma153_varpi_one χ β γ M hM,
    lemma34Tau,RealPrimitiveCharacter.evalNat]
  exact (lemma34_tau_multiplicative 2).map_one

lemma lemma153_coefficient_ramified_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hp : p.Prime) (hpD : p ∣ D) (n : ℕ) :
    lemma153Coefficient χ β γ M (p^(n+1)) = 0 := by
  have hv := χ.evalNat_eq_zero_of_dvd_modulus hpD hp.ne_one
  have hpow : χ.evalNat (p^(n+1)) = 0 := by
    simpa only [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow,zero_pow (Nat.succ_ne_zero n)]
      using congrArg (fun z : ℂ => z^(n+1)) hv
  simp [lemma153Coefficient,hpow]

/-- Ramification removes the entire positive-degree local Dirichlet series.
Consequently its ζ²-removal is exactly (1−q⁻ˢ)², with no α-error. -/
lemma lemma153_ramified_local_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hM : M 1 1 (1-γ) ≠ 0) (hp : p.Prime) (hpD : p ∣ D) (z : ℂ) :
    HasSum (fun n : ℕ => lemma153Coefficient χ β γ M (p^n)*z^n) 1 := by
  convert (hasSum_ite_eq 0 (1:ℂ)) using 1
  funext n
  cases n with
  | zero => simp [lemma153_coefficient_one χ β γ M hM]
  | succ n => simp [lemma153_coefficient_ramified_prime_power χ β γ M hp hpD n]

lemma lemma153_ramified_local_extraction {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ)
    (hM : M 1 1 (1-γ) ≠ 0) (hp : p.Prime) (hpD : p ∣ D) (z w : ℂ) :
    (1-z)^2*(1-χ.evalNat p*w*z)^2 *
      (∑' n : ℕ, lemma153Coefficient χ β γ M (p^n)*z^n) = (1-z)^2 := by
  rw [(lemma153_ramified_local_hasSum χ β γ M hM hp hpD z).tsum_eq,
    χ.evalNat_eq_zero_of_dvd_modulus hpD hp.ne_one]
  ring

lemma lemma153_ramified_factor_bound (z : ℂ) : ‖(1-z)^2‖ ≤ (1+‖z‖)^2 := by
  rw [norm_pow]
  gcongr
  simpa only [norm_one] using norm_sub_le (1:ℂ) z

/-- The explicit finite ramified bound keeps its D-dependence visible. -/
lemma lemma153_ramified_product_bound (S : Finset ℕ) (z : ℕ → ℂ) :
    ‖∏ q ∈ S, (1-z q)^2‖ ≤ ∏ q ∈ S, (1+‖z q‖)^2 := by
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun q _ => lemma153_ramified_factor_bound (z q))

end ZhangLS.Spec
