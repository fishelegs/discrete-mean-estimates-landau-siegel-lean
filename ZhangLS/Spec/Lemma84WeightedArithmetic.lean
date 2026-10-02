import ZhangLS.Spec.Lemma83XiBounds
import ZhangLS.Spec.Lemma83FinitePrimeBounds
import Mathlib.Data.Nat.Totient

/-! Genuine arithmetic weights for the Section 8 use of repaired Lemma 8.4.
The estimates keep λ₀ⱼ, μ and φ, with no assumed norm envelope.
Source: arXiv:2211.02515v1, TeX 2324–2327 and 2437–2460. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- Local λ bound retaining the reciprocal-prime gain, uniform in all purely
imaginary shifts. A constant bound at each prime would be insufficient here. -/
theorem lemma84_lambda_prime_weight (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime) :
    ‖lemma83LambdaFactor β p (1-β j)‖ ≤ 1+12/(p:ℝ) := by
  let a : ℝ := (p:ℝ)⁻¹
  have ha0 : 0≤a := by dsimp [a]; positivity
  have ha : a≤1/2 := by
    simpa only [a,norm_inv,Complex.norm_natCast] using lemma83_prime_reciprocal_norm_le_half hp
  let t : ℂ := (p:ℂ)^(-(1-β j))
  have ht : ‖t‖=a := lemma83_cpow_tail_norm hp.pos (β j) (hβ j)
  have hden : 1-a≤‖1-t‖ := by
    have hh := norm_sub_norm_le (1:ℂ) t
    simpa only [norm_one,ht] using hh
  have hb (i : Fin 3) : ‖1-(p:ℂ)^(-β i)*t‖ ≤ 1+a := by
    have hh := norm_sub_le (1:ℂ) ((p:ℂ)^(-β i)*t)
    simpa only [norm_one,norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i),ht,one_mul] using hh
  rw [lemma83_lambda_factor_inverse β hp.pos]
  change ‖(lemma83ActualKappaRational β p t)⁻¹‖ ≤ _
  rw [lemma83ActualKappaRational,lemma83KappaRational,inv_div,norm_div,norm_mul,norm_mul]
  have hnum : ‖1-(p:ℂ)^(-β 0)*t‖*‖1-(p:ℂ)^(-β 1)*t‖*‖1-(p:ℂ)^(-β 2)*t‖≤(1+a)^3 := by
    have hh := mul_le_mul (mul_le_mul (hb 0) (hb 1) (norm_nonneg _) (by positivity))
      (hb 2) (norm_nonneg _) (by positivity : 0≤(1+a)*(1+a))
    nlinarith only [hh]
  calc
    _ ≤ (1+a)^3/(1-a) := div_le_div₀ (by positivity) hnum (by linarith) hden
    _ ≤ 1+12*a := by
      apply (div_le_iff₀ (by linarith : 0<1-a)).mpr
      have ha2 : a^2≤a/2 := by nlinarith
      have ha3 : a^3≤a/4 := by nlinarith [mul_le_mul_of_nonneg_left ha2 ha0]
      nlinarith
    _ = _ := by dsimp [a]; ring

/-- The genuine λ₀ⱼ arithmetic factor is bounded by an explicit finite product. -/
theorem lemma84_lambda_product_weight (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) (n : ℕ) :
    ‖lemma83Lambda β n (1-β j)‖≤∏ p∈n.primeFactors, (1+12/(p:ℝ)) := by
  rw [lemma83Lambda,norm_prod]
  exact prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp =>
    lemma84_lambda_prime_weight β hβ j (Nat.prime_of_mem_primeFactors hp))

/-- Explicit D-free constant and exponent for the actual λ weight. -/
theorem lemma84_lambda_uniform_weight (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {n : ℕ} (hn : 0<n)
    {y : ℝ} (hy : 1<y) (hny : Real.log n≤y) :
    ‖lemma83Lambda β n (1-β j)‖≤
      Real.exp (12/Real.log 2)*(1+Real.log y)^36 := by
  exact (lemma84_lambda_product_weight β hβ j n).trans
    (lemma83_prime_product_uniform_le n hn y 12 36 hy hny (by norm_num) (by norm_num))

/-- Euler's totient formula over the reals, including n=0. -/
theorem lemma84_totient_real_product (n : ℕ) :
    (Nat.totient n : ℝ)=(n:ℝ)*∏ p∈n.primeFactors, (1-(p:ℝ)⁻¹) := by
  have h := congrArg (fun z : ℚ => (z:ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,Rat.cast_one,Rat.cast_inv] using h

/-- The actual reciprocal φ weight has the needed extra 1/n. -/
theorem lemma84_reciprocal_totient_product {n : ℕ} (hn : 0<n) :
    (Nat.totient n : ℝ)⁻¹≤(n:ℝ)⁻¹*∏ p∈n.primeFactors, (1+2/(p:ℝ)) := by
  rw [lemma84_totient_real_product,mul_inv_rev,← prod_inv_distrib,mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply prod_le_prod
  · intro p hp
    apply inv_nonneg.mpr
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hh : (p:ℝ)⁻¹≤1/2 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h2
    linarith
  · intro p hp
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h0 : 0<(p:ℝ) := by linarith
    have hh : (p:ℝ)⁻¹≤1/2 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h2
    have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
    rw [inv_eq_one_div,div_le_iff₀ (by linarith : 0<1-(p:ℝ)⁻¹)]
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hh hp0]

theorem lemma84_reciprocal_totient_uniform {n : ℕ} (hn : 0<n)
    {y : ℝ} (hy : 1<y) (hny : Real.log n≤y) :
    (Nat.totient n : ℝ)⁻¹≤
      (n:ℝ)⁻¹*(Real.exp (2/Real.log 2)*(1+Real.log y)^6) := by
  apply (lemma84_reciprocal_totient_product hn).trans
  exact mul_le_mul_of_nonneg_left
    (lemma83_prime_product_uniform_le n hn y 2 6 hy hny (by norm_num) (by norm_num))
    (by positivity)

end ZhangLS.Spec
