import ZhangLS.Spec.Lemma83XiLocalAbsolute
import ZhangLS.Spec.Lemma83ConverseEuler
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 500000

lemma lemma83_xi_term_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) (s : ℂ) :
    LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s 1 = 1 := by
  simp [LSeries.term,lemma83_xi_one,RealPrimitiveCharacter.evalNat]

lemma lemma83_xi_term_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ) (s : ℂ)
    (hmn : m.Coprime n) :
    LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s (m*n) =
      LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s m *
      LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s n := by
  by_cases hm : m = 0
  · subst m; simp
  by_cases hn : n = 0
  · subst n; simp
  have hXi : lemma83Xi β j (m*n) d r = lemma83Xi β j m d r * lemma83Xi β j n d r :=
    (lemma83_xi_multiplicative β hβ j d r).map_mul_of_coprime hmn
  have hχ : χ.evalNat (m*n) = χ.evalNat m * χ.evalNat n := by
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_mul,map_mul]
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,hXi,hχ,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  ring

lemma lemma83_xi_prime_power_term {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) (hp : 0 < p) (s : ℂ) (e : ℕ) :
    LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s (p^e) =
      lemma83Xi β j (p^e) d r * (χ.evalNat p * lemma32PrimeMonomial p s)^e := by
  have hχ : χ.evalNat (p^e) = χ.evalNat p^e := by
    simp [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow]
  rw [LSeries.term_of_ne_zero (pow_ne_zero e hp.ne'),hχ,Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p e s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s,mul_pow]
  ring

lemma lemma83_character_monomial_half {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : Nat.Primes) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ.evalNat p.val * lemma32PrimeMonomial p.val s‖ ≤ 1/2 := by
  have hn : ‖χ.evalNat p.val * lemma32PrimeMonomial p.val s‖ ≤ (p.val:ℝ)^(-s.re) := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖lemma32PrimeMonomial p.val s‖ :=
        mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one _) (norm_nonneg _)
      _ = _ := by rw [one_mul,lemma83_prime_monomial_norm_rpow p.property.pos]
  calc
    _ ≤ (p.val:ℝ)^(-s.re) := hn
    _ ≤ (p.val:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast p.property.one_le) (by linarith)
    _ = (p.val:ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1/2 := by simpa only [norm_inv,Complex.norm_natCast] using
      lemma83_prime_reciprocal_norm_le_half p.property

/-- Absolute convergence of the actual ξ Dirichlet series on Re(s)>1. -/
lemma lemma83_xi_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => χ.evalNat n * lemma83Xi β j n d r) s := by
  rw [LSeriesSummable,← summable_norm_iff]
  apply EulerProduct.summable_norm_of_prime_power_tsum_le
    (f := LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s)
    (LSeries.term_zero _ s) (lemma83_xi_term_one χ β j d r s)
    (fun h => lemma83_xi_term_mul χ β hβ j d r s h)
    (u := fun p => 40000*(p:ℝ)^(-s.re))
  · intro p hp
    simpa only [lemma83_xi_prime_power_term χ β j d r hp.pos] using
      (lemma83_xi_local_absolute β hβ j hp d r (χ.evalNat p*lemma32PrimeMonomial p s)
        (lemma83_character_monomial_half χ ⟨p,hp⟩ s hs.le)).1
  · intro p
    positivity
  · exact ((Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)).subtype Nat.Prime).mul_left _
  · intro p hp
    have hh := (lemma83_xi_local_absolute β hβ j hp d r (χ.evalNat p*lemma32PrimeMonomial p s)
      (lemma83_character_monomial_half χ ⟨p,hp⟩ s hs.le)).2
    simp only [lemma83_xi_prime_power_term χ β j d r hp.pos]
    apply hh.trans
    have hn : ‖χ.evalNat p*lemma32PrimeMonomial p s‖ ≤ (p:ℝ)^(-s.re) := by
      rw [norm_mul]
      calc
        _ ≤ 1*‖lemma32PrimeMonomial p s‖ :=
          mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one _) (norm_nonneg _)
        _ = _ := by rw [one_mul,lemma83_prime_monomial_norm_rpow hp.pos]
    linarith

lemma lemma83_xi_euler_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      LSeries.term (fun n => χ.evalNat n * lemma83Xi β j n d r) s (p.val^e))
      (lemma83XiDirichletSeries χ β j d r s) :=
  EulerProduct.eulerProduct_hasProd (lemma83_xi_term_one χ β j d r s)
    (fun h => lemma83_xi_term_mul χ β hβ j d r s h)
    (lemma83_xi_lseries_summable χ β hβ j d r s hs).norm (LSeries.term_zero _ s)

end ZhangLS.Spec
