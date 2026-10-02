import ZhangLS.Spec.Lemma153Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_tau_two_prime_power {p : ℕ} (hp : p.Prime) (e : ℕ) :
    lemma34Tau 2 (p^e) = e+1 := by
  exact (lemma34_tau_prime_power hp 1 e).trans (Nat.multichoose_two e)

lemma lemma153_coefficient_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (M : ℕ → ℕ → ℂ → ℂ) (hp : p.Prime) :
    lemma153Coefficient χ β γ M p =
      2*χ.evalNat p^2 * (M 1 p (1-γ) / M 1 1 (1-γ)) +
      2*χ.evalNat p*lemma152LambdaFactor χ β p 1*(p:ℂ)^γ *
        (M p 1 (1-γ) / M 1 1 (1-γ)) := by
  have hτ : lemma34Tau 2 p = 2 := by
    simpa using lemma153_tau_two_prime_power hp 1
  rw [lemma153Coefficient,hτ,lemma153_varpi_prime χ β γ M hp]
  push_cast
  ring

lemma lemma153_weighted_geometric_hasSum (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*x^n) (1/(1-x)^2) := by
  simpa using (hasSum_choose_mul_geometric_of_norm_lt_one 1 hx)

/-- τ₂-weighting the convolution of two geometric series. The numerator
1−a*b*x² is precisely the elementary corrected Euler factor. -/
lemma lemma153_weighted_h2_hasSum (a b x : ℂ)
    (ha : ‖a*x‖ < 1) (hb : ‖b*x‖ < 1) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*lemma83LocalH2 a b n*x^n)
      ((1-a*b*x^2)/((1-a*x)^2*(1-b*x)^2)) := by
  have hga := hasSum_geometric_of_norm_lt_one ha
  have hgb := hasSum_geometric_of_norm_lt_one hb
  have hwa := lemma153_weighted_geometric_hasSum (a*x) ha
  have hwb := lemma153_weighted_geometric_hasSum (b*x) hb
  have h1 := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_iff.mpr hwa.summable) (summable_norm_iff.mpr hgb.summable)
  have h2 := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_iff.mpr hga.summable) (summable_norm_iff.mpr hwb.summable)
  have h3 := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_iff.mpr hga.summable) (summable_norm_iff.mpr hgb.summable)
  rw [hwa.tsum_eq,hgb.tsum_eq] at h1
  rw [hga.tsum_eq,hwb.tsum_eq] at h2
  rw [hga.tsum_eq,hgb.tsum_eq] at h3
  convert (h1.add h2).sub h3 using 1
  · funext n
    simp only [lemma83LocalH2,lemma83AddConvolution,mul_sum,sum_mul,← sum_add_distrib,← sum_sub_distrib]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      ((n:ℂ)+1)*(a^i*b^j)*x^n)]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by have := mem_range.mp hk; omega
    have hc : ((k:ℂ)+1)+(((n-k:ℕ):ℂ)+1)-1 = (n:ℂ)+1 := by
      rw [Nat.cast_sub hkn]
      ring
    simp only [mul_pow]
    have hpow : x^k*x^(n-k) = x^n := by rw [← pow_add,Nat.add_sub_of_le hkn]
    symm
    calc
      _ = ((((k:ℂ)+1)+(((n-k:ℕ):ℂ)+1)-1)*a^k*b^(n-k))*(x^k*x^(n-k)) := by ring
      _ = _ := by rw [hc,hpow]; ring
  · have hax := lemma83_one_sub_ne_zero ha
    have hbx := lemma83_one_sub_ne_zero hb
    field_simp
    ring

end ZhangLS.Spec
