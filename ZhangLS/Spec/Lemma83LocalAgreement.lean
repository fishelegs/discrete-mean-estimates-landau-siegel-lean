import ZhangLS.Spec.Lemma83XiSeries
import ZhangLS.Spec.Lemma83RegularProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma83_actual_kappa_rational_cyclic (β : Fin 3 → ℂ) (p : ℕ) (j : Fin 3) (x : ℂ) :
    lemma83ActualKappaRational β p x =
      lemma83KappaRational ((p:ℂ)^(-β j)) ((p:ℂ)^(-β (j+1))) ((p:ℂ)^(-β (j+2))) x := by
  fin_cases j
  · rfl
  · change lemma83ActualKappaRational β p x =
      lemma83KappaRational ((p:ℂ)^(-β 1)) ((p:ℂ)^(-β 2)) ((p:ℂ)^(-β 0)) x
    unfold lemma83ActualKappaRational lemma83KappaRational
    congr 1
    ring
  · change lemma83ActualKappaRational β p x =
      lemma83KappaRational ((p:ℂ)^(-β 2)) ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x
    unfold lemma83ActualKappaRational lemma83KappaRational
    congr 1
    ring

lemma lemma83_lambda_factor_inverse (β : Fin 3 → ℂ) {p : ℕ} (hp : 0 < p) (s : ℂ) :
    lemma83LambdaFactor β p s = (lemma83ActualKappaRational β p ((p:ℂ)^(-s)))⁻¹ := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h (i : Fin 3) : (p:ℂ)^(-s-β i) = (p:ℂ)^(-β i)*(p:ℂ)^(-s) := by
    rw [show -s-β i = -β i + -s by ring,Complex.cpow_add _ _ hn]
  simp only [lemma83LambdaFactor,h,lemma83ActualKappaRational,lemma83KappaRational,inv_div]

lemma lemma83_prime_reciprocal_relation (β : ℂ) {p : ℕ} (hp : 0 < p) :
    (p:ℂ)^(-β)*(p:ℂ)^(-(1-β)) = (p:ℂ)⁻¹ := by
  rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hp.ne')]
  rw [show -β + -(1-β) = (-1:ℂ) by ring,Complex.cpow_neg_one]

lemma lemma83_prime_mobius_weight (β : ℂ) {p : ℕ} (hp : p.Prime) :
    (p:ℂ)^(1-β)/(p-1 : ℕ) = (p:ℂ)^(-β)/(1-(p:ℂ)⁻¹) := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpn : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [Complex.cpow_sub _ _ hn,Complex.cpow_one,Complex.cpow_neg,
    Nat.cast_sub hp.one_le,Nat.cast_one]
  repeat' field_simp [hn,hpn]
  all_goals ring

lemma lemma83_cpow_shift_norm {p : ℕ} (hp : 0 < p) (β : ℂ) (hβ : β.re = 0) :
    ‖(p:ℂ)^(-β)‖ = 1 := by
  rw [← lemma32_prime_monomial_eq_cpow hp]
  exact lemma83_shift_monomial_norm hp β hβ

lemma lemma83_cpow_tail_norm {p : ℕ} (hp : 0 < p) (β : ℂ) (hβ : β.re = 0) :
    ‖(p:ℂ)^(-(1-β))‖ = (p:ℝ)⁻¹ := by
  rw [← lemma32_prime_monomial_eq_cpow hp]
  exact lemma83_t_monomial_norm hp β hβ

lemma lemma83_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1-z ≠ 0 := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  rw [he,norm_one] at hz
  linarith

/-- The actual local ξ series, multiplied by the two L-removal factors,
is the explicit regular correction. -/
lemma lemma83_xi_regular_correction (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) (d r : ℕ) (hpd : ¬p ∣ d*r)
    (x : ℂ) (hx : ‖x‖ < 1) (hxt : x ≠ (p:ℂ)^(-(1-β j))) :
    lemma83LocalRemoval ((p:ℂ)^(-β (j+1))) ((p:ℂ)^(-β (j+2))) x *
      (∑' n : ℕ, lemma83Xi β j (p^n) d r*x^n) =
        lemma83RegularCorrection ((p:ℂ)^(-β (j+1))) ((p:ℂ)^(-β (j+2)))
          ((p:ℂ)^(-(1-β j))) x := by
  have hnorm (i : Fin 3) := lemma83_cpow_shift_norm hp.pos (β i) (hβ i)
  have ht : ‖(p:ℂ)^(-(1-β j))‖ < 1 := by
    rw [lemma83_cpow_tail_norm hp.pos _ (hβ j)]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hix (i : Fin 3) : 1-(p:ℂ)^(-β i)*x ≠ 0 :=
    lemma83_one_sub_ne_zero (by simpa [norm_mul,hnorm i] using hx)
  have hit (i : Fin 3) : 1-(p:ℂ)^(-β i)*(p:ℂ)^(-(1-β j)) ≠ 0 :=
    lemma83_one_sub_ne_zero (by simpa [norm_mul,hnorm i] using ht)
  have hu : 1-(p:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa only [norm_inv,Complex.norm_natCast] using
      (show (p:ℝ)⁻¹ < 1 from (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr
        (by exact_mod_cast hp.one_lt)))
  rw [(lemma83_xi_regular_hasSum β j hp hnorm d r hpd x hx ht hxt).tsum_eq,
    lemma83_lambda_factor_inverse β hp.pos,
    lemma83_actual_kappa_rational_cyclic β p j x,
    lemma83_actual_kappa_rational_cyclic β p j ((p:ℂ)^(-(1-β j))),
    lemma83_prime_mobius_weight (β j) hp]
  exact lemma83_regular_correction_identity _ _ _ _ _ _
    (lemma83_prime_reciprocal_relation (β j) hp.pos) (sub_ne_zero.mpr hxt)
    (lemma83_one_sub_ne_zero ht) (lemma83_one_sub_ne_zero hx) hu
    (hix j) (hix (j+1)) (hix (j+2)) (hit (j+1)) (hit (j+2))

lemma lemma83_xi_r_correction (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) (d r : ℕ) (hpr : p ∣ r)
    (x : ℂ) (hx : ‖x‖ < 1) :
    lemma83LocalRemoval ((p:ℂ)^(-β (j+1))) ((p:ℂ)^(-β (j+2))) x *
      (∑' n : ℕ, lemma83Xi β j (p^n) d r*x^n) =
        lemma83RCorrection ((p:ℂ)^(-β j)) x := by
  have hix (i : Fin 3) : ‖(p:ℂ)^(-β i)*x‖ < 1 := by
    simpa [norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i)] using hx
  rw [(lemma83_xi_r_hasSum β j hp d r hpr x hix).tsum_eq,
    lemma83_actual_kappa_rational_cyclic β p j x]
  exact lemma83_r_correction_identity _ _ _ _ (lemma83_one_sub_ne_zero hx)
    (lemma83_one_sub_ne_zero (hix j)) (lemma83_one_sub_ne_zero (hix (j+1)))
    (lemma83_one_sub_ne_zero (hix (j+2)))

lemma lemma83_xi_d_correction (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) (d r : ℕ) (hpd : p ∣ d) (hpr : ¬p ∣ r)
    (x : ℂ) (hx : ‖x‖ < 1) :
    lemma83LocalRemoval ((p:ℂ)^(-β (j+1))) ((p:ℂ)^(-β (j+2))) x *
      (∑' n : ℕ, lemma83Xi β j (p^n) d r*x^n) =
        lemma83DCorrection ((p:ℂ)^(-β j)) ((p:ℂ)⁻¹) x := by
  have hix (i : Fin 3) : ‖(p:ℂ)^(-β i)*x‖ < 1 := by
    simpa [norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i)] using hx
  have hu : 1-(p:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa only [norm_inv,Complex.norm_natCast] using
      (show (p:ℝ)⁻¹ < 1 from (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr
        (by exact_mod_cast hp.one_lt)))
  rw [(lemma83_xi_d_hasSum β j hp d r hpd hpr x hix).tsum_eq,
    lemma83_actual_kappa_rational_cyclic β p j x,lemma83_prime_mobius_weight (β j) hp]
  rw [sub_mul,one_mul]
  exact lemma83_d_correction_identity _ _ _ _ _ hu (lemma83_one_sub_ne_zero hx)
    (lemma83_one_sub_ne_zero (hix j)) (lemma83_one_sub_ne_zero (hix (j+1)))
    (lemma83_one_sub_ne_zero (hix (j+2)))

end ZhangLS.Spec
