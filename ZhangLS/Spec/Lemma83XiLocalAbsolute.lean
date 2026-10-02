import ZhangLS.Spec.Lemma83XiBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 500000

lemma lemma83_xi_local_absolute (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) (d r : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1/2) :
    Summable (fun e : ℕ => ‖lemma83Xi β j (p^e) d r*x^e‖) ∧
      (∑' e : ℕ, ‖lemma83Xi β j (p^e) d r*x^e‖) ≤ 1+40000*‖x‖ := by
  let t : ℝ := (4/3)*‖x‖
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t ≤ 2/3 := by dsimp [t]; linarith
  have htn : ‖t‖ < 1 := by rw [Real.norm_eq_abs,abs_of_nonneg ht0]; linarith
  have hg : HasSum (fun e : ℕ => 10000*t^(e+1)) (10000*t*(1-t)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one htn).mul_left (10000*t) using 1
    funext e
    rw [pow_succ]
    ring
  have hb (e : ℕ) : ‖lemma83Xi β j (p^(e+1)) d r*x^(e+1)‖ ≤ 10000*t^(e+1) := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (10000*(4/3:ℝ)^(e+1))*‖x‖^(e+1) :=
        mul_le_mul_of_nonneg_right (lemma83_xi_prime_power_norm_bound β hβ j hp e d r)
          (pow_nonneg (norm_nonneg x) _)
      _ = _ := by dsimp [t]; rw [mul_pow]; ring
  have htail : Summable (fun e : ℕ => ‖lemma83Xi β j (p^(e+1)) d r*x^(e+1)‖) :=
    hg.summable.of_nonneg_of_le (fun e => norm_nonneg _) hb
  have hts : (∑' e : ℕ, ‖lemma83Xi β j (p^(e+1)) d r*x^(e+1)‖) ≤ 40000*‖x‖ := by
    have h1 := htail.tsum_le_tsum hb hg.summable
    rw [hg.tsum_eq] at h1
    have hd : 0 < 1-t := by linarith
    have h2 : 10000*t*(1-t)⁻¹ ≤ 40000*‖x‖ := by
      rw [← div_eq_mul_inv,div_le_iff₀ hd]
      dsimp [t] at *
      nlinarith [norm_nonneg x]
    exact h1.trans h2
  have hfull : HasSum (fun e : ℕ => ‖lemma83Xi β j (p^e) d r*x^e‖)
      ((∑' e : ℕ, ‖lemma83Xi β j (p^(e+1)) d r*x^(e+1)‖)+1) := by
    simpa using (hasSum_nat_add_iff (f := fun e => ‖lemma83Xi β j (p^e) d r*x^e‖) 1).mp
      htail.hasSum
  refine ⟨hfull.summable,?_⟩
  rw [hfull.tsum_eq]
  linarith

end ZhangLS.Spec
