import ZhangLS.Spec.Lemma83FiniteXiUniform
import ZhangLS.Spec.Lemma83XiMoebiusConvolution

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def lemma83XiMoebiusMass (β : Fin 3 → ℂ) (j : Fin 3) (d r n : ℕ) : ℝ :=
  ‖lemma83XiMoebius β j d r n‖/(n:ℝ)

noncomputable def lemma83XiZeroLocalTail (p d r : ℕ) : ℝ :=
  if p ∣ r then 1 else if p ∣ d then ((p:ℝ)-1)⁻¹ else 0

lemma lemma83_xi_moebius_zero_shift_prime_power (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) : lemma83XiMoebius (fun _ => 0) j d r (p^(e+1)) =
      if p ∣ r then 1 else if p ∣ d then -(1/(p-1:ℕ):ℂ) else 0 := by
  rw [lemma83_xi_moebius_prime_power _ j hp]
  by_cases hpr : p ∣ r
  · rw [if_pos hpr,lemma83_xi_prime_power_r_zero_shift j hp e d r hpr]
    cases e with
    | zero => norm_num
    | succ e => rw [lemma83_xi_prime_power_r_zero_shift j hp e d r hpr]; push_cast; ring
  rw [if_neg hpr]
  by_cases hpd : p ∣ d
  · rw [if_pos hpd,lemma83_xi_prime_power_d_zero_shift j hp e d r hpd hpr]
    cases e with
    | zero => norm_num
    | succ e => rw [lemma83_xi_prime_power_d_zero_shift j hp e d r hpd hpr]; push_cast; ring
  · have hprd : ¬p ∣ d*r := fun h => (hp.dvd_mul.mp h).elim hpd hpr
    rw [if_neg hpd,lemma83_xi_prime_power_regular_zero_shift j hp e d r hprd]
    cases e with
    | zero => norm_num
    | succ e => rw [lemma83_xi_prime_power_regular_zero_shift j hp e d r hprd]; simp

lemma lemma83_xi_zero_local_tail_nonneg {p : ℕ} (hp : p.Prime) (d r : ℕ) :
    0 ≤ lemma83XiZeroLocalTail p d r := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  unfold lemma83XiZeroLocalTail
  split_ifs <;> positivity

lemma lemma83_xi_moebius_zero_shift_prime_norm (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) : ‖lemma83XiMoebius (fun _ => 0) j d r (p^(e+1))‖ =
      lemma83XiZeroLocalTail p d r := by
  rw [lemma83_xi_moebius_zero_shift_prime_power j hp]
  unfold lemma83XiZeroLocalTail
  split_ifs <;> simp only [norm_one,norm_zero,norm_neg,norm_div,norm_one,Complex.norm_natCast]
  rw [Nat.cast_sub hp.one_le,Nat.cast_one,one_div]

lemma lemma83_xi_moebius_zero_local_hasSum (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (d r : ℕ) :
    HasSum (fun e : ℕ => lemma83XiMoebiusMass (fun _ => 0) j d r (p^e))
      (1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1)) := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (p:ℝ)≠0 := by positivity
  have hs := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ (p:ℝ)⁻¹)
    ((inv_lt_one₀ (by positivity)).mpr hp1)).mul_left
      (lemma83XiZeroLocalTail p d r*(p:ℝ)⁻¹)
  have ht : HasSum (fun e : ℕ => lemma83XiMoebiusMass (fun _ => 0) j d r (p^(e+1)))
      (lemma83XiZeroLocalTail p d r/((p:ℝ)-1)) := by
    convert hs using 1
    · funext e
      unfold lemma83XiMoebiusMass
      rw [lemma83_xi_moebius_zero_shift_prime_norm j hp, Nat.cast_pow,
        div_eq_mul_inv,←inv_pow,pow_succ]
      ring
    · have hpm : (p:ℝ)-1 ≠ 0 := by linarith
      field_simp
  have hh := (hasSum_nat_add_iff (f := fun e => lemma83XiMoebiusMass (fun _ => 0) j d r (p^e)) 1).mp ht
  simpa [lemma83XiMoebiusMass,add_comm] using hh

lemma lemma83_xi_moebius_prime_power_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) :
    ‖lemma83XiMoebius β j d r (p^(e+1))-lemma83XiMoebius (fun _ => 0) j d r (p^(e+1))‖ ≤
      13000*(e+2:ℝ)^3*lemma83PrimeShiftMass β p := by
  rw [lemma83_xi_moebius_prime_power β j hp,lemma83_xi_moebius_prime_power (fun _ => 0) j hp]
  rw [show (lemma83Xi β j (p^(e+1)) d r-lemma83Xi β j (p^e) d r)-
      (lemma83Xi (fun _ => 0) j (p^(e+1)) d r-lemma83Xi (fun _ => 0) j (p^e) d r) =
      (lemma83Xi β j (p^(e+1)) d r-lemma83Xi (fun _ => 0) j (p^(e+1)) d r)-
      (lemma83Xi β j (p^e) d r-lemma83Xi (fun _ => 0) j (p^e) d r) by ring]
  have h1 := lemma83_xi_prime_power_perturbation β hβ j hp (e+1) d r
  have h0 := lemma83_xi_prime_power_perturbation β hβ j hp e d r
  have hh := norm_sub_le (lemma83Xi β j (p^(e+1)) d r-lemma83Xi (fun _ => 0) j (p^(e+1)) d r)
    (lemma83Xi β j (p^e) d r-lemma83Xi (fun _ => 0) j (p^e) d r)
  have hpw : (e+1:ℝ)^3 ≤ (e+2:ℝ)^3 := by gcongr; linarith
  push_cast at h1
  nlinarith [mul_le_mul_of_nonneg_right hpw (lemma83_prime_shift_mass_nonneg β p)]

/-- Absolute harmonic mass of the genuine μ*ξ local series, with an additive
finite-shift error. Infinite exponents are summed at just this one prime. -/
theorem lemma83_xi_moebius_local_mass (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime) (d r : ℕ) :
    Summable (fun e : ℕ => lemma83XiMoebiusMass β j d r (p^e)) ∧
      (∑' e : ℕ, lemma83XiMoebiusMass β j d r (p^e)) ≤
        1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1)+31200000*lemma83PrimeShiftMass β p/(p:ℝ) := by
  let K := lemma83PrimeShiftMass β p
  have hK : 0 ≤ K := lemma83_prime_shift_mass_nonneg β p
  let f : ℕ → ℝ := fun e => ‖lemma83XiMoebius β j d r (p^e)-lemma83XiMoebius (fun _ => 0) j d r (p^e)‖/(p^e:ℕ)
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hhalf : (p:ℝ)⁻¹ ≤ 1/2 := by
    simpa only [norm_inv,Complex.norm_natCast] using lemma83_prime_reciprocal_norm_le_half hp
  have hb (e : ℕ) : f (e+1) ≤ (104000*K/(p:ℝ))*((e+1:ℝ)^4*(1/2:ℝ)^e) := by
    dsimp [f]
    rw [Nat.cast_pow,div_eq_mul_inv,←inv_pow,pow_succ]
    have he : (e+2:ℝ)^3 ≤ 8*(e+1:ℝ)^4 := by
      calc
        _ ≤ (2*(e+1:ℝ))^3 := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) e]
        _ = 8*(e+1:ℝ)^3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) e]) (by norm_num : (3:ℕ)≤4))
          (by norm_num)
    have h1 := lemma83_xi_moebius_prime_power_perturbation β hβ j hp e d r
    calc
      _ ≤ (13000*(e+2:ℝ)^3*K)*((1/2:ℝ)^e*(p:ℝ)⁻¹) := mul_le_mul h1
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (by positivity))
        (by positivity) (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 13000*K*(1/2:ℝ)^e*(p:ℝ)⁻¹)
        convert hh using 1 <;> ring
  have hg := lemma83_quartic_half_geometric_hasSum.mul_left (104000*K/(p:ℝ))
  have ht : Summable (fun e => f (e+1)) := hg.summable.of_nonneg_of_le
    (fun e => by dsimp [f]; positivity) hb
  have hfs : Summable f := (summable_nat_add_iff 1).mp ht
  have hfm : (∑' e, f e) ≤ 31200000*K/(p:ℝ) := by
    have hh := ht.tsum_le_tsum hb hg.summable
    rw [hg.tsum_eq] at hh
    rw [hfs.tsum_eq_zero_add]
    have hf0 : f 0 = 0 := by simp [f]
    rw [hf0,zero_add]
    exact hh.trans_eq (by ring)
  have hz := lemma83_xi_moebius_zero_local_hasSum j hp d r
  have hpoint (e : ℕ) : lemma83XiMoebiusMass β j d r (p^e) ≤
      lemma83XiMoebiusMass (fun _ => 0) j d r (p^e)+f e := by
    dsimp [lemma83XiMoebiusMass,f]
    rw [←add_div]
    exact div_le_div_of_nonneg_right (norm_le_norm_add_norm_sub' _ _) (by positivity)
  have hsum := (hz.summable.add hfs).of_nonneg_of_le
    (fun e => by dsimp [lemma83XiMoebiusMass]; positivity) hpoint
  refine ⟨hsum,?_⟩
  have hh := hsum.tsum_le_tsum hpoint (hz.summable.add hfs)
  rw [hz.summable.tsum_add hfs,hz.tsum_eq] at hh
  linarith

end ZhangLS.Spec
