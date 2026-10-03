import ZhangLS.Spec.Lemma83FiniteXiPerturbation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma83_quartic_half_geometric_hasSum :
    HasSum (fun k : ℕ => (k+1:ℝ)^4*(1/2:ℝ)^k) 300 := by
  have hs : HasSum (fun k : ℕ => (k+1:ℂ)^4*(1/2:ℂ)^k) 300 := by
    convert lemma32_fourth_geometric_hasSum (1/2:ℂ) (by norm_num) using 1 <;> norm_num
  apply Complex.hasSum_ofReal.mp
  convert hs using 1
  funext k
  push_cast
  rfl

/-- Multiplication by a unit phase avoids division when comparing powers. -/
lemma lemma83_phase_tail_power_difference (a t u : ℂ) (ha : ‖a‖ = 1)
    (hat : a*t=u) (k : ℕ) :
    ‖t^k-u^k‖ ≤ ‖u‖^k*(k:ℝ)*‖a-1‖ := by
  have he : a^k*(t^k-u^k) = u^k*(1-a^k) := by
    rw [mul_sub,←mul_pow,hat]
    ring
  have hnorm : ‖t^k-u^k‖ = ‖u‖^k*‖a^k-1‖ := by
    have hh := congrArg norm he
    simpa only [norm_mul,norm_pow,ha,one_pow,one_mul,norm_sub_rev] using hh
  rw [hnorm]
  have hh := mul_le_mul_of_nonneg_left (lemma83_norm_pow_sub_one a ha.le k)
    (pow_nonneg (norm_nonneg u) k)
  nlinarith only [hh]

lemma lemma83_kappa_tail_summable (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re=0)
    {p : ℕ} (hp : p.Prime) (n : ℕ) (t : ℂ) (ht : ‖t‖ < 1) :
    Summable (fun k : ℕ => lemma83Kappa β (p^(n+k))*t^k) := by
  simp_rw [lemma83_kappa_prime_power β hp]
  apply lemma83_local_kappa_shifted_summable
  all_goals simpa only [norm_mul,lemma83_cpow_shift_norm hp.pos _ (hβ _),one_mul] using ht

/-- The actual supported tail stays Lipschitz in the three finite prime phases. -/
theorem lemma83_kappa_tail_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ‖(∑' k : ℕ, lemma83Kappa β (p^(n+k))*((p:ℂ)^(-(1-β j)))^k)-
      (∑' k : ℕ, lemma83Kappa (fun _ => 0) (p^(n+k))*((p:ℂ)⁻¹)^k)‖ ≤
      900*(n+1:ℝ)^3*lemma83PrimeShiftMass β p := by
  let t : ℂ := (p:ℂ)^(-(1-β j))
  let u : ℂ := (p:ℂ)⁻¹
  let K := lemma83PrimeShiftMass β p
  have hK : 0 ≤ K := lemma83_prime_shift_mass_nonneg β p
  have hu : ‖u‖ ≤ 1/2 := lemma83_prime_reciprocal_norm_le_half hp
  have ht : ‖t‖ = ‖u‖ := by
    rw [lemma83_cpow_tail_norm hp.pos _ (hβ j),norm_inv,Complex.norm_natCast]
  have hpw (k : ℕ) : ‖t^k-u^k‖ ≤ ‖u‖^k*(k:ℝ)*K :=
    (lemma83_phase_tail_power_difference ((p:ℂ)^(-β j)) t u
      (lemma83_cpow_shift_norm hp.pos _ (hβ j))
      (lemma83_prime_reciprocal_relation _ hp.pos) k).trans
      (mul_le_mul_of_nonneg_left (lemma83_prime_shift_term_le β p j) (by positivity))
  let f : ℕ → ℂ := fun k => lemma83Kappa β (p^(n+k))*t^k-
    lemma83Kappa (fun _ => 0) (p^(n+k))*u^k
  have hb (k : ℕ) : ‖f k‖ ≤ (3*(n+1:ℝ)^3*K)*((k+1:ℝ)^4*(1/2:ℝ)^k) := by
    have he : (n+k+1:ℝ) ≤ (n+1:ℝ)*(k+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) k]
    have he3 : (n+k+1:ℝ)^3 ≤ (n+1:ℝ)^3*(k+1:ℝ)^3 := by
      rw [←mul_pow]; gcongr
    have hkk : (k:ℝ) ≤ k+1 := by linarith
    have hkn : (k+1:ℝ)^3 ≤ (k+1:ℝ)^4 := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)
    have hn : (n+1:ℝ) ≤ (n+1:ℝ)^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1≤(n+1:ℝ)) (by norm_num : (1:ℕ)≤3)
    have hk : (k+1:ℝ)^2 ≤ (k+1:ℝ)^4 := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)
    have h1 : ‖(lemma83Kappa β (p^(n+k))-lemma83Kappa (fun _ => 0) (p^(n+k)))*t^k‖ ≤
        2*(n+1:ℝ)^3*(k+1:ℝ)^4*K*(1/2:ℝ)^k := by
      rw [norm_mul,norm_pow,ht]
      calc
        _ ≤ (2*(n+k+1:ℝ)^3*K)*(1/2:ℝ)^k := mul_le_mul
          (by simpa only [Nat.cast_add] using lemma83_kappa_prime_power_perturbation β hβ hp (n+k))
          (pow_le_pow_left₀ (norm_nonneg _) hu _) (pow_nonneg (norm_nonneg _) _) (by positivity)
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right
            (he3.trans (mul_le_mul_of_nonneg_left hkn (by positivity)))
            (by positivity : 0≤2*K*(1/2:ℝ)^k)
          nlinarith only [hh]
    have h2 : ‖lemma83Kappa (fun _ => 0) (p^(n+k))*(t^k-u^k)‖ ≤
        (n+1:ℝ)^3*(k+1:ℝ)^4*K*(1/2:ℝ)^k := by
      have hnrm : ‖lemma83Kappa (fun _ => 0) (p^(n+k))‖ = (n+k+1:ℝ) := by
        rw [lemma83_kappa_prime_power_zero_shift hp]
        norm_cast
      rw [norm_mul,hnrm]
      calc
        _ ≤ (n+k+1:ℝ)*(‖u‖^k*(k:ℝ)*K) := mul_le_mul_of_nonneg_left (hpw k) (by positivity)
        _ ≤ ((n+1:ℝ)*(k+1))*((1/2:ℝ)^k*(k+1)*K) := by push_cast; gcongr
        _ = (n+1:ℝ)*(k+1:ℝ)^2*K*(1/2:ℝ)^k := by ring
        _ ≤ _ := by gcongr
    dsimp [f]
    rw [show lemma83Kappa β (p^(n+k))*t^k-lemma83Kappa (fun _ => 0) (p^(n+k))*u^k =
      (lemma83Kappa β (p^(n+k))-lemma83Kappa (fun _ => 0) (p^(n+k)))*t^k+
      lemma83Kappa (fun _ => 0) (p^(n+k))*(t^k-u^k) by ring]
    exact (norm_add_le _ _).trans (by nlinarith only [h1,h2])
  have hg := lemma83_quartic_half_geometric_hasSum.mul_left (3*(n+1:ℝ)^3*K)
  have hf : Summable (fun k => ‖f k‖) :=
    hg.summable.of_nonneg_of_le (fun k => norm_nonneg _) hb
  have hs := hf.of_norm.hasSum.norm_le_of_bounded hg hb
  have ht1 : ‖t‖ < 1 := by linarith
  have hu1 : ‖u‖ < 1 := by linarith
  rw [show (∑' k : ℕ, lemma83Kappa β (p^(n+k))*t^k)-
      (∑' k : ℕ, lemma83Kappa (fun _ => 0) (p^(n+k))*u^k) = ∑' k, f k from
      ((lemma83_kappa_tail_summable β hβ hp n t ht1).tsum_sub
        (lemma83_kappa_tail_summable (fun _ => 0) (by simp) hp n u hu1)).symm]
  nlinarith only [hs]

/-- The zero-shift supported tail is an elementary linear geometric sum. -/
lemma lemma83_zero_shift_kappa_tail {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (∑' k : ℕ, lemma83Kappa (fun _ => 0) (p^(n+k))*((p:ℂ)⁻¹)^k) =
      (n+1:ℂ)/(1-(p:ℂ)⁻¹)+(p:ℂ)⁻¹/(1-(p:ℂ)⁻¹)^2 := by
  have hu : ‖(p:ℂ)⁻¹‖ < 1 := (lemma83_prime_reciprocal_norm_le_half hp).trans_lt (by norm_num)
  have hs := ((hasSum_geometric_of_norm_lt_one hu).mul_left (n+1:ℂ)).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hu)
  convert hs.tsum_eq using 1
  · apply tsum_congr
    intro k
    rw [lemma83_kappa_prime_power_zero_shift hp]
    push_cast
    ring

lemma lemma83_lambda_prime_zero_shift {p : ℕ} (hp : p.Prime) :
    lemma83LambdaFactor (fun _ => 0) p 1 = (1-(p:ℂ)⁻¹)^2 := by
  have hu : 1-(p:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero
    ((lemma83_prime_reciprocal_norm_le_half hp).trans_lt (by norm_num))
  simp only [lemma83LambdaFactor,sub_zero,Complex.cpow_neg_one]
  field_simp

/-- Exact regular coefficient at zero shift, including the endpoint prime 2. -/
theorem lemma83_xi_prime_power_regular_zero_shift (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) (hpd : ¬p ∣ d*r) : lemma83Xi (fun _ => 0) j (p^(e+1)) d r = 1 := by
  have hu : 1-(p:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero
    ((lemma83_prime_reciprocal_norm_le_half hp).trans_lt (by norm_num))
  rw [lemma83_xi_prime_power_regular _ j hp e d r hpd]
  simp only [sub_zero,Complex.cpow_neg_one]
  rw [lemma83_lambda_prime_zero_shift hp,lemma83_zero_shift_kappa_tail hp,
    lemma83_kappa_prime_power_zero_shift hp,Complex.cpow_one]
  have hz := lemma83_prime_mobius_weight (0:ℂ) hp
  simp only [sub_zero,Complex.cpow_one,neg_zero,Complex.cpow_zero] at hz
  rw [mul_div_assoc,hz]
  push_cast
  generalize huval : (p:ℂ)⁻¹ = u at hu ⊢
  field_simp [hu] <;> ring

end ZhangLS.Spec
