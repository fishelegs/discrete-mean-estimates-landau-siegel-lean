import ZhangLS.Spec.Proposition71DyadicCoefficientEnergy

/-! # The actual weighted dyadic prime polynomial moment in Section 7 -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

lemma proposition71_primitive_inverse_sum (r : ℕ) (F : DirichletCharacter ℂ r → ℝ) :
    (∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), F θ⁻¹)=
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), F θ := by
  apply sum_bij (fun θ _ => θ⁻¹)
  · intro θ hθ
    simpa only [mem_filter,mem_univ,true_and,DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_inv] using hθ
  · intro θ hθ ψ hψ h
    exact inv_injective h
  · intro θ hθ
    refine ⟨θ⁻¹,?_,by simp⟩
    simpa only [mem_filter,mem_univ,true_and,DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_inv] using hθ
  · intro θ hθ
    rfl

lemma proposition71_paper_prime_le_twice_P {D p : ℕ}
    (hL : 3≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D) :
    (p : ℝ)≤2*lemma23PaperP D := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hz : lemma23PaperL D^(-68 : ℤ)≤1 :=
    zpow_le_one_of_nonpos₀ (by linarith : 1≤lemma23PaperL D) (by norm_num)
  have hh := ((lemma56_mem_paper_primes D p).mp hp).2.2
  unfold lemma56PrimeUpper at hh
  nlinarith

/-- The true finite prime coefficient energy, with no prime-density hypothesis. -/
theorem proposition71_actual_prime_coefficient_energy {D : ℕ}
    (hL : 3≤lemma23PaperL D) (b : ℝ) {s : ℂ} (hs : s.re=1) :
    (∑ p∈lemma56PaperPrimes D, ‖(p : ℂ)^(s+I*(b : ℂ))‖^2)≤8*lemma23PaperP D^3 := by
  have hP : 0<lemma23PaperP D := Real.exp_pos _
  have hsub : lemma56PaperPrimes D⊆Icc 1 ⌊2*lemma23PaperP D⌋₊ := by
    intro p hp
    refine mem_Icc.mpr ⟨((lemma56_mem_paper_primes D p).mp hp).1.one_le,?_⟩
    exact Nat.le_floor (proposition71_paper_prime_le_twice_P hL hp)
  have hcard : ((lemma56PaperPrimes D).card : ℝ)≤2*lemma23PaperP D := by
    have hh := card_le_card hsub
    simp only [Nat.card_Icc,add_tsub_cancel_right] at hh
    exact (by exact_mod_cast hh : ((lemma56PaperPrimes D).card : ℝ)≤⌊2*lemma23PaperP D⌋₊).trans
      (Nat.floor_le (by positivity))
  calc
    _≤∑ _p∈lemma56PaperPrimes D, (2*lemma23PaperP D)^2 := by
      apply sum_le_sum
      intro p hp
      have hpp : 0<(p : ℝ) := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.pos
      rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      simp only [add_re,mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,
        sub_zero,add_zero,hs,Real.rpow_one]
      exact pow_le_pow_left₀ hpp.le (proposition71_paper_prime_le_twice_P hL hp) 2
    _=((lemma56PaperPrimes D).card : ℝ)*(2*lemma23PaperP D)^2 := by simp
    _≤(2*lemma23PaperP D)*(2*lemma23PaperP D)^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _=_ := by ring

/-- The weighted all-primitive dyadic prime moment, uniformly for every imaginary β. -/
theorem proposition71_actual_weighted_dyadic_prime_mean {D : ℕ}
    (hL : 3≤lemma23PaperL D) {R : ℝ} (hR : 1≤R) (b : ℝ) {s : ℂ} (hs : s.re=1) :
    (∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(s+I*(b : ℂ))*θ (p : ZMod r)‖^2)≤
      (16*(32+Real.pi^2))*(R^2+lemma23PaperP D)*lemma23PaperP D^3 := by
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hh := primitive_large_sieve_finset_weighted (primitiveDyadicModuli R)
    (fun r hr => (mem_primitiveDyadicModuli.mp hr).1) (lemma56PaperPrimes D)
    (fun p => (p : ℂ)^(s+I*(b : ℂ))) hR
    (fun r hr => (mem_primitiveDyadicModuli.mp hr).2.2.le) 0 ⌊2*lemma23PaperP D⌋₊
    (fun p hp => ⟨Nat.zero_le p,by simpa using Nat.le_floor (proposition71_paper_prime_le_twice_P hL hp)⟩)
  apply hh.trans
  have henergy := proposition71_actual_prime_coefficient_energy hL b hs
  calc
    _≤(32+Real.pi^2)*(R^2+(⌊2*lemma23PaperP D⌋₊ : ℝ))*(8*lemma23PaperP D^3) := by gcongr
    _≤(32+Real.pi^2)*(R^2+2*lemma23PaperP D)*(8*lemma23PaperP D^3) := by
      gcongr
      exact Nat.floor_le (by positivity)
    _≤_ := by nlinarith [sq_nonneg R,mul_nonneg (show 0≤32+Real.pi^2 by positivity) (pow_nonneg hP 3)]

/-- The actual inverse-character prime polynomial from σ has the same full
primitive dyadic moment. No substitution of character families is assumed. -/
theorem proposition71_actual_weighted_dyadic_inverse_prime_mean {D : ℕ}
    (hL : 3≤lemma23PaperL D) {R : ℝ} (hR : 1≤R) (b : ℝ) {s : ℂ} (hs : s.re=1) :
    (∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(s+I*(b : ℂ))*θ⁻¹ (p : ZMod r)‖^2)≤
      (16*(32+Real.pi^2))*(R^2+lemma23PaperP D)*lemma23PaperP D^3 := by
  have he : (∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(s+I*(b : ℂ))*θ⁻¹ (p : ZMod r)‖^2)=
      ∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
        ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
          ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(s+I*(b : ℂ))*θ (p : ZMod r)‖^2 := by
    apply sum_congr rfl
    intro r hr
    congr 1
    exact proposition71_primitive_inverse_sum r (fun θ =>
      ‖∑ p∈lemma56PaperPrimes D, (p : ℂ)^(s+I*(b : ℂ))*θ (p : ZMod r)‖^2)
  rw [he]
  exact proposition71_actual_weighted_dyadic_prime_mean hL hR b hs

end ZhangLS.Spec
