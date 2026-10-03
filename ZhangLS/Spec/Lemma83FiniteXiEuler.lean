import ZhangLS.Spec.Lemma83FiniteXiLocalMass
import ZhangLS.Spec.Lemma83FinitePrimeBounds
import Mathlib.NumberTheory.EulerProduct.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

@[simp] lemma lemma83_xi_moebius_mass_one (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) :
    lemma83XiMoebiusMass β j d r 1 = 1 := by simp [lemma83XiMoebiusMass]

lemma lemma83_xi_moebius_mass_nonneg (β : Fin 3 → ℂ) (j : Fin 3) (d r n : ℕ) :
    0 ≤ lemma83XiMoebiusMass β j d r n := by unfold lemma83XiMoebiusMass; positivity

lemma lemma83_xi_moebius_mass_mul (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re=0)
    (j : Fin 3) (d r : ℕ) {m n : ℕ} (h : m.Coprime n) :
    lemma83XiMoebiusMass β j d r (m*n)=
      lemma83XiMoebiusMass β j d r m*lemma83XiMoebiusMass β j d r n := by
  simp only [lemma83XiMoebiusMass,(lemma83_xi_moebius_multiplicative β hβ j d r).map_mul_of_coprime h,
    norm_mul,Nat.cast_mul]
  ring

/-- The finite integer sum is dominated by a product over primes at most N.
No all-prime Euler product at real part one is introduced. -/
theorem lemma83_xi_moebius_mass_finite_euler (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) (d r N : ℕ) :
    (∑ n ∈ Icc 1 N, lemma83XiMoebiusMass β j d r n) ≤
      ∏ p ∈ (Icc 1 N).filter Nat.Prime,
        (1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1)+31200000*lemma83PrimeShiftMass β p/(p:ℝ)) := by
  let A : Set ℕ := Nat.factoredNumbers (Icc 1 N)
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖lemma83XiMoebiusMass β j d r (p^k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs,abs_of_nonneg (lemma83_xi_moebius_mass_nonneg β j d r _)] using
      (lemma83_xi_moebius_local_mass β hβ j hp d r).1
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (lemma83_xi_moebius_mass_one β j d r) (lemma83_xi_moebius_mass_mul β hβ j d r) hlocal (Icc 1 N)
  have hAsum : Summable (fun n : A => lemma83XiMoebiusMass β j d r n.val) := hEuler.2.summable
  have hIsum : Summable (A.indicator (lemma83XiMoebiusMass β j d r)) :=
    summable_subtype_iff_indicator.mp hAsum
  have he : (∑ n∈Icc 1 N,lemma83XiMoebiusMass β j d r n)=
      ∑ n∈Icc 1 N,A.indicator (lemma83XiMoebiusMass β j d r) n := by
    apply sum_congr rfl
    intro n hn
    have hn0 : n≠0 := by have := (mem_Icc.mp hn).1; omega
    have hnA : n∈A := Nat.mem_factoredNumbers_of_primeFactors_subset hn0 (by
      intro p hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hn).2⟩)
    exact (Set.indicator_of_mem hnA _).symm
  calc
    _ = ∑ n∈Icc 1 N,A.indicator (lemma83XiMoebiusMass β j d r) n := he
    _ ≤ ∑' n : ℕ,A.indicator (lemma83XiMoebiusMass β j d r) n :=
      hIsum.sum_le_tsum _ (fun n _ => Set.indicator_nonneg
        (fun n _ => lemma83_xi_moebius_mass_nonneg β j d r n) n)
    _ = ∑' n : A,lemma83XiMoebiusMass β j d r n := (tsum_subtype A _).symm
    _ = ∏ p∈(Icc 1 N).filter Nat.Prime,∑' k : ℕ,lemma83XiMoebiusMass β j d r (p^k) := hEuler.2.tsum_eq
    _ ≤ _ := by
      apply prod_le_prod (fun p _ => tsum_nonneg (fun k => lemma83_xi_moebius_mass_nonneg β j d r _))
      intro p hp
      exact (lemma83_xi_moebius_local_mass β hβ j (mem_filter.mp hp).2 d r).2

noncomputable def lemma83XiRLocalMass (p r : ℕ) : ℝ :=
  if p ∣ r then (p:ℝ)/((p:ℝ)-1) else 1

lemma lemma83_xi_r_local_mass_ge_one {p : ℕ} (hp : p.Prime) (r : ℕ) :
    1 ≤ lemma83XiRLocalMass p r := by
  unfold lemma83XiRLocalMass
  split_ifs
  · have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
    apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
    linarith
  · rfl

lemma lemma83_xi_baseline_le (p d r : ℕ) (hp : p.Prime) :
    1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1) ≤
      lemma83XiRLocalMass p r*(1+4/(p:ℝ)^2) := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hrec : ((p:ℝ)-1)⁻¹ ≤ 2/(p:ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
    nlinarith
  have hsq : ((p:ℝ)-1)⁻¹^2 ≤ 4/(p:ℝ)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0≤((p:ℝ)-1)⁻¹) hrec 2
    simpa only [div_pow,show (2:ℝ)^2=4 by norm_num] using hh
  unfold lemma83XiZeroLocalTail lemma83XiRLocalMass
  split_ifs
  · have hpm : (p:ℝ)-1 ≠ 0 := by linarith
    have he : 1+1/((p:ℝ)-1)=(p:ℝ)/((p:ℝ)-1) := by
      apply (eq_div_iff hpm).mpr
      rw [add_mul,one_mul,div_mul_cancel₀ _ hpm]
      ring
    rw [he]
    have hpos : 0≤(p:ℝ)/((p:ℝ)-1) := by positivity
    exact le_mul_of_one_le_right hpos (by linarith [div_nonneg (by norm_num : (0:ℝ)≤4) (sq_nonneg (p:ℝ))])
  · simpa only [one_mul,div_eq_mul_inv,pow_two,add_comm] using add_le_add_left hsq (1:ℝ)
  · simp only [zero_div,add_zero,one_mul]
    exact le_add_of_nonneg_right (by positivity)

/-- The truncated r-prime contribution never exceeds the full totient ratio. -/
lemma lemma83_xi_r_mass_product_le (S : Finset ℕ) (hS : ∀ p∈S,p.Prime)
    (r : ℕ) (hr : 0<r) :
    (∏ p∈S,lemma83XiRLocalMass p r) ≤ (r:ℝ)/(r.totient:ℝ) := by
  have hsub : S.filter (fun p => p ∣ r) ⊆ r.primeFactors := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpS,hpr⟩
    exact Nat.mem_primeFactors.mpr ⟨hS p hpS,hpr,hr.ne'⟩
  have hfull : (∏ p∈r.primeFactors,(p:ℝ)/((p:ℝ)-1))=(r:ℝ)/(r.totient:ℝ) := by
    have hφ : (r.totient:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
    have hp0 : (∏ p∈r.primeFactors,((p:ℝ)-1)) ≠ 0 := prod_ne_zero_iff.mpr (by
      intro p hp
      have hh : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith)
    have hh : (r.totient:ℝ)*(∏ p∈r.primeFactors,(p:ℝ))=
        (r:ℝ)*(∏ p∈r.primeFactors,((p:ℝ)-1)) := by
      have hnat := Nat.totient_mul_prod_primeFactors r
      have hc := congrArg (fun x : ℕ => (x:ℝ)) hnat
      simp only [Nat.cast_mul,Nat.cast_prod] at hc
      convert hc using 1
      congr 1
      apply prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
    rw [prod_div_distrib]
    apply (div_eq_div_iff hp0 hφ).mpr
    nlinarith only [hh]
  rw [show (∏ p∈S,lemma83XiRLocalMass p r)=
      ∏ p∈S.filter (fun p => p ∣ r),(p:ℝ)/((p:ℝ)-1) by rw [prod_filter]; rfl]
  rw [←hfull]
  apply prod_le_prod_of_subset_of_one_le hsub
  · intro p hp
    have hh : (1:ℝ)<p := by exact_mod_cast (hS p (mem_filter.mp hp).1).one_lt
    positivity
  · intro p hp _
    have hh : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
    linarith

lemma lemma83_finite_reciprocal_square_sum (S : Finset ℕ) :
    (∑ n∈S,1/(n:ℝ)^2) ≤ 2 := by
  have hs : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hh := lemma83_rpow_tsum_le 1 (by norm_num)
  norm_num [Real.rpow_neg,Real.rpow_natCast,one_div] at hh
  exact (hs.sum_le_tsum S (fun n _ => by positivity)).trans (by simpa only [one_div] using hh)

/-- Quantitative finite-β μ*ξ majorant with the exact r/φ(r) dependence.
Only primes at most N enter the phase error. -/
theorem lemma83_xi_moebius_finite_harmonic_bound (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (b : ℝ) (hb : 0≤b) (hsmall : ∀ i, ‖β i‖≤b)
    (j : Fin 3) (d r N : ℕ) (hr : 0<r) :
    (∑ n∈Icc 1 N,‖lemma83XiMoebius β j d r n‖/(n:ℝ)) ≤
      ((r:ℝ)/(r.totient:ℝ))*Real.exp (8+93600000*b*Real.log 4*(2+Real.log (N:ℝ))) := by
  let S := (Icc 1 N).filter Nat.Prime
  let E : ℕ → ℝ := fun p => 93600000*b*Real.log (p:ℝ)/(p:ℝ)
  have hS (p : ℕ) (hp : p∈S) : p.Prime := (mem_filter.mp hp).2
  have hE (p : ℕ) (hp : p∈S) : 0≤E p := by
    dsimp [E]
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (hS p hp).one_le)))
      (Nat.cast_nonneg p)
  have hlocal (p : ℕ) (hp : p∈S) :
      1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1)+31200000*lemma83PrimeShiftMass β p/(p:ℝ) ≤
      lemma83XiRLocalMass p r*Real.exp (4/(p:ℝ)^2+E p) := by
    have hpP := hS p hp
    have hR := lemma83_xi_r_local_mass_ge_one hpP r
    have hbase := lemma83_xi_baseline_le p d r hpP
    have hδ : 31200000*lemma83PrimeShiftMass β p/(p:ℝ) ≤ E p := by
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (lemma83_prime_shift_mass_bound β hβ b hsmall hpP)
          (by norm_num : (0:ℝ)≤31200000)) (Nat.cast_nonneg p)
      dsimp [E]
      convert hh using 1 <;> ring
    have hle : 1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1)+31200000*lemma83PrimeShiftMass β p/(p:ℝ) ≤
        lemma83XiRLocalMass p r*(1+(4/(p:ℝ)^2+E p)) := by
      nlinarith [mul_le_mul_of_nonneg_right hR (hE p hp)]
    exact hle.trans (mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using Real.add_one_le_exp (4/(p:ℝ)^2+E p)) (by linarith))
  have hsum : (∑ p∈S,(4/(p:ℝ)^2+E p)) ≤
      8+93600000*b*Real.log 4*(2+Real.log (N:ℝ)) := by
    have hsquare := lemma83_finite_reciprocal_square_sum S
    have hlog := appendixB_prime_log_mass N
    have hlog' := mul_le_mul_of_nonneg_left hlog (by positivity : 0≤93600000*b)
    rw [sum_add_distrib]
    have hsqeq : (∑ p∈S,4/(p:ℝ)^2)=4*(∑ p∈S,1/(p:ℝ)^2) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    have hEeq : (∑ p∈S,E p)=93600000*b*(∑ p∈S,Real.log (p:ℝ)/(p:ℝ)) := by
      rw [mul_sum]; apply sum_congr rfl; intros; dsimp [E]; ring
    rw [hsqeq,hEeq]
    nlinarith only [hsquare,hlog']
  calc
    _ ≤ ∏ p∈S,(1+lemma83XiZeroLocalTail p d r/((p:ℝ)-1)+31200000*lemma83PrimeShiftMass β p/(p:ℝ)) :=
      lemma83_xi_moebius_mass_finite_euler β hβ j d r N
    _ ≤ ∏ p∈S,lemma83XiRLocalMass p r*Real.exp (4/(p:ℝ)^2+E p) := by
      apply prod_le_prod
      · intro p hp
        have hpp := hS p hp
        have hp1 : (1:ℝ)<p := by exact_mod_cast hpp.one_lt
        have htail := lemma83_xi_zero_local_tail_nonneg hpp d r
        have hmass := lemma83_prime_shift_mass_nonneg β p
        positivity
      · exact hlocal
    _ = (∏ p∈S,lemma83XiRLocalMass p r)*Real.exp (∑ p∈S,(4/(p:ℝ)^2+E p)) := by
      rw [prod_mul_distrib,Real.exp_sum]
    _ ≤ _ := mul_le_mul (lemma83_xi_r_mass_product_le S hS r hr)
      (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le (by positivity)

end ZhangLS.Spec
