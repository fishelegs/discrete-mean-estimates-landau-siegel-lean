import ZhangLS.Spec.AppendixBRoughPrimeLog
import ZhangLS.Spec.RoughCollisionRegressions
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The actual rho coefficients, all prime powers and p=2 retained. The local
factor is exactly 1+|rho(p)|/(p-1); there is no nonuniform O(p^-2) term. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def appendixBRhoMass (β : ℂ) (n : ℕ) : ℝ := ‖lemma151Rho β n‖/(n : ℝ)

@[simp] lemma appendixB_rho_mass_zero (β : ℂ) : appendixBRhoMass β 0=0 := by
  simp [appendixBRhoMass]

@[simp] lemma appendixB_rho_mass_one (β : ℂ) : appendixBRhoMass β 1=1 := by
  simp [appendixBRhoMass,(roughCollision_rho_multiplicative β).map_one]

lemma appendixB_rho_mass_nonneg (β : ℂ) (n : ℕ) : 0≤appendixBRhoMass β n := by
  unfold appendixBRhoMass; positivity

lemma appendixB_rho_mass_mul (β : ℂ) {m n : ℕ} (h : m.Coprime n) :
    appendixBRhoMass β (m*n)=appendixBRhoMass β m*appendixBRhoMass β n := by
  simp only [appendixBRhoMass,(roughCollision_rho_multiplicative β).map_mul_of_coprime h,
    norm_mul,Nat.cast_mul]
  ring

/-- Every positive prime power has the same actual rho coefficient. -/
@[simp] theorem appendixB_rho_prime_power (β : ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    lemma151Rho β (p^(k+1))=1-(p : ℂ)^β := by
  induction k with
  | zero => simpa using roughCollision_rho_prime_exact β hp
  | succ k ih =>
    rw [lemma151_rho_divisor_sum,Nat.sum_divisors_prime_pow hp,sum_range_succ]
    have he : (∑ d∈range (k+1+1),
        (ArithmeticFunction.moebius (p^d) : ℂ)*((p^d : ℕ) : ℂ)^β)=1-(p : ℂ)^β := by
      simpa only [lemma151_rho_divisor_sum,Nat.sum_divisors_prime_pow hp] using ih
    rw [he,ArithmeticFunction.moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
    simp

/-- The local phase is controlled by the actual finite-D beta, without replacing
it by its limiting phase. -/
theorem appendixB_rho_prime_norm {β : ℂ} (hβ : β.re=0) {p : ℕ} (hp : p.Prime) :
    ‖lemma151Rho β p‖≤‖β‖*Real.log (p : ℝ) := by
  have hp0 : (0 : ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hlog : 0≤Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have he : (p : ℂ)^β=exp (I*((β.im*Real.log (p : ℝ) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero)]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_log hp0.le]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,hβ,mul_comm]
  rw [roughCollision_rho_prime_exact β hp,he,norm_sub_rev]
  calc
    _ ≤ |β.im*Real.log (p : ℝ)| := by simpa [Real.norm_eq_abs] using
      Real.norm_exp_I_mul_ofReal_sub_one_le (x := β.im*Real.log (p : ℝ))
    _ = |β.im| * Real.log (p : ℝ) := by rw [abs_mul,abs_of_nonneg hlog]
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_im_le_norm β) hlog

/-- Actual finite prime-factor formula, valid also at n=1 by the empty product. -/
theorem appendixB_rho_prime_factorization (β : ℂ) {n : ℕ} (hn : n≠0) :
    lemma151Rho β n=∏ p∈n.primeFactors,(1-(p : ℂ)^β) := by
  rw [(roughCollision_rho_multiplicative β).multiplicative_factorization _ hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl
  intro p hp
  have he := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
    (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  rw [hk]
  exact appendixB_rho_prime_power β (Nat.prime_of_mem_primeFactors hp) k

/-- Distinct-prime logarithms are at most log n; multiplicities are kept in the
factorization identity, rather than assuming squarefreeness. -/
lemma appendixB_prime_factor_log_sum {n : ℕ} (hn : n≠0) :
    (∑ p∈n.primeFactors,Real.log (p : ℝ))≤Real.log (n : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p∈n.primeFactors,Real.log (p : ℝ))≤
    ∑ p∈n.primeFactors,(n.factorization p : ℝ)*Real.log (p : ℝ)
  apply sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have he := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  exact le_mul_of_one_le_left (Real.log_nonneg (by exact_mod_cast hprime.one_le))
    (by exact_mod_cast (show 1≤n.factorization p from he))

/-- A scale-sensitive pointwise bound useful for the strict sqrt(P) tail.
This does not replace the global absolute mass estimate used for B.2. -/
theorem appendixB_rho_norm_exp_log {β : ℂ} (hβ : β.re=0) {n : ℕ} (hn : n≠0) :
    ‖lemma151Rho β n‖≤Real.exp (‖β‖*Real.log (n : ℝ)) := by
  rw [appendixB_rho_prime_factorization β hn,norm_prod]
  calc
    _ ≤ ∏ p∈n.primeFactors,Real.exp (‖β‖*Real.log (p : ℝ)) := by
      apply prod_le_prod (fun p _ => norm_nonneg _)
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hb := appendixB_rho_prime_norm hβ hprime
      rw [roughCollision_rho_prime_exact β hprime] at hb
      exact hb.trans ((by linarith : ‖β‖*Real.log (p : ℝ)≤‖β‖*Real.log (p : ℝ)+1).trans
        (Real.add_one_le_exp _))
    _ = Real.exp (‖β‖*(∑ p∈n.primeFactors,Real.log (p : ℝ))) := by
      rw [mul_sum,Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (appendixB_prime_factor_log_sum hn) (norm_nonneg β))

/-- A global polynomial majorant, including the zero convention, useful past P
when controlling the remote Gaussian tail. -/
theorem appendixB_rho_norm_le_index {β : ℂ} (hβre : β.re=0)
    (hβ : ‖β‖≤1) (n : ℕ) : ‖lemma151Rho β n‖≤(n : ℝ) := by
  by_cases hn : n=0
  · simp [hn]
  have hnp : 0<(n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog : 0≤Real.log (n : ℝ) := Real.log_natCast_nonneg n
  calc
    _ ≤ Real.exp (‖β‖*Real.log (n : ℝ)) := appendixB_rho_norm_exp_log hβre hn
    _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hβ hlog)
    _ = _ := Real.exp_log hnp

lemma appendixB_rho_local_tail (β : ℂ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => appendixBRhoMass β (p^(k+1))) ∧
      (∑' k : ℕ, appendixBRhoMass β (p^(k+1)))=‖lemma151Rho β p‖/((p : ℝ)-1) := by
  have hp1 : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ)≠0 := by positivity
  have hr : (p : ℝ)⁻¹<1 := (inv_lt_one₀ (by positivity)).mpr hp1
  have he (k : ℕ) : appendixBRhoMass β (p^(k+1))=
      (‖lemma151Rho β p‖*(p : ℝ)⁻¹)*((p : ℝ)⁻¹)^k := by
    unfold appendixBRhoMass
    rw [appendixB_rho_prime_power β hp k,roughCollision_rho_prime_exact β hp,
      Nat.cast_pow,div_eq_mul_inv,inv_pow,pow_succ]
    ring
  have hs := (summable_geometric_of_lt_one (by positivity : 0≤(p : ℝ)⁻¹) hr).mul_left
    (‖lemma151Rho β p‖*(p : ℝ)⁻¹)
  refine ⟨by simpa only [he] using hs,?_⟩
  simp_rw [he]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by positivity) hr]
  have hp1ne : (p : ℝ)-1≠0 := sub_ne_zero.mpr hp1.ne'
  field_simp [hp0,hp1ne]
  <;> ring

lemma appendixB_rho_local_series (β : ℂ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => appendixBRhoMass β (p^k)) ∧
      (∑' k : ℕ, appendixBRhoMass β (p^k))=1+‖lemma151Rho β p‖/((p : ℝ)-1) := by
  have ht := appendixB_rho_local_tail β hp
  have hs : Summable (fun k : ℕ => appendixBRhoMass β (p^k)) :=
    (summable_nat_add_iff 1).mp ht.1
  refine ⟨hs,?_⟩
  rw [hs.tsum_eq_zero_add,ht.2]
  simp

/-- A finite sum of actual rho masses is bounded by its genuine finite Euler
product, including the complete geometric tail at every prime. -/
theorem appendixB_rho_mass_euler (β : ℂ) (N : ℕ) :
    (∑ n∈Icc 1 N, appendixBRhoMass β n)≤
      ∏ p∈(Icc 1 N).filter Nat.Prime, (1+‖lemma151Rho β p‖/((p : ℝ)-1)) := by
  let A : Set ℕ := Nat.factoredNumbers (Icc 1 N)
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖appendixBRhoMass β (p^k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs,abs_of_nonneg (appendixB_rho_mass_nonneg β _)] using
      (appendixB_rho_local_series β hp).1
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (appendixB_rho_mass_one β) (appendixB_rho_mass_mul β) hlocal (Icc 1 N)
  have hAsum : Summable (fun n : A => appendixBRhoMass β n.val) := hEuler.2.summable
  have hIsum : Summable (A.indicator (appendixBRhoMass β)) :=
    summable_subtype_iff_indicator.mp hAsum
  have he : (∑ n∈Icc 1 N,appendixBRhoMass β n)=
      ∑ n∈Icc 1 N,A.indicator (appendixBRhoMass β) n := by
    apply sum_congr rfl
    intro n hn
    have hn0 : n≠0 := by have := (mem_Icc.mp hn).1; omega
    have hnA : n∈A := Nat.mem_factoredNumbers_of_primeFactors_subset hn0 (by
      intro p hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hn).2⟩)
    exact (Set.indicator_of_mem hnA _).symm
  calc
    _ = ∑ n∈Icc 1 N,A.indicator (appendixBRhoMass β) n := he
    _ ≤ ∑' n : ℕ,A.indicator (appendixBRhoMass β) n :=
      hIsum.sum_le_tsum _ (fun n _ => Set.indicator_nonneg (fun n _ => appendixB_rho_mass_nonneg β n) n)
    _ = ∑' n : A,appendixBRhoMass β n := (tsum_subtype A _).symm
    _ = ∏ p∈(Icc 1 N).filter Nat.Prime,∑' k : ℕ,appendixBRhoMass β (p^k) := hEuler.2.tsum_eq
    _ = _ := prod_congr rfl (fun p hp => (appendixB_rho_local_series β (mem_filter.mp hp).2).2)

/-- The factor p/(p-1) is at most 2, including equality at p=2. -/
lemma appendixB_rho_local_excess {β : ℂ} (hβ : β.re=0) {p : ℕ} (hp : p.Prime) :
    ‖lemma151Rho β p‖/((p : ℝ)-1)≤2*‖β‖*Real.log (p : ℝ)/(p : ℝ) := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ)<p := by positivity
  have hpm : 0<(p : ℝ)-1 := by linarith
  calc
    _ ≤ (‖β‖*Real.log (p : ℝ))/((p : ℝ)-1) :=
      div_le_div_of_nonneg_right (appendixB_rho_prime_norm hβ hp) hpm.le
    _ ≤ _ := by
      apply (div_le_div_iff₀ hpm hp0).mpr
      have hpos : 0≤‖β‖*Real.log (p : ℝ) := mul_nonneg (norm_nonneg _) (Real.log_nonneg (by linarith))
      nlinarith

/-- Uniform global absolute Euler-product control with only one logarithm.
No assumption (A), character coprimality or omission of ramified primes occurs. -/
theorem appendixB_rho_mass_exp_bound {β : ℂ} (hβ : β.re=0) (N : ℕ) :
    (∑ n∈Icc 1 N,appendixBRhoMass β n)≤
      Real.exp (2*‖β‖*Real.log 4*(2+Real.log (N : ℝ))) := by
  have hu : ∀ p : ℕ, 0≤2*‖β‖*Real.log (p : ℝ)/(p : ℝ) := by
    intro p
    by_cases hp : p=0
    · simp [hp]
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp))) (Nat.cast_nonneg p)
  calc
    _ ≤ ∏ p∈(Icc 1 N).filter Nat.Prime,(1+‖lemma151Rho β p‖/((p : ℝ)-1)) := appendixB_rho_mass_euler β N
    _ ≤ ∏ p∈(Icc 1 N).filter Nat.Prime,(1+2*‖β‖*Real.log (p : ℝ)/(p : ℝ)) := by
      apply prod_le_prod
      · intro p hp
        have hp1 : (1 : ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
        positivity
      · intro p hp
        exact add_le_add le_rfl (appendixB_rho_local_excess hβ (mem_filter.mp hp).2)
    _ ≤ Real.exp (∑ p∈(Icc 1 N).filter Nat.Prime,2*‖β‖*Real.log (p : ℝ)/(p : ℝ)) :=
      Real.prod_one_add_le_exp_sum _ hu
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have he : (∑ p∈(Icc 1 N).filter Nat.Prime,2*‖β‖*Real.log (p : ℝ)/(p : ℝ))=
          2*‖β‖*(∑ p∈(Icc 1 N).filter Nat.Prime,Real.log (p : ℝ)/(p : ℝ)) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      rw [he,mul_assoc (2*‖β‖)]
      exact mul_le_mul_of_nonneg_left (appendixB_prime_log_mass N) (by positivity)

end ZhangLS.Spec
