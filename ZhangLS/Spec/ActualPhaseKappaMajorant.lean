import ZhangLS.Spec.Proposition71ActualKappaSeries
import ZhangLS.Spec.Lemma83RegularPerturbation
import ZhangLS.Spec.Lemma34TauProduct

/-! A finite-range tau2 majorant for the actual kappa coefficient.
The cancellation with Mobius is retained locally before taking absolute
values. This avoids a new prime-average or Mertens estimate in the R2
second/fourth coefficient moments. No moment bound is an input hypothesis.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real Classical ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

theorem actualPhase_local_h3_recursion (x y z : ℂ) (k : ℕ) :
    lemma83LocalH3 x y z (k+1) = lemma83LocalH2 x y (k+1) + z*lemma83LocalH3 x y z k := by
  unfold lemma83LocalH3 lemma83AddConvolution
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [pow_zero,mul_one,pow_succ,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Exact local Mobius cancellation is performed before applying the triangle inequality. -/
theorem actualPhase_local_kappa_cancellation (x y z : ℂ) (k : ℕ) :
    lemma83LocalKappa x y z (k+1) =
      lemma83LocalH2 x y (k+1) + (z-1)*lemma83LocalH3 x y z k := by
  rw [lemma83_local_kappa_succ,actualPhase_local_h3_recursion]
  ring

/-- A linear-in-k local majorant with an exponential small-shift correction.
The coarser existing h3 bound suffices, so no unproved sharp local count is used. -/
theorem actualPhase_local_kappa_tau_two (x y z : ℂ)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖lemma83LocalKappa x y z k‖ ≤ (k+1 : ℝ)*Real.exp ((k : ℝ)*‖z-1‖) := by
  cases k with
  | zero => simp
  | succ k =>
    rw [actualPhase_local_kappa_cancellation]
    have h2 := lemma83_local_h2_norm_bound x y hx hy (k+1)
    have h3 := lemma83_local_h3_norm_bound x y z hx hy hz k
    have he := Real.add_one_le_exp (((k : ℝ)+1)*‖z-1‖)
    have ht := norm_add_le (lemma83LocalH2 x y (k+1)) ((z-1)*lemma83LocalH3 x y z k)
    rw [norm_mul] at ht
    have hh := mul_le_mul_of_nonneg_left h3 (norm_nonneg (z-1))
    push_cast at h2 ⊢
    calc
      _ ≤ (k+2 : ℝ)+‖z-1‖*(k+1 : ℝ)^2 := by linarith only [ht,h2,hh]
      _ ≤ (k+2 : ℝ)*(1+(k+1 : ℝ)*‖z-1‖) := by
        nlinarith only [norm_nonneg (z-1),Nat.cast_nonneg (α := ℝ) k]
      _ ≤ (k+2 : ℝ)*Real.exp ((k+1 : ℝ)*‖z-1‖) :=
        mul_le_mul_of_nonneg_left (by linarith only [he]) (by positivity)
      _ = _ := by ring

theorem actualPhase_kappa_prime_power_tau_two (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖lemma83Kappa β (p^k)‖ ≤ (lemma34Tau 2 (p^k) : ℝ)*
      Real.exp ((k : ℝ)*(‖β 2‖*Real.log (p : ℝ))) := by
  have hd : ‖(p : ℂ)^(-β 2)-1‖ ≤ ‖β 2‖*Real.log (p : ℝ) := by
    rw [norm_sub_rev,←lemma32_prime_monomial_eq_cpow hp.pos]
    exact lemma83_shift_monomial_sub_one_bound hp.pos (β 2) (hβ 2)
  rw [lemma83_kappa_prime_power β hp,lemma34_tau_prime_power hp 1 k,Nat.multichoose_two]
  push_cast
  apply (actualPhase_local_kappa_tau_two _ _ _
    (lemma83_cpow_shift_norm hp.pos _ (hβ 0)).le
    (lemma83_cpow_shift_norm hp.pos _ (hβ 1)).le
    (lemma83_cpow_shift_norm hp.pos _ (hβ 2)).le k).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg k))

/-- The actual multiplicative coefficient is bounded by tau2 times n to
the size of one shift. No squarefree restriction is present. -/
theorem actualPhase_kappa_tau_two_global (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) {n : ℕ} (hn : n ≠ 0) :
    ‖lemma83Kappa β n‖ ≤ (lemma34Tau 2 n : ℝ)*Real.exp (‖β 2‖*Real.log (n : ℝ)) := by
  have hk := (lemma83_kappa_multiplicative β).multiplicative_factorization (lemma83Kappa β) hn
  have ht := (lemma34_tau_multiplicative 2).multiplicative_factorization
    (ArithmeticFunction.zeta^2) hn
  simp only [Finsupp.prod] at hk ht
  have hτ : (lemma34Tau 2 n : ℝ) =
      ∏ p ∈ n.primeFactors, (lemma34Tau 2 (p^n.factorization p) : ℝ) := by
    exact_mod_cast ht
  have hl : Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ)*Real.log (p : ℝ) := by
    simpa only [Finsupp.sum] using Real.log_nat_eq_sum_factorization n
  rw [hk,norm_prod,hτ]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (lemma34Tau 2 (p^n.factorization p) : ℝ)*
        Real.exp ((n.factorization p : ℝ)*(‖β 2‖*Real.log (p : ℝ))) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      exact actualPhase_kappa_prime_power_tau_two β hβ (Nat.prime_of_mem_primeFactors hp) _
    _ = _ := by
      rw [Finset.prod_mul_distrib,←Real.exp_sum,hl,Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Finite-range form used before the actual large sieve. The size bound
is derived from the actual coefficient rather than taken as a moment premise. -/
theorem actualPhase_kappa_tau_two_finite (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) {X B : ℝ} (hX : 0 < X)
    (hB : ‖β 2‖*Real.log X ≤ B) {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ X) :
    ‖lemma83Kappa β n‖ ≤ Real.exp B*(lemma34Tau 2 n : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log hnp hnX) (norm_nonneg (β 2))
  apply (actualPhase_kappa_tau_two_global β hβ hn.ne').trans
  calc
    _ ≤ (lemma34Tau 2 n : ℝ)*Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hl.trans hB)) (Nat.cast_nonneg _)
    _ = _ := by ring


theorem actualPhase_paper_kappa_tau_two {D : ℕ} {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (n : ℕ) (hn : (n : ℝ) ≤ lemma23PaperP D^2) :
    ‖(lemma83Kappa (lemma83PaperBeta D c)) n‖ ≤ Real.exp (6*Real.pi)*(lemma34Tau 2 n : ℝ) := by
  by_cases hn0 : n = 0
  · subst n
    simp [lemma34Tau]
  have hLp : 0 < lemma23PaperL D := by linarith
  have ho := (lemma52_offset_bounds hL hc hsmall).2.2
  have hb : ‖lemma83PaperBeta D c 2‖ ≤ 3*lemma44PaperAlpha D := by
    simpa only [lemma83PaperBeta,show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide,if_false,lemma52PaperBetaThree,
      norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho.1] using ho.2
  have ha : lemma44PaperAlpha D*lemma23PaperL D^9 = Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    exact div_mul_cancel₀ _ (pow_ne_zero 9 hLp.ne')
  have hbudget : ‖lemma83PaperBeta D c 2‖*Real.log (lemma23PaperP D^2) ≤ 6*Real.pi := by
    rw [Real.log_pow,lemma23PaperP,Real.log_exp]
    have hh := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2*lemma23PaperL D^9)
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hh,ha]
  exact actualPhase_kappa_tau_two_finite _ (lemma83_beta_re D c)
    (pow_pos (Real.exp_pos _) 2) hbudget (Nat.pos_of_ne_zero hn0) hn

/-- The fixed constant precedes the modulus, character and coefficients.
The original three shifts are used literally. -/
theorem actualPhase_uniform_paper_kappa_tau_two {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧
      ∀ D : ℕ, N ≤ D → ∀ n : ℕ, (n : ℝ) ≤ lemma23PaperP D^2 →
        ‖(lemma83Kappa (lemma83PaperBeta D c)) n‖ ≤ Real.exp (6*Real.pi)*(lemma34Tau 2 n : ℝ) := by
  obtain ⟨N,hN,hs⟩ := lemma52_exists_shift_threshold hc
  refine ⟨N,hN,?_⟩
  intro D hD n hn
  exact actualPhase_paper_kappa_tau_two
    (lemma44_parameters_at_explicit_threshold (hN.trans hD)).1 hc (hs D hD) n hn

/-- Genuine second coefficient energy with exponent four in log X,
hence L^36 at the original P^2 range. -/
theorem actualPhase_paper_kappa_second_energy {D : ℕ} {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (X : ℕ) (hX : 1 ≤ X) (hXP : (X : ℝ) ≤ lemma23PaperP D^2) :
    (∑ n ∈ Finset.Icc 1 X, ‖(lemma83Kappa (lemma83PaperBeta D c)) n‖^2/(n : ℝ)) ≤
      (Real.exp (6*Real.pi))^2*(1+Real.log (X : ℝ))^4 := by
  have hh := lemma34_tau_majorized_coefficient_harmonic_energy 2 X (by norm_num) hX
    (Real.exp (6*Real.pi)) (Real.exp_nonneg _) ((lemma83Kappa (lemma83PaperBeta D c)))
    (fun n hn => actualPhase_paper_kappa_tau_two hL hc hsmall n
      ((show (n : ℝ) ≤ X by exact_mod_cast (Finset.mem_Icc.mp hn).2).trans hXP))
  simpa only [show (2 : ℕ)*2 = 4 by norm_num] using hh


/-- The strict hard truncation as an actual arithmetic function. -/
noncomputable def actualPhaseTruncatedKappa (D : ℕ) (c R : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if (n : ℝ) < R then (lemma83Kappa (lemma83PaperBeta D c)) n else 0, by simp⟩

/-- The strict finite endpoint is excluded, including when R is an integer. -/
theorem actualPhase_truncated_kappa_source_endpoint (D : ℕ) (c R : ℝ)
    (n : ℕ) (hn : R ≤ (n : ℝ)) : actualPhaseTruncatedKappa D c R n = 0 := by
  simp [actualPhaseTruncatedKappa,not_lt.mpr hn]

/-- Below the cutoff the coefficient is the literal source kappa with all
three original shifts, without a continued-product substitution. -/
theorem actualPhase_truncated_kappa_source_coefficient (D : ℕ) (c R : ℝ)
    (n : ℕ) (hn : (n : ℝ) < R) : actualPhaseTruncatedKappa D c R n =
      (lemma83Kappa (lemma83PaperBeta D c)) n := by
  simp [actualPhaseTruncatedKappa,hn]

theorem actualPhase_truncated_kappa_tau_two {D : ℕ} {c R : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (hR : R ≤ lemma23PaperP D^2) (n : ℕ) :
    ‖actualPhaseTruncatedKappa D c R n‖ ≤ Real.exp (6*Real.pi)*(lemma34Tau 2 n : ℝ) := by
  unfold actualPhaseTruncatedKappa
  simp only [ArithmeticFunction.coe_mk]
  split_ifs with hn
  · exact actualPhase_paper_kappa_tau_two hL hc hsmall n (hn.le.trans hR)
  · simp only [norm_zero]
    positivity

/-- A genuine hard-truncated square is majorized after taking absolute
values. Removed complex cancellation is never restored. -/
theorem actualPhase_truncated_square_tau_four {D : ℕ} {c R : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (hR : R ≤ lemma23PaperP D^2) (n : ℕ) :
    ‖(actualPhaseTruncatedKappa D c R * actualPhaseTruncatedKappa D c R) n‖ ≤
      (Real.exp (6*Real.pi))^2*(lemma34Tau 4 n : ℝ) := by
  have hh := proposition71_convolution_majorant
    (actualPhaseTruncatedKappa D c R) (actualPhaseTruncatedKappa D c R)
    (ArithmeticFunction.zeta^2) (ArithmeticFunction.zeta^2)
    (Real.exp_nonneg (6*Real.pi)) (Real.exp_nonneg (6*Real.pi))
    (fun m => actualPhase_truncated_kappa_tau_two hL hc hsmall hR m)
    (fun m => actualPhase_truncated_kappa_tau_two hL hc hsmall hR m) n
  have hprod : (ArithmeticFunction.zeta : ArithmeticFunction ℕ)^2 *
      ArithmeticFunction.zeta^2 = ArithmeticFunction.zeta^4 :=
    (pow_add (ArithmeticFunction.zeta : ArithmeticFunction ℕ) 2 2).symm
  rw [hprod] at hh
  simpa only [pow_two,lemma34Tau] using hh

/-- Fourth-moment coefficient energy: log exponent sixteen, not four.
The required square-length condition for applying the large sieve is a
separate support obligation and is not suppressed by this coefficient lemma. -/
theorem actualPhase_truncated_square_energy {D : ℕ} {c R : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (hR : R ≤ lemma23PaperP D^2) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
      ‖(actualPhaseTruncatedKappa D c R * actualPhaseTruncatedKappa D c R) n‖^2/(n : ℝ)) ≤
      (Real.exp (6*Real.pi))^4*(1+Real.log (X : ℝ))^16 := by
  have hh := lemma34_tau_majorized_coefficient_harmonic_energy 4 X (by norm_num) hX
    ((Real.exp (6*Real.pi))^2) (sq_nonneg _) _
    (fun n _ => actualPhase_truncated_square_tau_four hL hc hsmall hR n)
  convert hh using 1 <;> ring


theorem actualPhase_log_prefix_power_budget {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) (X k : ℕ) (hX : 1 ≤ X)
    (hXP : (X : ℝ) ≤ lemma23PaperP D^2) :
    (1+Real.log (X : ℝ))^k ≤ (3 : ℝ)^k*lemma23PaperL D^(9*k) := by
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hl := Real.log_le_log hXp hXP
  rw [Real.log_pow,lemma23PaperP,Real.log_exp] at hl
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL9 : 1 ≤ lemma23PaperL D^9 := one_le_pow₀ hL1
  have hb : 1+Real.log (X : ℝ) ≤ 3*lemma23PaperL D^9 := by
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl,hL9]
  have hnonneg : 0 ≤ 1+Real.log (X : ℝ) := by linarith only [Real.log_nonneg hX1]
  apply (pow_le_pow_left₀ hnonneg hb k).trans_eq
  rw [mul_pow,←pow_mul]

theorem actualPhase_paper_kappa_second_L36 {D : ℕ} {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (X : ℕ) (hX : 1 ≤ X) (hXP : (X : ℝ) ≤ lemma23PaperP D^2) :
    (∑ n ∈ Finset.Icc 1 X, ‖(lemma83Kappa (lemma83PaperBeta D c)) n‖^2/(n : ℝ)) ≤
      (81*(Real.exp (6*Real.pi))^2)*lemma23PaperL D^36 := by
  have hh := actualPhase_paper_kappa_second_energy hL hc hsmall X hX hXP
  have hb := actualPhase_log_prefix_power_budget hL X 4 hX hXP
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.exp (6*Real.pi)))).trans_eq
  norm_num <;> ring

theorem actualPhase_truncated_square_L144 {D : ℕ} {c R : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (hR : R ≤ lemma23PaperP D^2) (X : ℕ) (hX : 1 ≤ X)
    (hXP : (X : ℝ) ≤ lemma23PaperP D^2) :
    (∑ n ∈ Finset.Icc 1 X,
      ‖(actualPhaseTruncatedKappa D c R * actualPhaseTruncatedKappa D c R) n‖^2/(n : ℝ)) ≤
      (43046721*(Real.exp (6*Real.pi))^4)*lemma23PaperL D^144 := by
  have hh := actualPhase_truncated_square_energy hL hc hsmall hR X hX
  have hb := actualPhase_log_prefix_power_budget hL X 16 hX hXP
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (Real.exp (6*Real.pi))^4)).trans_eq
  norm_num <;> ring

end ZhangLS.Spec
