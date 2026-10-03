import ZhangLS.Spec.Lemma153ActualDirichletSeries

/-! Sharp first-prime and quadratic local absolute budgets for the genuine
Section 15 coefficient A(n)=chi(n)*tau2(n)*varpi(n). These estimates retain
all original shifts, include p=2, and explicitly remove ramified coefficients.
They do not assert a pointwise global tau4 majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma actual151_local_chi_varpi_at_prime (B C E F lam t : ℂ) :
    lemma153LocalChiVarpi B C E F lam t 1 = C/B + (lam*E/B)*t := by
  have hH : lemma83LocalH2 1 t 1 = 1+t := by
    unfold lemma83LocalH2 lemma83AddConvolution
    rw [show 1=0+1 by norm_num,Finset.Nat.sum_antidiagonal_succ]
    simp [add_comm]
  simp [lemma153LocalChiVarpi,hH]

lemma actual151_local_weighted_prime_norm (B C E F lam t : ℂ) (u : ℝ)
    (ht : ‖t‖≤1) (hC : ‖C/B-1‖≤10000*u)
    (hE : ‖lam*E/B-1‖≤10000*u) :
    ‖2*lemma153LocalChiVarpi B C E F lam t 1‖≤4+40000*u := by
  have hC' : ‖C/B‖≤1+10000*u := by
    have hh := norm_le_norm_sub_add (C/B) (1:ℂ)
    rw [norm_one] at hh
    linarith
  have hE' : ‖lam*E/B‖≤1+10000*u := by
    have hh := norm_le_norm_sub_add (lam*E/B) (1:ℂ)
    rw [norm_one] at hh
    linarith
  have hEt : ‖(lam*E/B)*t‖≤‖lam*E/B‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ht
  rw [actual151_local_chi_varpi_at_prime,norm_mul]
  norm_num only [norm_ofNat]
  have hh := norm_add_le (C/B) ((lam*E/B)*t)
  nlinarith only [hh,hC',hE',hEt]

/-- The coefficient of p has leading bound 4, with a summable prime correction
only after the external p^-sigma weight is inserted. -/
theorem actual151_weighted_prime_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (q : Nat.Primes) :
    ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) q.val‖≤
      4+40000/(q.val : ℝ) := by
  by_cases hqd : q.val∣D
  · have hz := lemma153_coefficient_ramified_prime_power χ β γ
      (lemma153GeneralMEulerProduct χ β) q.property hqd 0
    simp only [zero_add,pow_one] at hz
    rw [hz,norm_zero]
    positivity
  let B := lemma153Baseline χ β γ q
  let lam := lemma152LambdaFactor χ β q.val 1
  let A := χ.evalNat q.val/(1-(q.val:ℂ)⁻¹)
  let y := lemma32PrimeMonomial q.val (1-γ)
  let K := lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) y
  have hr := lemma153_actual_local_ratio_bounds χ β γ hpar q
  have ht : ‖χ.evalNat q.val*(q.val:ℂ)^γ‖≤1 := by
    have hw : ‖(q.val:ℂ)^γ‖=1 := by
      simpa using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hpar.gamma_re])
    simpa only [norm_mul,hw,mul_one] using χ.evalNat_norm_le_one q.val
  have hn := actual151_local_weighted_prime_norm B (B+lam*A*y*K) ((1-A*y)*K) K lam
    (χ.evalNat q.val*(q.val:ℂ)^γ) ‖(q.val:ℂ)⁻¹‖ ht hr.2.1 hr.2.2.1
  have he := lemma153_actual_unramified_chi_varpi χ β hpar.beta_re γ hpar.gamma_re q hqd hM 1
  simp only [pow_one] at he
  have htau : lemma34Tau 2 q.val=2 := by
    simpa only [pow_one] using lemma153_tau_two_prime_power q.property 1
  have hcoeff : lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) q.val =
      2*lemma153LocalChiVarpi B (B+lam*A*y*K) ((1-A*y)*K) K lam
        (χ.evalNat q.val*(q.val:ℂ)^γ) 1 := by
    unfold lemma153Coefficient
    rw [htau]
    push_cast
    calc
      _ = 2*(χ.evalNat q.val*
        lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) q.val) := by ring
      _ = _ := by rw [he]
  rw [hcoeff]
  simpa only [norm_inv,Complex.norm_natCast,div_eq_mul_inv] using hn

/-- A fixed absolute constant for the positive-degree tail starting at p². -/
noncomputable def actual151WeightedPrimeTailConstant : ℝ :=
  ∑' n : ℕ,(50000:ℝ)*((n:ℝ)+3)^2*(1/2:ℝ)^n

lemma actual151_weighted_prime_tail_majorant_summable :
    Summable (fun n : ℕ => (50000:ℝ)*((n:ℝ)+3)^2*(1/2:ℝ)^n) := by
  have hg := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2:ℝ)‖<1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1/2:ℝ)‖<1)
  convert (h2.mul_left 50000).add ((h1.mul_left 300000).add (hg.mul_left 450000)) using 1
  funext n
  ring

lemma actual151_weighted_prime_tail_constant_nonneg :
    0≤actual151WeightedPrimeTailConstant := tsum_nonneg (fun _ => by positivity)

/-- A quadratic, rather than linear, absolute local tail. -/
theorem actual151_weighted_prime_power_tail {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (q : Nat.Primes)
    (z : ℂ) (hz : ‖z‖≤1/2) :
    Summable (fun n : ℕ =>
      ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+2))*z^(n+2)‖) ∧
    (∑' n : ℕ,
      ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+2))*z^(n+2)‖)≤
      actual151WeightedPrimeTailConstant*‖z‖^2 := by
  have hm := actual151_weighted_prime_tail_majorant_summable.mul_left (‖z‖^2)
  have hbound (n : ℕ) :
      ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+2))*z^(n+2)‖≤
        ‖z‖^2*((50000:ℝ)*((n:ℝ)+3)^2*(1/2:ℝ)^n) := by
    have hn := lemma153_actual_prime_power_norm χ β γ hpar hM q (n+1)
    have hn' : ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+2))‖≤
        50000*((n:ℝ)+3)^2 := by
      convert hn using 1 <;> push_cast <;> ring
    have hp := pow_le_pow_left₀ (norm_nonneg _) hz n
    rw [norm_mul,norm_pow,pow_add ‖z‖]
    calc
      _ ≤ (50000*((n:ℝ)+3)^2)*((1/2:ℝ)^n*‖z‖^2) := by gcongr
      _ = _ := by ring
  have hs := hm.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  refine ⟨hs,?_⟩
  have hb := hs.tsum_le_tsum hbound hm
  rw [tsum_mul_left] at hb
  simpa only [actual151WeightedPrimeTailConstant,mul_comm] using hb

/-- Exact leading coefficient and a uniform quadratic remainder in the
absolute local Dirichlet series; all beta/gamma dependence is retained. -/
theorem actual151_weighted_local_norm_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (q : Nat.Primes)
    (z : ℂ) (hz : ‖z‖≤1/2) :
    (∑' n : ℕ,
      ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*z^n‖)≤
      1+4*‖z‖+40000*‖z‖/(q.val : ℝ)+actual151WeightedPrimeTailConstant*‖z‖^2 := by
  let f : ℕ→ℝ := fun n =>
    ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*z^n‖
  have hs : Summable f := (lemma153_actual_local_norm_series χ β γ hpar hM q z hz).1
  have hs1 : Summable (fun n : ℕ => f (n+1)) := (summable_nat_add_iff 1).mpr hs
  have h0 : f 0=1 := by
    simp only [f,pow_zero,lemma153_coefficient_one χ β γ
      (lemma153GeneralMEulerProduct χ β) (by simpa using hM),mul_one,norm_one]
  have h1 : f 1≤(4+40000/(q.val : ℝ))*‖z‖ := by
    simp only [f,pow_one,norm_mul]
    exact mul_le_mul_of_nonneg_right (actual151_weighted_prime_norm χ β γ hpar hM q) (norm_nonneg _)
  have htail : (∑' n : ℕ,f (n+1+1))≤actual151WeightedPrimeTailConstant*‖z‖^2 := by
    simpa only [f,Nat.add_assoc] using (actual151_weighted_prime_power_tail χ β γ hpar hM q z hz).2
  change (∑' n : ℕ,f n)≤_
  rw [hs.tsum_eq_zero_add,hs1.tsum_eq_zero_add,h0]
  calc
    _ ≤ 1+((4+40000/(q.val : ℝ))*‖z‖+actual151WeightedPrimeTailConstant*‖z‖^2) := by
      gcongr
    _ = _ := by ring

end ZhangLS.Spec
