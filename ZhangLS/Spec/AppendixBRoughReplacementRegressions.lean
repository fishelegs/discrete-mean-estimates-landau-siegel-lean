import ZhangLS.Spec.AppendixBRoughKernelReplacement

/-! Expanded source-object and endpoint regressions. No full Lemma 15.1 result
is asserted: strict sqrt(P) tail, product reindex and outer n1 weights remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

@[simp] theorem appendixB_regression_rho_one (β : ℂ) : lemma151Rho β 1=1 :=
  (roughCollision_rho_multiplicative β).map_one

@[simp] theorem appendixB_regression_two_power (β : ℂ) (k : ℕ) :
    lemma151Rho β (2^(k+1))=1-(2 : ℂ)^β :=
  appendixB_rho_prime_power β Nat.prime_two k

/-- The q=2 Euler factor is retained exactly; its denominator p-1 is one. -/
theorem appendixB_regression_two_euler_factor (β : ℂ) :
    (∑' k : ℕ,appendixBRhoMass β (2^k))=1+‖1-(2 : ℂ)^β‖ := by
  rw [(appendixB_rho_local_series β Nat.prime_two).2,roughCollision_rho_prime_exact β Nat.prime_two]
  norm_num

/-- Ramification is not a hypothesis in either the local series or global mass.
This specialization explicitly keeps a ramified prime in the Euler factor. -/
theorem appendixB_regression_ramified_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (_hpd : p∣D) :
    (∑' k : ℕ,appendixBRhoMass β (p^k))=1+‖1-(p : ℂ)^β‖/((p : ℝ)-1) := by
  rw [(appendixB_rho_local_series β hp).2,roughCollision_rho_prime_exact β hp]

/-- Closed endpoint D^4 cannot be a nontrivial rough integer. -/
theorem appendixB_regression_fourth_endpoint {D : ℕ} (hD : 1<D) :
    ¬(D^4).Coprime (lemma151Q D) := by
  intro h
  have hh : 1<D^4 := one_lt_pow₀ hD (by decide : (4 : ℕ)≠0)
  have hgt := appendixB_rough_gt_fourth hh h
  omega

/-- The global bound includes the closed n=P endpoint when P is integral. -/
theorem appendixB_regression_closed_P {D N : ℕ} {β : ℂ}
    (hL : 1≤lemma23PaperL D) (hN : 1≤N) (hNP : (N : ℝ)=lemma23PaperP D)
    (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) :
    (∑ n∈Icc 1 N,‖lemma151Rho β n‖/(n : ℝ))≤Real.exp (18*Real.pi*Real.log 4) :=
  appendixB_original_rho_mass hL hN hNP.le hβre hβ

/-- Strict source sums are genuine finite restrictions of the proved closed bound. -/
theorem appendixB_regression_strict_B2 {D N : ℕ} {β : ℂ}
    (hL : 1≤lemma23PaperL D) (hN : 1≤N) (hNP : (N : ℝ)≤lemma23PaperP D)
    (hβre : β.re=0) (hβ : ‖β‖≤3*lemma44PaperAlpha D) :
    (∑ n∈(Icc 1 N).filter (fun (n : ℕ) => (n : ℝ)<lemma23PaperP D ∧
      ¬n.Coprime (lemma151Q D)),‖lemma151Rho β n‖/(n : ℝ))≤
      appendixBRoughRemovalConstant*lemma23PaperL D^(-8 : ℤ) := by
  apply le_trans _ (appendixB_original_B2_explicit hL hN hNP hβre hβ)
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,(mem_filter.mp hn).2.2⟩
  · intro n hn hnot
    exact appendixB_rho_mass_nonneg β n

/-- The actual Section 8 kernel used by the weighted replacement has strict
support, including zero value at its own endpoint. -/
theorem appendixB_regression_kernel_endpoint (X : ℝ) (γ : ℂ) (n₁ n : ℕ)
    (he : ((n₁*n : ℕ) : ℝ)=X) : lemma151Kernel X γ (n₁*n)=0 := by
  unfold lemma151Kernel
  apply if_neg
  intro h
  exact (not_lt_of_ge he.ge) h.2

/-- The source shifts are the actual finite-D definitions, not j*i*alpha. -/
theorem appendixB_regression_beta_shifts (D : ℕ) (c : ℝ) :
    lemma83PaperBeta D c 0=I*((lemma44PaperAlpha D*(1-5*c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) ∧
    lemma83PaperBeta D c 1=I*((2*lemma44PaperAlpha D*(1+c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) ∧
    lemma83PaperBeta D c 2=I*((3*lemma44PaperAlpha D*(1-c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) := by
  exact ⟨rfl,rfl,rfl⟩

/-- Original Q uses strict q<D^4, not a closed prime product. -/
theorem appendixB_regression_original_Q (D : ℕ) :
    lemma151Q D=∏ q∈(range (D^4)).filter Nat.Prime,q := rfl

/-- B.1's repaired input is the actual linear ν tail through floor(P^2),
not an assumed extension of the D^8 Lemma 3.2 statement. -/
theorem appendixB_regression_B1_source_input {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    (hN : N≤⌊lemma23PaperP D^2⌋₊) :
    (∑ h∈Ioc (D^4) N,‖lemma23NuArithmeticFunction χ h‖/(h : ℝ))≤
      21*lemma23PaperL D^(-2013 : ℤ) :=
  appendixB_actual_nu_tail χ hD hL hA hAbs hN

end ZhangLS.Spec
