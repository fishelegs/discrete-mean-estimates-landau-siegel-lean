import ZhangLS.Spec.BCoefficientBounds

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ComplexConjugate

lemma b_paperP_one_le (D : ℕ) : 1 ≤ lemma23PaperP D := by
  unfold lemma23PaperP lemma23PaperL
  exact Real.one_le_exp (pow_nonneg (Real.log_natCast_nonneg D) 9)

lemma b_h14_cutoff_le_P1 (D : ℕ) :
    (lemma23PaperP D)^(1/2 : ℝ) ≤ lemma151P1 D :=
  Real.rpow_le_rpow_of_exponent_le (b_paperP_one_le D) (by norm_num)

lemma b_paperT_one_le (D : ℕ) : 1 ≤ lemma56PaperT D := by
  unfold lemma56PaperT
  exact Real.one_le_exp (Real.rpow_nonneg (Real.log_natCast_nonneg D) _)

lemma b_P2_le_half_power (D : ℕ) :
    lemma151P2 D ≤ (lemma23PaperP D)^(1/2 : ℝ) := by
  have ht : lemma56PaperT D^(-10 : ℤ) ≤ 1 := by
    rw [zpow_neg,zpow_ofNat]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (b_paperT_one_le D))
  have hP : 0 ≤ (lemma23PaperP D)^(0.5 : ℝ) :=
    Real.rpow_nonneg (Real.exp_nonneg _) _
  have hh := mul_le_mul_of_nonneg_left ht hP
  norm_num only [mul_one] at hh
  convert hh using 1
  norm_num [lemma151P2]

/-- Exact source support bound in original parameters; neither cutoff is asymptotically replaced. -/
theorem b_product_cutoff_exact (D : ℕ) :
    bProductCutoff D = max ((lemma23PaperP D)^(0.998 : ℝ))
      (lemma23PaperP D*lemma56PaperT D^(-10 : ℤ)) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  unfold bProductCutoff bFirstCutoff bSecondCutoff
  rw [max_eq_left (b_P2_le_half_power D),mul_max_of_nonneg]
  · congr 1
    · unfold lemma151P3
      rw [← Real.rpow_add hP]
      norm_num
    · unfold lemma151P2
      rw [← mul_assoc,← Real.rpow_add hP]
      norm_num
  · exact (Real.rpow_pos_of_pos hP _).le

/-- The literal finite summand, with no hidden coefficient substitution. -/
lemma b_source_H_literal {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (X : ℝ) (β : ℂ) (Y : ℝ)
    (hYX : Y ≤ X) (s : ℂ) :
    bSourceH χ ψ X β Y s =
      ∑ n ∈ (Icc 1 ⌈Y⌉₊).filter (fun n : ℕ => (n : ℝ) < Y),
        χ.evalNat n*ψ (n : ZMod p)/(n : ℂ)^s *
        (1-(Real.log (n : ℝ)/Real.log X : ℂ))*((X/n : ℝ) : ℂ)^β := by
  unfold bSourceH
  apply sum_congr rfl
  intro n hn
  have hmem := mem_filter.mp hn
  rw [lemma151Kernel,if_pos ⟨(mem_Icc.mp hmem.1).1,hmem.2.trans_le hYX⟩]
  ring

/-- Literal H14 of (12.1), including its strict P^(1/2) cutoff and P1 kernel. -/
theorem b_actual_H14_literal {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH14 χ ψ s =
      ∑ n ∈ (Icc 1 ⌈(lemma23PaperP D)^(1/2 : ℝ)⌉₊).filter
        (fun n : ℕ => (n : ℝ) < (lemma23PaperP D)^(1/2 : ℝ)),
        χ.evalNat n*ψ (n : ZMod p)/(n : ℂ)^s *
        (1-(Real.log (n : ℝ)/Real.log (lemma151P1 D) : ℂ))*
        ((lemma151P1 D/n : ℝ) : ℂ)^(lemma151Beta6 D) :=
  b_source_H_literal χ ψ _ _ _ (b_h14_cutoff_le_P1 D) s

theorem b_actual_H12_literal {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH12 χ ψ s =
      ∑ n ∈ (Icc 1 ⌈lemma151P2 D⌉₊).filter (fun n : ℕ => (n : ℝ) < lemma151P2 D),
        χ.evalNat n*ψ (n : ZMod p)/(n : ℂ)^s *
        (1-(Real.log (n : ℝ)/Real.log (lemma151P2 D) : ℂ))*
        ((lemma151P2 D/n : ℝ) : ℂ)^(lemma151Beta7 D) :=
  b_source_H_literal χ ψ _ _ _ le_rfl s

theorem b_actual_H13_literal {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    bSourceH13 χ ψ s =
      ∑ n ∈ (Icc 1 ⌈lemma151P3 D⌉₊).filter (fun n : ℕ => (n : ℝ) < lemma151P3 D),
        χ.evalNat n*ψ (n : ZMod p)/(n : ℂ)^s *
        (1-(Real.log (n : ℝ)/Real.log (lemma151P3 D) : ℂ))*
        ((lemma151P3 D/n : ℝ) : ℂ)^(lemma151Beta6 D) :=
  b_source_H_literal χ ψ _ _ _ le_rfl s

/-- These are the exact four source-model coefficients. Changing coefficient basis
multiplies by χ(n), and does not modify any of these iota factors or kernel parameters. -/
theorem b_four_source_coefficients_unchanged (D n : ℕ) :
    lemma151BChiPsi D n =
      conj lemma151Iota3*LSeries.convolution (bH14Coefficient D)
        (lemma151Kernel (lemma151P3 D) (lemma151Beta6 D)) n +
      conj lemma151Iota4*LSeries.convolution (bH14Coefficient D)
        (lemma151Kernel (lemma151P2 D) (lemma151Beta7 D)) n +
      (lemma151Iota2*conj lemma151Iota3)*LSeries.convolution
        (lemma151Kernel (lemma151P2 D) (lemma151Beta7 D))
        (lemma151Kernel (lemma151P3 D) (lemma151Beta6 D)) n +
      (lemma151Iota2*conj lemma151Iota4)*LSeries.convolution
        (lemma151Kernel (lemma151P2 D) (lemma151Beta7 D))
        (lemma151Kernel (lemma151P2 D) (lemma151Beta7 D)) n := by
  rw [b_canonical_four_kernel_expansion]
  simp only [LSeries.convolution_def,mul_sum,←sum_add_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

/-- Exact arithmetic-sum basis repair on the original rough domain, with all shifts retained.
This is a finite-support identity, not a contour or asymptotic claim. -/
theorem b_repaired_rough_sum {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (c : ℝ) (j : Fin 3) (n₁ : ℕ) :
    lemma151ArithmeticSum χ c j (lemma151BPsi χ) n₁ =
      χ.evalNat n₁ * ∑' n : ℕ, if n.Coprime (lemma151Q D) then
        lemma151BChiPsi D (n₁*n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n else 0 := by
  unfold lemma151ArithmeticSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs with hn
  · rw [lemma151_psi_basis_rough_cancellation χ hD n₁ hn]
    ring
  · simp

/-- Strict H14 endpoint regression on the actual coefficient. -/
theorem b_actual_H14_endpoint (D n : ℕ)
    (hn : (n : ℝ)=(lemma23PaperP D)^(1/2 : ℝ)) : bH14Coefficient D n=0 := by
  simp [bH14Coefficient,hn]

/-- P2 keeps the source T^-10 factor, not the leading-order replacement P^.5. -/
theorem b_actual_P2_exact (D : ℕ) :
    lemma151P2 D=(lemma23PaperP D)^(0.5 : ℝ)*lemma56PaperT D^(-10 : ℤ) := rfl

/-- The actual product coefficient at 1 is unchanged in the two bases. -/
theorem b_actual_basis_at_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma151BPsi χ 1=lemma151First D 1*lemma151Second D 1 := by
  simp [lemma151BPsi,lemma151BChiPsi,RealPrimitiveCharacter.evalNat]

/-- The actual Section 15 L-ratio coefficient at 1 is the same source coefficient. -/
theorem b_actual_ratio_coefficient_at_one {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) :
    (lemma152Kappa (lemma152PaperBeta D c)*bPsiArithmetic χ) 1 =
      lemma151First D 1*lemma151Second D 1 := by
  simp only [ArithmeticFunction.mul_apply_one,lemma152_kappa_one,one_mul,
    bPsiArithmetic,ArithmeticFunction.coe_mk,b_actual_basis_at_one]

end ZhangLS.Spec
