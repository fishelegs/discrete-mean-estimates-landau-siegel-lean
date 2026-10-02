import ZhangLS.Spec.BRatioConvolution
import ZhangLS.Spec.Lemma34TupleConvolution

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ComplexConjugate

lemma b_kernel_norm_le_one (X : ℝ) (β : ℂ) (hβ : β.re=0) (n : ℕ) :
    ‖lemma151Kernel X β n‖ ≤ 1 := by
  unfold lemma151Kernel
  split_ifs with h
  · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr h.1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.1
    have hX : 1 < X := hn1.trans_lt h.2
    have hlog : 0 < Real.log X := Real.log_pos hX
    have hrat0 : 0 ≤ Real.log (n : ℝ)/Real.log X :=
      div_nonneg (Real.log_natCast_nonneg n) hlog.le
    have hrat1 : Real.log (n : ℝ)/Real.log X ≤ 1 :=
      (div_le_one hlog).mpr (Real.log_le_log hn h.2.le)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (hn.trans h.2) hn),
      hβ,Real.rpow_zero,mul_one]
    have he : (1-(Real.log (n : ℝ)/Real.log X : ℂ)) =
        ((1-Real.log (n : ℝ)/Real.log X : ℝ) : ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hrat1)]
    linarith
  · simp

lemma b_beta6_re (D : ℕ) : (lemma151Beta6 D).re=0 := by
  simp [lemma151Beta6]
lemma b_beta7_re (D : ℕ) : (lemma151Beta7 D).re=0 := by
  simp [lemma151Beta7]

lemma b_h14_norm_le_one (D n : ℕ) : ‖bH14Coefficient D n‖ ≤ 1 := by
  unfold bH14Coefficient
  split_ifs
  · exact b_kernel_norm_le_one _ _ (b_beta6_re D) n
  · simp

lemma b_first_norm_bound (D n : ℕ) : ‖lemma151First D n‖ ≤ 1+‖lemma151Iota2‖ := by
  change ‖bH14Coefficient D n+lemma151Iota2*lemma151Kernel _ _ n‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add (b_h14_norm_le_one D n)
    (by simpa using (mul_le_mul_of_nonneg_left
      (b_kernel_norm_le_one _ _ (b_beta7_re D) n) (norm_nonneg lemma151Iota2)))

lemma b_second_norm_bound (D n : ℕ) :
    ‖lemma151Second D n‖ ≤ ‖lemma151Iota3‖+‖lemma151Iota4‖ := by
  unfold lemma151Second
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_conj]
  exact add_le_add
    (by simpa using (mul_le_mul_of_nonneg_left
      (b_kernel_norm_le_one _ _ (b_beta6_re D) n) (norm_nonneg lemma151Iota3)))
    (by simpa using (mul_le_mul_of_nonneg_left
      (b_kernel_norm_le_one _ _ (b_beta7_re D) n) (norm_nonneg lemma151Iota4)))

/-- Explicit D-independent coefficient constant, retaining the source iotas. -/
noncomputable def bCoefficientConstant : ℝ :=
  (1+‖lemma151Iota2‖)*(‖lemma151Iota3‖+‖lemma151Iota4‖)

lemma b_coefficient_constant_nonneg : 0 ≤ bCoefficientConstant := by
  unfold bCoefficientConstant; positivity

lemma b_coefficient_constant_pos : 0 < bCoefficientConstant := by
  have h3 : 0 < ‖lemma151Iota3‖ := norm_pos_iff.mpr (by
    intro h
    have hh := congrArg Complex.re h
    norm_num [lemma151Iota3] at hh)
  unfold bCoefficientConstant
  positivity

/-- Elementary convolution majorant; no unpublished P71 coefficient helper is imported. -/
lemma b_arithmetic_convolution_majorant (f g : ArithmeticFunction ℂ)
    (F G : ArithmeticFunction ℕ) {B C : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n, ‖f n‖ ≤ B*(F n : ℝ))
    (hg : ∀ n, ‖g n‖ ≤ C*(G n : ℝ)) (n : ℕ) :
    ‖(f*g) n‖ ≤ B*C*((F*G) n : ℝ) := by
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,Nat.cast_sum,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro ab _
  rw [norm_mul,Nat.cast_mul]
  calc
    _ ≤ (B*(F ab.1 : ℝ))*(C*(G ab.2 : ℝ)) :=
      mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

noncomputable def bFirstArithmetic (D : ℕ) : ArithmeticFunction ℂ :=
  ⟨lemma151First D, by simp [lemma151First,lemma151Kernel]⟩
noncomputable def bSecondArithmetic (D : ℕ) : ArithmeticFunction ℂ :=
  ⟨lemma151Second D, by simp [lemma151Second,lemma151Kernel]⟩
noncomputable def bCanonicalArithmetic (D : ℕ) : ArithmeticFunction ℂ :=
  ⟨lemma151BChiPsi D, by simp [lemma151BChiPsi]⟩

lemma b_canonical_arithmetic_product (D : ℕ) :
    bCanonicalArithmetic D=bFirstArithmetic D*bSecondArithmetic D := by
  ext n
  rfl

theorem b_canonical_norm_le_tau_two (D n : ℕ) :
    ‖lemma151BChiPsi D n‖ ≤ bCoefficientConstant*(lemma34Tau 2 n : ℝ) := by
  have hf (n : ℕ) : ‖bFirstArithmetic D n‖ ≤
      (1+‖lemma151Iota2‖)*(ArithmeticFunction.zeta n : ℝ) := by
    by_cases hn : n=0
    · subst n; simp
    · simpa only [ArithmeticFunction.zeta_apply_ne hn,Nat.cast_one,mul_one] using
        b_first_norm_bound D n
  have hg (n : ℕ) : ‖bSecondArithmetic D n‖ ≤
      (‖lemma151Iota3‖+‖lemma151Iota4‖)*(ArithmeticFunction.zeta n : ℝ) := by
    by_cases hn : n=0
    · subst n; simp
    · simpa only [ArithmeticFunction.zeta_apply_ne hn,Nat.cast_one,mul_one] using
        b_second_norm_bound D n
  have h := b_arithmetic_convolution_majorant (bFirstArithmetic D) (bSecondArithmetic D)
    ArithmeticFunction.zeta ArithmeticFunction.zeta (by positivity) hf hg n
  simpa only [← b_canonical_arithmetic_product,bCanonicalArithmetic,ArithmeticFunction.coe_mk,
    ← pow_two,lemma34Tau,bCoefficientConstant] using h

theorem b_psi_norm_le_tau_two {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma151BPsi χ n‖ ≤ bCoefficientConstant*(lemma34Tau 2 n : ℝ) := by
  rw [lemma151BPsi,norm_mul]
  calc
    _ ≤ ‖lemma151BChiPsi D n‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (χ.chi.norm_le_one _)
    _ ≤ _ := b_canonical_norm_le_tau_two D n

lemma b_power_coefficient_majorant (β : ℂ) (hβ : β.re=0) (n : ℕ) :
    ‖lemma83PowerCoefficient β n‖ ≤ (ArithmeticFunction.zeta n : ℝ) := by
  by_cases hn : n=0
  · subst n; simp [lemma83PowerCoefficient]
  · simp only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,if_neg hn,
      ArithmeticFunction.zeta_apply_ne hn,Nat.cast_one]
    have hnp : 0<(n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hnp,
      neg_re,hβ,neg_zero,Real.rpow_zero]

lemma b_moebius_coefficient_majorant (n : ℕ) :
    ‖(ArithmeticFunction.moebius : ArithmeticFunction ℂ) n‖ ≤
      (ArithmeticFunction.zeta n : ℝ) := by
  by_cases hn : n=0
  · subst n; simp
  · rw [ArithmeticFunction.zeta_apply_ne hn,ArithmeticFunction.intCoe_apply]
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

lemma b_kappa_norm_le_tau_three (β : Fin 2 → ℂ) (hβ : ∀ j, (β j).re=0) (n : ℕ) :
    ‖lemma152Kappa β n‖ ≤ (lemma34Tau 3 n : ℝ) := by
  have hpow (j : Fin 2) (n : ℕ) : ‖lemma83PowerCoefficient (β j) n‖ ≤
      1*(ArithmeticFunction.zeta n : ℝ) := by
    simpa using b_power_coefficient_majorant (β j) (hβ j) n
  have h01 := b_arithmetic_convolution_majorant
    (lemma83PowerCoefficient (β 0)) (lemma83PowerCoefficient (β 1))
    ArithmeticFunction.zeta ArithmeticFunction.zeta (by norm_num : (0 : ℝ) ≤ 1) (hpow 0) (hpow 1)
  have hμ (n : ℕ) : ‖(ArithmeticFunction.moebius : ArithmeticFunction ℂ) n‖ ≤
      1*(ArithmeticFunction.zeta n : ℝ) := by simpa using b_moebius_coefficient_majorant n
  have h := b_arithmetic_convolution_majorant (C := 1)
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
    (lemma83PowerCoefficient (β 0)*lemma83PowerCoefficient (β 1))
    ArithmeticFunction.zeta (ArithmeticFunction.zeta*ArithmeticFunction.zeta)
    (by norm_num : (0 : ℝ) ≤ 1) hμ (by simpa only [one_mul] using h01) n
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℕ)*
      (ArithmeticFunction.zeta*ArithmeticFunction.zeta)=ArithmeticFunction.zeta^3 := by ring
  simpa only [one_mul,he,lemma152Kappa,lemma34Tau] using h

/-- Actual τ₅ admissibility needed for the Section 15 application of Proposition 14.1. -/
theorem b_actual_ratio_coefficient_tau_five {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (n : ℕ) :
    ‖(lemma152Kappa (lemma152PaperBeta D c)*bPsiArithmetic χ) n‖ ≤
      bCoefficientConstant*(lemma34Tau 5 n : ℝ) := by
  have h := b_arithmetic_convolution_majorant
    (lemma152Kappa (lemma152PaperBeta D c)) (bPsiArithmetic χ)
    (ArithmeticFunction.zeta^3) (ArithmeticFunction.zeta^2)
    (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_mul,lemma34Tau] using
      b_kappa_norm_le_tau_three (lemma152PaperBeta D c) (lemma152_beta_re D c))
    (b_psi_norm_le_tau_two χ) n
  simpa only [← pow_add,lemma34Tau,one_mul] using h

end ZhangLS.Spec
