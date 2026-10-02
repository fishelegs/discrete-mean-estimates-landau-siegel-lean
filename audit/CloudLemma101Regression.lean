import ZhangLS.Spec.Lemma101

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma101_regression_scales (D : ℕ) :
    lemma23PaperP D=Real.exp (Real.log (D:ℝ)^9) ∧
    lemma56PaperT D=Real.exp (Real.log (D:ℝ)^(11/10:ℝ)) ∧
    lemma44PaperAlpha D=Real.pi/Real.log (lemma23PaperP D) := ⟨rfl,rfl,rfl⟩

lemma lemma101_regression_beta_formulas (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c 0=I*((lemma44PaperAlpha D*
      (1-5*c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) ∧
    lemma82PaperBeta D c 1=I*((2*lemma44PaperAlpha D*
      (1+c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) ∧
    lemma82PaperBeta D c 2=I*((3*lemma44PaperAlpha D*
      (1-c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) := by
  simp [lemma82PaperBeta,lemma52PaperBetaOne,lemma52PaperBetaTwo,lemma52PaperBetaThree,
    lemma23PaperOffsetOne,lemma23PaperOffsetTwo,lemma23PaperOffsetThree]

/-- Literal paper labels 1,2,3 correspond bijectively to the zero-based Fin 3 index. -/
lemma lemma101_regression_natural_index (D : ℕ) (c : ℝ) (k : ℕ)
    (hk1 : 1≤k) (hk3 : k≤3) :
    let j : Fin 3 := ⟨k-1,by omega⟩
    j.val+1=k ∧ lemma82PaperBeta D c j =
      if k=1 then lemma52PaperBetaOne D c else
      if k=2 then lemma52PaperBetaTwo D c else lemma52PaperBetaThree D c := by
  have hk : k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hk with h|h|h <;> subst k <;> simp [lemma82PaperBeta]

lemma lemma101_regression_cyclic_wrap (D : ℕ) (c : ℝ) :
    lemma82PaperBeta D c ((2:Fin 3)+1)=lemma52PaperBetaOne D c ∧
    lemma82PaperBeta D c ((2:Fin 3)+2)=lemma52PaperBetaTwo D c := by
  rw [show ((2:Fin 3)+1)=0 by decide,show ((2:Fin 3)+2)=1 by decide]
  simp [lemma82PaperBeta]

lemma lemma101_regression_cyclic_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (y : ℝ) :
    lemma101Sum χ c (j+3) y=lemma101Sum χ c j y := by simp

lemma lemma101_regression_tent_endpoints :
    lemma111Tent (1/2)=0 ∧ lemma111Tent (251/500)=1 ∧ lemma111Tent (63/125)=0 := by
  norm_num [lemma111Tent]

lemma lemma101_regression_literal_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) {y : ℝ} (hy : 0<y) :
    lemma101Sum χ c j y=∑' n : ℕ,
      χ.evalNat n/(n:ℂ)^(1-lemma82PaperBeta D c j)*
      (lemma111Tent (Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ) :=
  lemma101_sum_eq_tsum χ hD c j hy

lemma lemma101_regression_top_summand {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (c : ℝ) (j : Fin 3) {y : ℝ} (hy : 0<y)
    {n : ℕ} (hn : 0<n) (he : (n:ℝ)=lemma23PaperP D^(63/125:ℝ)/y) :
    χ.evalNat n/(n:ℂ)^(1-lemma82PaperBeta D c j)*
      (lemma111Tent (Real.log (y*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ)=0 := by
  apply lemma101_term_zero_beyond_support χ hD c j hy hn
  exact he.ge

lemma lemma101_regression_transition_expanded (D : ℕ) (y : ℝ) :
    Lemma101Transition D y ↔
      ((lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D<y ∧ y≤lemma23PaperP D^(1/2:ℝ)) ∨
      (lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D<y ∧ y≤lemma23PaperP D^(251/500:ℝ))) ∨
      (lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D<y ∧ y<lemma23PaperP D^(63/125:ℝ)) := Iff.rfl

lemma lemma101_regression_first_transition_closed {D : ℕ} (hD : 1<D) :
    Lemma101Transition D (lemma23PaperP D^(1/2:ℝ)) := by
  have hpos : 0<lemma23PaperP D^(1/2:ℝ) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  exact Or.inl (Or.inl ⟨div_lt_self hpos (lemma101_T_gt_one hD),le_rfl⟩)

lemma lemma101_regression_middle_transition_closed {D : ℕ} (hD : 1<D) :
    Lemma101Transition D (lemma23PaperP D^(251/500:ℝ)) := by
  have hpos : 0<lemma23PaperP D^(251/500:ℝ) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  exact Or.inl (Or.inr ⟨div_lt_self hpos (lemma101_T_gt_one hD),le_rfl⟩)

lemma lemma101_regression_last_transition_open {D : ℕ} (hD : 1<D) :
    ¬Lemma101Transition D (lemma23PaperP D^(63/125:ℝ)) := by
  have h₁ := Real.rpow_lt_rpow_of_exponent_lt (lemma101_P_gt_one hD)
    (by norm_num : (1/2:ℝ)<63/125)
  have h₂ := Real.rpow_lt_rpow_of_exponent_lt (lemma101_P_gt_one hD)
    (by norm_num : (251/500:ℝ)<63/125)
  rintro ((h|h)|h)
  · exact (not_le_of_gt h₁) h.2
  · exact (not_le_of_gt h₂) h.2
  · exact (lt_irrefl _) h.2

lemma lemma101_regression_first_transition_lower_open {D : ℕ} (hD : 1<D) :
    ¬Lemma101Transition D (lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D) := by
  have hT : 0≤lemma56PaperT D := (Real.exp_pos _).le
  have h₁ := div_le_div_of_nonneg_right
    (lemma101_half_power_le_power hD (by norm_num : (1/2:ℝ)≤251/500)) hT
  have h₂ := div_le_div_of_nonneg_right
    (lemma101_half_power_le_power hD (by norm_num : (1/2:ℝ)≤63/125)) hT
  rintro ((h|h)|h)
  · exact (lt_irrefl _) h.1
  · exact (not_lt_of_ge h₁) h.1
  · exact (not_lt_of_ge h₂) h.1

lemma lemma101_regression_strict_interior_lower (D : ℕ) :
    ¬lemma23PaperP D^(1/2:ℝ)<lemma23PaperP D^(1/2:ℝ) ∧
    ¬lemma23PaperP D^(251/500:ℝ)<lemma23PaperP D^(251/500:ℝ) := by simp

lemma lemma101_regression_closed_interior_upper (D : ℕ) :
    lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D≤lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D ∧
    lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D≤lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D := ⟨le_rfl,le_rfl⟩

/-- Explicitly derived boundary rate; not a definition of the paper's unexplained α₁. -/
lemma lemma101_regression_boundary_rate {D : ℕ} (hL : 1≤lemma23PaperL D) :
    Real.log (lemma56PaperT D)/Real.log (lemma23PaperP D)=lemma23PaperL D^(-79/10:ℝ) ∧
    Real.log (lemma56PaperT D)/Real.log (lemma23PaperP D)≤lemma23PaperL D^(-7:ℤ) :=
  ⟨paper_logT_div_logP (by linarith),paper_boundary_scale_le_L7 hL⟩

/-- Expanded actual-object statement with every original range and quantifier. -/
theorem lemma101_regression_original_expanded :
  ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ y : ℝ,
      let P := Real.exp (Real.log (D:ℝ)^9)
      let T := Real.exp (Real.log (D:ℝ)^(11/10:ℝ))
      let V := ∑ m ∈ Finset.Icc 1 ⌊P^(63/125:ℝ)/y⌋₊,
        χ.evalNat m/(m:ℂ)^(1-lemma82PaperBeta D c j)*
        (lemma111Tent (Real.log (y*(m:ℝ))/Real.log P):ℂ)
      (1≤y → y≤P^(1/2:ℝ)/T → ‖V‖≤C*T^(-κ)) ∧
      (P^(1/2:ℝ)<y → y≤P^(251/500:ℝ)/T →
        ‖V-(500*LDerivAtOne χ/(Real.log P:ℂ))*(-1-lemma82PaperBeta D c j*(Real.log (y/P^(1/2:ℝ)):ℂ))‖≤
          C*Real.log (D:ℝ)^(-15:ℤ)) ∧
      (P^(251/500:ℝ)<y → y≤P^(63/125:ℝ)/T →
        ‖V-(500*LDerivAtOne χ/(Real.log P:ℂ))*(1-lemma82PaperBeta D c j*(Real.log (P^(63/125:ℝ)/y):ℂ))‖≤
          C*Real.log (D:ℝ)^(-15:ℤ)) ∧
      (((P^(1/2:ℝ)/T<y ∧ y≤P^(1/2:ℝ)) ∨ (P^(251/500:ℝ)/T<y ∧ y≤P^(251/500:ℝ))) ∨
        (P^(63/125:ℝ)/T<y ∧ y<P^(63/125:ℝ)) → ‖V‖≤C*Real.log (D:ℝ)^(-7:ℤ)) := by
  exact lemma101_proved

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma101_three_errors
#print axioms ZhangLS.Spec.lemma101_low_estimate
#print axioms ZhangLS.Spec.lemma101Constant
#print axioms ZhangLS.Spec.lemma101_constant_pos
#print axioms ZhangLS.Spec.lemma101_proved
#print axioms ZhangLS.Spec.lemma101Cutoff
#print axioms ZhangLS.Spec.lemma101Sum
#print axioms ZhangLS.Spec.lemma101MainLower
#print axioms ZhangLS.Spec.lemma101MainUpper
#print axioms ZhangLS.Spec.Lemma101Transition
#print axioms ZhangLS.Spec.Lemma101Target
#print axioms ZhangLS.Spec.lemma101_second_difference_norm
#print axioms ZhangLS.Spec.lemma101_two_errors
#print axioms ZhangLS.Spec.lemma101_log_second_difference
#print axioms ZhangLS.Spec.lemma101_log_lower_combination
#print axioms ZhangLS.Spec.lemma101_uniform_sum_bound
#print axioms ZhangLS.Spec.lemma101InteriorConstant
#print axioms ZhangLS.Spec.lemma101_interior_constant_pos
#print axioms ZhangLS.Spec.lemma101_weighted_interior_error
#print axioms ZhangLS.Spec.lemma101_lower_main_identity
#print axioms ZhangLS.Spec.lemma101_lower_estimate
#print axioms ZhangLS.Spec.lemma101_upper_estimate
#print axioms ZhangLS.Spec.lemma101_log_cutoff
#print axioms ZhangLS.Spec.lemma101_cutoff_pos
#print axioms ZhangLS.Spec.lemma101_cutoff_mono
#print axioms ZhangLS.Spec.lemma101_positive_log_sum
#print axioms ZhangLS.Spec.lemma101_tent_log_kernel
#print axioms ZhangLS.Spec.lemma101_sum_exact_bridge
#print axioms ZhangLS.Spec.lemma101_weighted_zero_of_le_one
#print axioms ZhangLS.Spec.lemma101_tent_zero_of_ge
#print axioms ZhangLS.Spec.lemma101_term_zero_beyond_support
#print axioms ZhangLS.Spec.lemma101_sum_eq_tsum
#print axioms ZhangLS.Spec.lemma101_P_gt_one
#print axioms ZhangLS.Spec.lemma101_T_gt_one
#print axioms ZhangLS.Spec.lemma101_cutoff_lt_P
#print axioms ZhangLS.Spec.lemma101_cutoff_ge_T
#print axioms ZhangLS.Spec.lemma101_cutoff_le_one
#print axioms ZhangLS.Spec.lemma101_half_power_le_power
#print axioms ZhangLS.Spec.lemma101_half_power_gt_one
#print axioms ZhangLS.Spec.lemma101_T_le_half_power
#print axioms ZhangLS.Spec.lemma101_transition_ge_one
#print axioms ZhangLS.Spec.lemma101_prefactor_norm
#print axioms ZhangLS.Spec.lemma101_uniform_threshold
#print axioms ZhangLS.Spec.lemma101_shift_in_disk
#print axioms ZhangLS.Spec.lemma101_weighted_linear_error
#print axioms ZhangLS.Spec.lemma101_weighted_trivial
#print axioms ZhangLS.Spec.lemma101WeightedBoundConstant
#print axioms ZhangLS.Spec.lemma101_weighted_bound_constant_pos
#print axioms ZhangLS.Spec.lemma101_weighted_uniform_bound
#print axioms ZhangLS.Spec.lemma101_regression_scales
#print axioms ZhangLS.Spec.lemma101_regression_beta_formulas
#print axioms ZhangLS.Spec.lemma101_regression_natural_index
#print axioms ZhangLS.Spec.lemma101_regression_cyclic_wrap
#print axioms ZhangLS.Spec.lemma101_regression_cyclic_sum
#print axioms ZhangLS.Spec.lemma101_regression_tent_endpoints
#print axioms ZhangLS.Spec.lemma101_regression_literal_sum
#print axioms ZhangLS.Spec.lemma101_regression_top_summand
#print axioms ZhangLS.Spec.lemma101_regression_transition_expanded
#print axioms ZhangLS.Spec.lemma101_regression_first_transition_closed
#print axioms ZhangLS.Spec.lemma101_regression_middle_transition_closed
#print axioms ZhangLS.Spec.lemma101_regression_last_transition_open
#print axioms ZhangLS.Spec.lemma101_regression_first_transition_lower_open
#print axioms ZhangLS.Spec.lemma101_regression_strict_interior_lower
#print axioms ZhangLS.Spec.lemma101_regression_closed_interior_upper
#print axioms ZhangLS.Spec.lemma101_regression_boundary_rate
#print axioms ZhangLS.Spec.lemma101_regression_original_expanded
