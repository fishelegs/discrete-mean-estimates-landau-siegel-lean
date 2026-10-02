import ZhangLS.Spec.Lemma121Concrete
import ZhangLS.Spec.Lemma121RepairedHigh

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Real

-- 1–4: exact decimal arithmetic and the source T^(-10) factor.
example (D : ℕ) : lemma121P1 D=lemma23PaperP D^(63/125:ℝ) := rfl
example (D : ℕ) : lemma121PDoublePrimeOne D=
    lemma23PaperP D^(62/125:ℝ)*(D:ℝ)*lemma51PaperT0 D := rfl
example (D : ℕ) : lemma121PDoublePrimeTwo D=
    lemma23PaperP D^(1/2:ℝ)*(D:ℝ)*lemma51PaperT0 D := rfl
example (D : ℕ) : lemma121P2 D=
    lemma23PaperP D^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ) := rfl

-- 5–6: neither endpoint is silently included.
example (D : ℕ) : lemma121Kappa13 D (lemma121PDoublePrimeOne D)=0 :=
  lemma121_kernel_lower_endpoint _ _ _ _
example (D : ℕ) : lemma121Kappa13 D (lemma121PDoublePrimeTwo D)=0 :=
  lemma121_kernel_upper_endpoint _ _ _ _

-- 7–8: original signed phase and first-order coefficient.
example (b a : ℂ) (h : ℝ) : lemma121Phase b a h=
    Complex.exp (-b*(h:ℂ))*(-1+(b-a)*(h:ℂ)) := rfl
example (b a : ℂ) (h : ℝ) : lemma121LinearPhase b a h=
    -1+(2*b-a)*(h:ℂ) := rfl

-- 9–10: midpoint cancellation and zero logarithm.
example (b : ℂ) (h : ℝ) : lemma121LinearPhase b (2*b) h = -1 := by
  simp [lemma121LinearPhase]
example (b a : ℂ) : lemma121Phase b a 0 = -1 := by
  simp [lemma121Phase]

-- 11: β6 retains its exact 3iα/2 value.
example (D : ℕ) : lemma82SmoothingBeta D 6=3*I*(lemma44PaperAlpha D:ℂ)/2 := by
  simp [lemma82SmoothingBeta]

-- 12: original shared c′ is present in β3; it was not reset to zero.
example (D : ℕ) (c : ℝ) : lemma82PaperBeta D c (2:Fin 3)=
    I*((3*lemma44PaperAlpha D*(1-c*lemma44PaperAlpha D*lemma23PaperL D):ℝ):ℂ) := by
  simp [lemma82PaperBeta,lemma52PaperBetaThree,lemma23PaperOffsetThree]

-- 13–14: the repaired conclusions are actually proved.
example : Lemma121ExactHighTarget := lemma121_exact_high_proved
example : Lemma121RepairedHighTarget := lemma121_repaired_high_proved

-- 15: the printed proposition remains separately named with its 10^-5 bound.
example : Lemma121PrintedHighTarget ↔
  (∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℕ,
      lemma121PDoublePrimeOne D<(d:ℝ) → (d:ℝ)<lemma121P2 D →
      ∃ ε : ℂ, ‖ε‖<(1:ℝ)/100000 ∧
        lemma121Sum χ c j d=LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
          (lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
            (Real.log ((d:ℝ)/lemma121PDoublePrimeOne D))+ε)) := Iff.rfl

-- 16–17: exact error-budget arithmetic is visible.
example : (101:ℝ)/125000+1/10000 < 1/1000 := by norm_num
example : (1:ℝ)/100000 < 1/1000 := by norm_num

-- 18: source-level phase obstruction is kernel checked, not numerical evidence.
example : (1:ℝ)/100000 <
    ‖lemma121Phase (3*I*(Real.pi:ℂ)/2) (3*I*(Real.pi:ℂ)) (1/500)-
      lemma121LinearPhase (3*I*(Real.pi:ℂ)/2) (3*I*(Real.pi:ℂ)) (1/500)‖ :=
  lemma121_limiting_phase_exceeds_printed_budget

-- 19–20: high range really implies a long truncated sum and the exact log gap.
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) {d : ℝ}
    (hlo : lemma121PDoublePrimeOne D<d) (hhi : d<lemma121P2 D) :
    lemma56PaperT D<lemma121PDoublePrimeTwo D/d :=
  (lemma121_high_range_geometry hD hL hlo hhi).1
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) :
    Real.log (lemma121PDoublePrimeTwo D/lemma121PDoublePrimeOne D)=
      (1/250:ℝ)*lemma23PaperL D^9 :=
  (lemma121_endpoint_geometry hD hL).2.2.2.2.2.1

end ZhangLS.Spec

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

-- 21–23: all added capstones are proved, separately from the printed target.
example : Lemma121LowTarget := lemma121_low_proved
example : Lemma121TransitionTarget := lemma121_transition_proved
example : Lemma121ConcreteExactTarget := lemma121_concrete_exact_proved

-- 24: the all-range kernel decomposition uses actual characters and both cutoffs.
example {D : ℕ} (χ : RealPrimitiveCharacter D) {A B Q d : ℝ}
    (hA : 0<A) (hB : 0<B) (hAB : A≤B) (hd : 0<d) (a b : ℂ) :
    (∑ n ∈ lemma82StrictCutoff (B/d),
      χ.evalNat n*lemma121Kernel A B Q b (d*(n:ℝ))/(n:ℂ)^(1-a)) =
    (((d/A:ℝ):ℂ)^(-b)/(Q:ℂ))*
      ((Real.log (B/A):ℂ)*lemma121StrictPolynomial χ (B/d) (1+b-a)-
        lemma82WeightedPolynomial χ (B/d) (1+b-a)+
        lemma82WeightedPolynomial χ (A/d) (1+b-a)) :=
  lemma121_kernel_sum_all_ranges χ hA hB hAB hd a b

-- 25: the exact low/transition boundary belongs to the low branch.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : (D:ℝ)/lemma56PaperT D≤lemma56PaperT D^(-(1/2:ℝ))) (j : Fin 3) :
    ‖lemma121Sum χ c j (lemma121PDoublePrimeOne D/lemma56PaperT D)‖≤
      36*lemma56PaperT D^(-(1/2:ℝ)) :=
  lemma121_low_exponential_estimate χ hD hL hc hsmall htail j
    (div_pos (lemma121_endpoint_geometry hD hL).1 (Real.exp_pos _)) le_rfl

-- 26: the upper transition boundary is included and has the concrete L^-7 bound.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    (hA : NormalizedAssumptionA χ) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : ∀ x : ℝ, lemma56PaperT D<x → (D:ℝ)/x≤lemma23PaperL D^(-15:ℤ)) (j : Fin 3) :
    ‖lemma121Sum χ c j (lemma121PDoublePrimeOne D)‖≤
      lemma121TransitionConstant*lemma23PaperL D^(-7:ℤ) := by
  have hg := lemma121_endpoint_geometry hD hL
  have hLp : 0<lemma23PaperL D := by linarith
  have hT : 1<lemma56PaperT D := Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hLp _)
  exact lemma121_transition_estimate χ hD hL hA hc hsmall htail j
    (div_lt_self hg.1 hT) le_rfl

-- 27–28: integer strict-cutoff behavior and its unweighted correction.
example : lemma82StrictCutoff 1=∅ := by
  ext n
  rw [lemma82_mem_strictCutoff (by norm_num)]
  simp only [Finset.notMem_empty,iff_false,not_and]
  intro hn
  have hh : (1:ℝ)≤n := by exact_mod_cast hn
  exact not_lt_of_ge hh
example {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    lemma82FinitePolynomial χ 1 s-lemma121StrictPolynomial χ 1 s=χ.evalNat 1 := by
  simpa using lemma121_strict_polynomial_endpoint χ (by norm_num : (1:ℝ)≤1) s

-- 29: when the strict endpoints coincide, the kernel is identically zero.
example (A Q n : ℝ) (b : ℂ) : lemma121Kernel A A Q b n=0 := by
  have hh : ¬(A<n ∧ n<A) := by intro h; linarith
  simp [lemma121Kernel,hh]

-- 30: the shared absolute constant dominates the original exponential constant.
example : 36<lemma121ConcreteConstant := by
  unfold lemma121ConcreteConstant
  have := lemma121_transition_constant_pos
  have := lemma121_exact_high_constant_pos
  linarith

-- 31: the transition endpoint geometry forces the upper sum to be long.
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) {d : ℝ}
    (hlo : lemma121PDoublePrimeOne D/lemma56PaperT D<d)
    (hhi : d≤lemma121PDoublePrimeOne D) : lemma56PaperT D<lemma121PDoublePrimeTwo D/d :=
  (lemma121_transition_geometry hD hL hlo hhi).2.2.2.1

-- 32: the exact-phase source repair is retained in the full capstone.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) (j : Fin 3) (d : ℝ) :
    lemma121ExactMain χ c j d=LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
      Complex.exp (-(lemma82SmoothingBeta D 6)*(Real.log (d/lemma121PDoublePrimeOne D):ℂ))*
      (-1+(lemma82SmoothingBeta D 6-lemma82PaperBeta D c j)*(Real.log (d/lemma121PDoublePrimeOne D):ℂ)) := by
  unfold lemma121ExactMain lemma121Phase
  ring

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma121Phase
#print axioms ZhangLS.Spec.lemma121LinearPhase
#print axioms ZhangLS.Spec.lemma121_phase_linearization_bound
#print axioms ZhangLS.Spec.lemma121_phase_remainder_lower
#print axioms ZhangLS.Spec.lemma121_limiting_phase_exceeds_printed_budget
#print axioms ZhangLS.Spec.lemma121P1
#print axioms ZhangLS.Spec.lemma121P2
#print axioms ZhangLS.Spec.lemma121PDoublePrimeOne
#print axioms ZhangLS.Spec.lemma121PDoublePrimeTwo
#print axioms ZhangLS.Spec.lemma121Kernel
#print axioms ZhangLS.Spec.lemma121Kappa13
#print axioms ZhangLS.Spec.lemma121Sum
#print axioms ZhangLS.Spec.lemma121ExactMain
#print axioms ZhangLS.Spec.lemma121PrintedMain
#print axioms ZhangLS.Spec.Lemma121PrintedHighTarget
#print axioms ZhangLS.Spec.Lemma121PrintedTarget
#print axioms ZhangLS.Spec.lemma121_kernel_lower_endpoint
#print axioms ZhangLS.Spec.lemma121_kernel_upper_endpoint
#print axioms ZhangLS.Spec.lemma121StrictPolynomial
#print axioms ZhangLS.Spec.lemma121_strict_polynomial_endpoint
#print axioms ZhangLS.Spec.lemma121_finite_polynomial_error
#print axioms ZhangLS.Spec.lemma121_strict_polynomial_error
#print axioms ZhangLS.Spec.lemma121_kernel_sum_exact
#print axioms ZhangLS.Spec.lemma121_kernel_sum_analytic_error
#print axioms ZhangLS.Spec.lemma121_local_negative_derivative_error
#print axioms ZhangLS.Spec.lemma121_actual_exact_phase_bound
#print axioms ZhangLS.Spec.lemma121_log_P1
#print axioms ZhangLS.Spec.lemma121_endpoint_geometry
#print axioms ZhangLS.Spec.lemma121_high_range_geometry
#print axioms ZhangLS.Spec.lemma121_tail_absorption_eventually
#print axioms ZhangLS.Spec.lemma121ExactHighConstant
#print axioms ZhangLS.Spec.lemma121_exact_high_constant_pos
#print axioms ZhangLS.Spec.lemma121_high_error_absorption
#print axioms ZhangLS.Spec.Lemma121ExactHighTarget
#print axioms ZhangLS.Spec.lemma121_exact_high_proved
#print axioms ZhangLS.Spec.lemma121_smoothing_beta_six_norm
#print axioms ZhangLS.Spec.lemma121_shift_difference_norm
#print axioms ZhangLS.Spec.lemma121_actual_phase_budget
#print axioms ZhangLS.Spec.lemma121_LDeriv_norm_lower
#print axioms ZhangLS.Spec.lemma121_normalized_analytic_error
#print axioms ZhangLS.Spec.Lemma121RepairedHighTarget
#print axioms ZhangLS.Spec.lemma121_repaired_high_proved
#print axioms ZhangLS.Spec.lemma121_strict_filter
#print axioms ZhangLS.Spec.lemma121_raw_kernel_term
#print axioms ZhangLS.Spec.lemma121_kernel_sum_all_ranges
#print axioms ZhangLS.Spec.lemma121_kernel_sum_low_error
#print axioms ZhangLS.Spec.lemma121_low_exponential_estimate
#print axioms ZhangLS.Spec.lemma121_exponential_absorption_eventually
#print axioms ZhangLS.Spec.Lemma121LowTarget
#print axioms ZhangLS.Spec.lemma121_low_proved
#print axioms ZhangLS.Spec.lemma121_weighted_trivial
#print axioms ZhangLS.Spec.lemma121WeightedConstant
#print axioms ZhangLS.Spec.lemma121_weighted_constant_pos
#print axioms ZhangLS.Spec.lemma121_weighted_uniform
#print axioms ZhangLS.Spec.lemma121UnweightedConstant
#print axioms ZhangLS.Spec.lemma121_unweighted_constant_pos
#print axioms ZhangLS.Spec.lemma121_strict_unweighted_uniform
#print axioms ZhangLS.Spec.lemma121_transition_geometry
#print axioms ZhangLS.Spec.lemma121TransitionConstant
#print axioms ZhangLS.Spec.lemma121_transition_constant_pos
#print axioms ZhangLS.Spec.lemma121_transition_estimate
#print axioms ZhangLS.Spec.Lemma121TransitionTarget
#print axioms ZhangLS.Spec.lemma121_transition_proved
#print axioms ZhangLS.Spec.lemma121ConcreteConstant
#print axioms ZhangLS.Spec.lemma121_concrete_constant_pos
#print axioms ZhangLS.Spec.Lemma121ConcreteExactTarget
#print axioms ZhangLS.Spec.lemma121_concrete_exact_proved
