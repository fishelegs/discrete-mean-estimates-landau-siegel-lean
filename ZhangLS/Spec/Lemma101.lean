import ZhangLS.Spec.Lemma101Estimates

/-! # Complete original Lemma 10.1

The original tent and shifted character sum are used. The proof is purely
Abelian: exact finite tent decomposition, the actual 16D/x Abel tail, and
actual local L-function derivative bounds. It needs no contour hypotheses,
no averaged inputs, and none of unfinished Lemmas 7.1 or 8.4.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma101_three_errors {a b c A B C : ℂ} {E : ℝ}
    (ha : ‖a-A‖≤E) (hb : ‖b-B‖≤E) (hc : ‖c-C‖≤E)
    (hcancel : A-2*B+C=0) : ‖a-2*b+c‖≤4*E := by
  have he : a-2*b+c=(a-A)-2*(b-B)+(c-C) := by
    linear_combination hcancel
  rw [he]
  apply (lemma101_second_difference_norm _ _ _).trans
  linarith

lemma lemma101_low_estimate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (htail : (D:ℝ)/lemma56PaperT D≤lemma56PaperT D^(-(1/2:ℝ)))
    (j : Fin 3) {y : ℝ} (hy1 : 1≤y)
    (hyhi : y≤lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D) :
    ‖lemma101Sum χ c j y‖≤32000*lemma56PaperT D^(-(1/2:ℝ)) := by
  have hyp : 0<y := zero_lt_one.trans_le hy1
  have hLp : 0<lemma23PaperL D := by linarith
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  have hT : 0<lemma56PaperT D := Real.exp_pos _
  have hxlo := lemma101_cutoff_ge_T hyp hyhi
  let s := 1-lemma82PaperBeta D c j
  let A : ℝ → ℂ := fun x => (Real.log x:ℂ)*dirichletLFunction χ s+deriv (dirichletLFunction χ) s
  have hs : s.re=1 := by simp [s,lemma82_beta_re]
  have hsn : ‖s‖≤2 := (lemma101_shift_in_disk hL hc hsmall j).2
  have hb (a : ℝ) (ha : 1/2≤a) :
      ‖lemma82WeightedPolynomial χ (lemma101Cutoff D y a) s-A (lemma101Cutoff D y a)‖≤
      16*((D:ℝ)/lemma56PaperT D) := by
    have hx := hxlo.trans (lemma101_cutoff_mono hD hyp ha)
    have hh := lemma82_weighted_abel_error χ hD ((lemma101_T_gt_one hD).le.trans hx) hs hsn
    apply hh.trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Nat.cast_nonneg D) hT hx) (by norm_num)
  have hcancel : A (lemma101Cutoff D y (63/125))-2*A (lemma101Cutoff D y (251/500))+
      A (lemma101Cutoff D y (1/2))=0 := by
    have he := lemma101_log_second_difference (D := D) hyp
    have heC : (Real.log (lemma101Cutoff D y (63/125)):ℂ)-
        2*(Real.log (lemma101Cutoff D y (251/500)):ℂ)+
        (Real.log (lemma101Cutoff D y (1/2)):ℂ)=0 := by exact_mod_cast he
    dsimp only [A]
    linear_combination dirichletLFunction χ s*heC
  have hh := lemma101_three_errors (hb (63/125) (by norm_num))
    (hb (251/500) (by norm_num)) (hb (1/2) (by norm_num)) hcancel
  have hpre : 500/lemma23PaperL D^9≤500 := by
    apply div_le_self (by norm_num)
    exact one_le_pow₀ (by linarith : 1≤lemma23PaperL D)
  rw [lemma101_sum_exact_bridge χ hD c j hyp,norm_mul,lemma101_prefactor_norm hLp]
  calc
    _ ≤ (500/lemma23PaperL D^9)*(4*(16*((D:ℝ)/lemma56PaperT D))) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ 500*(4*(16*((D:ℝ)/lemma56PaperT D))) :=
      mul_le_mul_of_nonneg_right hpre (by positivity)
    _ ≤ 32000*lemma56PaperT D^(-(1/2:ℝ)) := by nlinarith [htail]

noncomputable def lemma101Constant : ℝ :=
  32000 + lemma101InteriorConstant + 2000*lemma101WeightedBoundConstant

lemma lemma101_constant_pos : 0<lemma101Constant := by
  unfold lemma101Constant
  positivity [lemma101_interior_constant_pos, lemma101_weighted_bound_constant_pos]

/-- Full original Lemma 10.1, including its strict lower endpoints and the
strict final upper transition endpoint. The exponential exponent is 1/2;
all constants are absolute and chosen before the fixed positive c′. -/
theorem lemma101_proved : Lemma101Target := by
  refine ⟨lemma101Constant,1/2,lemma101_constant_pos,by norm_num,?_⟩
  intro c hc
  obtain ⟨D₀,hD₀,hh⟩ := lemma101_uniform_threshold c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN χ hA j y
  have h := hh D hDN
  have hD : 1<D := by omega
  have hL := h.2.1
  have hsmall := h.2.2.1
  have htail := h.2.2.2.1
  have htail' := h.2.2.2.2
  have hC₀ : 32000≤lemma101Constant := by
    unfold lemma101Constant
    have := lemma101_interior_constant_pos
    have := lemma101_weighted_bound_constant_pos
    linarith
  have hC₁ : lemma101InteriorConstant≤lemma101Constant := by
    unfold lemma101Constant
    have := lemma101_weighted_bound_constant_pos
    linarith
  have hC₂ : 2000*lemma101WeightedBoundConstant≤lemma101Constant := by
    unfold lemma101Constant
    have := lemma101_interior_constant_pos
    linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  refine ⟨?_,?_,?_,?_⟩
  · intro hy1 hyhi
    exact (lemma101_low_estimate χ hD hL hc hsmall htail' j hy1 hyhi).trans
      (mul_le_mul_of_nonneg_right hC₀ (by positivity))
  · intro hylo hyhi
    exact (lemma101_lower_estimate χ hD hL hA hc hsmall htail j hylo hyhi).trans
      (mul_le_mul_of_nonneg_right hC₁ (by positivity))
  · intro hylo hyhi
    exact (lemma101_upper_estimate χ hD hL hA hc hsmall htail j hylo hyhi).trans
      (mul_le_mul_of_nonneg_right hC₁ (by positivity))
  · intro hy
    exact (lemma101_uniform_sum_bound χ hD hL hA hc hsmall j
      (lemma101_transition_ge_one hD hL hy)).trans
      (mul_le_mul_of_nonneg_right hC₂ (by positivity))

end ZhangLS.Spec
