import ZhangLS.Spec.Lemma101ExactBridge
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Real

lemma lemma101_shift_in_disk {D : ℕ} {c : ℝ} (hL : 2000≤lemma23PaperL D)
    (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖(1-lemma82PaperBeta D c j)-1‖≤10*lemma44PaperAlpha D ∧
      ‖1-lemma82PaperBeta D c j‖≤2 := by
  have hβ := lemma82_beta_norm (by linarith : 3≤lemma23PaperL D) hc hsmall j
  have ha : 0<lemma44PaperAlpha D := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    positivity
  have hs : ‖(1-lemma82PaperBeta D c j)-1‖≤10*lemma44PaperAlpha D := by
    rw [sub_sub_cancel_left, norm_neg]
    linarith
  refine ⟨hs,?_⟩
  have hr : 10*lemma44PaperAlpha D≤1/(4*lemma23PaperL D) :=
    lemma58_original_radius_in_taylor_disk hL
  have hq : 1/(4*lemma23PaperL D)≤(1:ℝ) := by
    apply (div_le_one (by positivity : 0<4*lemma23PaperL D)).mpr
    linarith
  calc
    ‖1-lemma82PaperBeta D c j‖ ≤ ‖(1-lemma82PaperBeta D c j)-1‖+‖(1:ℂ)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 2 := by simp only [norm_one]; linarith

lemma lemma101_weighted_linear_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {x : ℝ} (hx : 1≤x) (hxp : x<lemma23PaperP D) :
    ‖lemma82WeightedPolynomial χ x (1-lemma82PaperBeta D c j) -
      LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log x:ℂ))‖ ≤
      16*(D:ℝ)/x + lemma82LocalErrorConstant*lemma23PaperL D^(-6:ℤ) := by
  have hs := lemma101_shift_in_disk hL hc hsmall j
  have ha := lemma82_weighted_abel_error χ hD hx
    (by simp [lemma82_beta_re] : (1-lemma82PaperBeta D c j).re=1) hs.2
  have hb := lemma82_local_analytic_error χ hD hL hA hx hxp hs.1
  have he : (1+(1-lemma82PaperBeta D c j-1)*(Real.log x:ℂ)) =
      1-lemma82PaperBeta D c j*(Real.log x:ℂ) := by ring
  rw [he] at hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add ha hb)

lemma lemma101_weighted_trivial {D : ℕ} (χ : RealPrimitiveCharacter D)
    {x : ℝ} (hx : 1≤x) {s : ℂ} (hs : s.re=1) :
    ‖lemma82WeightedPolynomial χ x s‖ ≤ Real.log x*(1+Real.log x) := by
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hlog : 0≤Real.log x := Real.log_nonneg hx
  have hh : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n:ℝ)⁻¹) ≤ 1+Real.log x := by
    have he := harmonic_floor_le_one_add_log x hx
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using he
  calc
    ‖lemma82WeightedPolynomial χ x s‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ‖χ.evalNat n*(n:ℂ)^(-s)*(Real.log (x/(n:ℝ)):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x*(n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn1 : (1:ℝ)≤n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnx : (n:ℝ)≤x := (Nat.le_floor_iff hxp.le).mp (Finset.mem_Icc.mp hn).2
      have hnl : 0≤Real.log (x/(n:ℝ)) := Real.log_nonneg ((le_div_iff₀ hn0).mpr (by simpa using hnx))
      have hnl' : Real.log (x/(n:ℝ))≤Real.log x := by
        rw [Real.log_div hxp.ne' hn0.ne']
        linarith [Real.log_nonneg hn1]
      rw [norm_mul, norm_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re, hs,
        Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnl]
      calc
        ‖χ.evalNat n‖*(n:ℝ)⁻¹*Real.log (x/(n:ℝ)) ≤ 1*(n:ℝ)⁻¹*Real.log x := by
          gcongr
          exact χ.evalNat_norm_le_one n
        _ = _ := by ring
    _ = Real.log x*(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n:ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh hlog

noncomputable def lemma101WeightedBoundConstant : ℝ :=
  18 + lemma82LocalErrorConstant + 16*Real.exp 1*(1+3*Real.pi)

lemma lemma101_weighted_bound_constant_pos : 0<lemma101WeightedBoundConstant := by
  unfold lemma101WeightedBoundConstant
  positivity [lemma82_local_error_constant_pos]

/-- A uniform actual coefficient bound, stronger than what the three transition
layers need. No undefined alpha-one symbol or contour estimate is used. -/
lemma lemma101_weighted_uniform_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {x : ℝ} (hx : 0<x) (hxp : x<lemma23PaperP D) :
    ‖lemma82WeightedPolynomial χ x (1-lemma82PaperBeta D c j)‖ ≤
      lemma101WeightedBoundConstant*lemma23PaperL D^2 := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hC : 0<lemma101WeightedBoundConstant := lemma101_weighted_bound_constant_pos
  by_cases hx1 : x≤1
  · rw [lemma101_weighted_zero_of_le_one χ hx hx1]
    simp only [norm_zero]
    positivity
  have hx1' : 1≤x := (lt_of_not_ge hx1).le
  by_cases hDx : x≤(D:ℝ)
  · have hh := lemma101_weighted_trivial χ hx1' (by simp [lemma82_beta_re] : (1-lemma82PaperBeta D c j).re=1)
    have hlx : Real.log x≤L := Real.log_le_log hx hDx
    have hlx0 : 0≤Real.log x := Real.log_nonneg hx1'
    have hC2 : 2≤lemma101WeightedBoundConstant := by
      unfold lemma101WeightedBoundConstant
      have hh := lemma82_local_error_constant_pos
      have hp : 0≤16*Real.exp 1*(1+3*Real.pi) := by positivity
      linarith
    calc
      _ ≤ Real.log x*(1+Real.log x) := hh
      _ ≤ L*(1+L) := by gcongr
      _ ≤ 2*L^2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)
  have hDx' : (D:ℝ)≤x := (lt_of_not_ge hDx).le
  have he := lemma101_weighted_linear_error χ hD hL hA hc hsmall j hx1' hxp
  have htail : 16*(D:ℝ)/x≤16 := by
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by norm_num) ((div_le_one hx).mpr hDx')
  have hpower : L^(-6:ℤ)≤L^2 := by
    rw [← zpow_natCast L 2]
    exact zpow_le_zpow_right₀ hL1 (by norm_num)
  have hder : ‖LDerivAtOne χ‖≤16*Real.exp 1*L^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith)
      (by simp; positivity)
  have hlog : 0≤Real.log x := Real.log_nonneg hx1'
  have hlog' : Real.log x≤L^9 := by
    have hh := Real.log_lt_log hx hxp
    simpa [lemma23PaperP,L] using hh.le
  have hb := lemma82_beta_norm (by linarith : 3≤lemma23PaperL D) hc hsmall j
  have hb' : ‖lemma82PaperBeta D c j‖*Real.log x≤3*Real.pi := by
    calc
      _ ≤ (3*lemma44PaperAlpha D)*L^9 :=
        mul_le_mul hb hlog' hlog ((norm_nonneg _).trans hb)
      _ = 3*Real.pi := by
        rw [paper_alpha_eq_L9]
        change 3*(Real.pi*L^(-9:ℤ))*L^9=3*Real.pi
        rw [zpow_neg, zpow_ofNat]
        field_simp
  have hm : ‖LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log x:ℂ))‖ ≤
      (16*Real.exp 1*(1+3*Real.pi))*L^2 := by
    rw [norm_mul]
    have hh : ‖1-lemma82PaperBeta D c j*(Real.log x:ℂ)‖≤1+3*Real.pi := by
      apply (norm_sub_le _ _).trans
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
      linarith
    calc
      _ ≤ (16*Real.exp 1*L^2)*(1+3*Real.pi) := mul_le_mul hder hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖lemma82WeightedPolynomial χ x (1-lemma82PaperBeta D c j)-
        LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log x:ℂ))‖ +
        ‖LDerivAtOne χ*(1-lemma82PaperBeta D c j*(Real.log x:ℂ))‖ := norm_le_norm_sub_add _ _
    _ ≤ 16 + lemma82LocalErrorConstant*L^2 + (16*Real.exp 1*(1+3*Real.pi))*L^2 := by
      exact add_le_add (he.trans (add_le_add htail
        (mul_le_mul_of_nonneg_left hpower lemma82_local_error_constant_pos.le))) hm
    _ ≤ lemma101WeightedBoundConstant*L^2 := by
      unfold lemma101WeightedBoundConstant
      have hL2 : 1≤L^2 := one_le_pow₀ hL1
      nlinarith

end ZhangLS.Spec
