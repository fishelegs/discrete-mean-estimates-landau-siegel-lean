import ZhangLS.Spec.Lemma84WeightedMass
import ZhangLS.Spec.Lemma82

/-! Global bounds for the actual first inner sum, including the small-x boundary
where Lemma 8.2 is unavailable. This handles cross terms without assuming that
both mollifier cutoffs are simultaneously interior. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

/-- The actual first inner sum has an elementary log-squared bound at every
positive cutoff. Purely imaginary powers have unit modulus. -/
theorem lemma84_companion_elementary {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ : ℕ) {x : ℝ} (hx : 1≤x) :
    ‖lemma82ShiftedSum χ c j μ x‖≤Real.log x*(1+Real.log x) := by
  have hxp : 0<x := by linarith
  have hlx : 0≤Real.log x := Real.log_nonneg hx
  have hterm (n : ℕ) (hn : n∈lemma82StrictCutoff x) :
      ‖χ.evalNat n/(n:ℂ)^(1-lemma82PaperBeta D c j)*
        ((x/(n:ℝ):ℝ):ℂ)^(lemma82SmoothingBeta D μ)*(Real.log (x/(n:ℝ)):ℂ)‖≤
        Real.log x*(n:ℝ)⁻¹ := by
    have hm := (lemma82_mem_strictCutoff hxp.le n).mp hn
    have hn0 : 0<(n:ℝ) := by exact_mod_cast hm.1
    have hn1 : 1≤(n:ℝ) := by exact_mod_cast hm.1
    have hratio : 1≤x/(n:ℝ) := (le_div_iff₀ hn0).mpr (by simpa using hm.2.le)
    have hlog0 : 0≤Real.log (x/(n:ℝ)) := Real.log_nonneg hratio
    have hlog : Real.log (x/(n:ℝ))≤Real.log x := by
      apply Real.log_le_log (by positivity)
      exact div_le_self hxp.le hn1
    have hncp : ‖(n:ℂ)^(1-lemma82PaperBeta D c j)‖=(n:ℝ) := by
      change ‖((n:ℝ):ℂ)^(1-lemma82PaperBeta D c j)‖=_
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp only [Complex.sub_re,Complex.one_re,lemma82_beta_re,sub_zero,Real.rpow_one]
    have hxcp : ‖((x/(n:ℝ):ℝ):ℂ)^(lemma82SmoothingBeta D μ)‖=1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),lemma82_smoothing_beta_re,Real.rpow_zero]
    rw [norm_mul,norm_mul,norm_div,hncp,hxcp,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hlog0]
    calc
      _ ≤ (1/(n:ℝ))*Real.log x := mul_le_mul
        (div_le_div_of_nonneg_right (χ.evalNat_norm_le_one n) hn0.le) hlog
        hlog0 (by positivity)
      _ = _ := by ring
  have hH : (∑ n∈lemma82StrictCutoff x, (n:ℝ)⁻¹)≤1+Real.log x := by
    apply le_trans _ (harmonic_floor_le_one_add_log x hx)
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ n∈lemma82StrictCutoff x, Real.log x*(n:ℝ)⁻¹ :=
      (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = Real.log x*(∑ n∈lemma82StrictCutoff x, (n:ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hH hlx

/-- Uniform bound for the genuine residue F on the whole original x range. -/
theorem lemma84_companion_main_bound {D : ℕ} {c : ℝ}
    (hL : 2000≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (μ : ℕ) {x : ℝ} (hx : 1≤x) (hxP : x<lemma23PaperP D) :
    ‖lemma82MainTerm D c j μ x‖≤1+10*Real.pi := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hxp : 0<x := by linarith
  have hs := (lemma82_shift_in_disk hL hc hsmall j μ).1
  have hs' : ‖lemma82SmoothingBeta D μ-lemma82PaperBeta D c j‖≤10*lemma44PaperAlpha D := by
    convert hs using 1 <;> congr 1 <;> ring
  have hlx : Real.log x≤lemma23PaperL D^9 := by
    have hh := Real.log_lt_log hxp hxP
    simpa only [lemma23PaperP,Real.log_exp] using hh.le
  have hα : lemma44PaperAlpha D*lemma23PaperL D^9=Real.pi := by
    rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp,div_mul_cancel₀ _ (pow_ne_zero _ hLp.ne')]
  rw [lemma82MainTerm,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxp,
    lemma82_smoothing_beta_re,Real.rpow_zero,mul_one]
  calc
    _ ≤ 1+‖lemma82SmoothingBeta D μ-lemma82PaperBeta D c j‖*Real.log x := by
      simpa only [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hx)] using norm_add_le (1:ℂ)
          ((lemma82SmoothingBeta D μ-lemma82PaperBeta D c j)*(Real.log x:ℂ))
    _ ≤ 1+(10*lemma44PaperAlpha D)*lemma23PaperL D^9 := by
      have hα0 : 0≤lemma44PaperAlpha D := by rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]; positivity
      exact add_le_add_right (mul_le_mul hs' hlx (Real.log_nonneg hx) (by positivity)) 1
    _ = _ := by rw [mul_assoc,hα]

noncomputable def lemma84CompanionConstant : ℝ :=
  2+16*Real.exp 1*(1+10*Real.pi)+lemma82ErrorConstant

lemma lemma84_companion_constant_pos : 0<lemma84CompanionConstant := by
  unfold lemma84CompanionConstant
  positivity [lemma82_error_constant_pos,Real.pi_pos]

/-- Uniform global estimate for the actual companion sum. The boundary x≤T is
proved separately by the elementary sum, so this theorem has no missing cutoff
layer. The slightly weaker L^3 is deliberate and enough downstream. -/
theorem lemma84_companion_global :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ μ : ℕ, ∀ x : ℝ, 1≤x → x<lemma23PaperP D →
        ‖lemma82ShiftedSum χ c j μ x‖≤lemma84CompanionConstant*lemma23PaperL D^3 := by
  intro c hc
  obtain ⟨D₀,hD02,hth⟩ := lemma82_uniform_threshold c hc
  refine ⟨D₀,hD02,?_⟩
  intro D hDD χ hA j μ x hx hxP
  obtain ⟨hD2,hL,hsmall,htail⟩ := hth D hDD
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hC : 2≤lemma84CompanionConstant := by
    unfold lemma84CompanionConstant
    have hh : 0≤16*Real.exp 1*(1+10*Real.pi) := by positivity
    linarith [lemma82_error_constant_pos]
  by_cases hxT : x≤lemma56PaperT D
  · have hlx : Real.log x≤lemma23PaperL D^(3/2:ℝ) := by
      calc
        _ ≤ Real.log (lemma56PaperT D) := Real.log_le_log (by linarith) hxT
        _ = lemma23PaperL D^(11/10:ℝ) := by rw [lemma56PaperT,Real.log_exp]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hp : 1≤lemma23PaperL D^(3/2:ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hsq : (lemma23PaperL D^(3/2:ℝ))^2=lemma23PaperL D^3 := by
      rw [←Real.rpow_natCast (lemma23PaperL D^(3/2:ℝ)) 2,←Real.rpow_mul hLp.le]
      norm_num only [Nat.cast_ofNat,show (3/2:ℝ)*2=3 by norm_num]
      exact Real.rpow_natCast _ 3
    apply (lemma84_companion_elementary χ c j μ hx).trans
    have hh : Real.log x*(1+Real.log x)≤2*lemma23PaperL D^3 := by
      rw [←hsq]
      nlinarith [Real.log_nonneg hx]
    exact hh.trans (mul_le_mul_of_nonneg_right hC (by positivity))
  · have herr := lemma82_at_parameters χ (by omega) hL hA hc hsmall hx hxP
      (htail x (lt_of_not_ge hxT)) j μ
    have hf := lemma84_companion_main_bound hL hc hsmall j μ hx hxP
    have hd : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
      lemma32_actual_first_derivative_bound χ (by omega) (by change 2≤lemma23PaperL D; linarith) (by simp; positivity)
    have hnorm : ‖lemma82ShiftedSum χ c j μ x‖≤
        lemma82ErrorConstant*lemma23PaperL D^(-6:ℤ)+
        (16*Real.exp 1*lemma23PaperL D^2)*(1+10*Real.pi) := by
      calc
        _ = ‖(lemma82ShiftedSum χ c j μ x-LDerivAtOne χ*lemma82MainTerm D c j μ x)+
            LDerivAtOne χ*lemma82MainTerm D c j μ x‖ := by congr 1; ring
        _ ≤ ‖lemma82ShiftedSum χ c j μ x-LDerivAtOne χ*lemma82MainTerm D c j μ x‖+
            ‖LDerivAtOne χ*lemma82MainTerm D c j μ x‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_mul]; exact add_le_add herr (mul_le_mul hd hf (norm_nonneg _) (by positivity))
    have hp2 : lemma23PaperL D^2≤lemma23PaperL D^3 := pow_le_pow_right₀ hL1 (by omega)
    have hpn : lemma23PaperL D^(-6:ℤ)≤lemma23PaperL D^3 := by
      exact_mod_cast zpow_le_zpow_right₀ hL1 (show (-6:ℤ)≤3 by norm_num)
    apply hnorm.trans
    have h1 := mul_le_mul_of_nonneg_left hpn lemma82_error_constant_pos.le
    have h2 := mul_le_mul_of_nonneg_left hp2 (show 0≤16*Real.exp 1*(1+10*Real.pi) by positivity)
    unfold lemma84CompanionConstant
    nlinarith [pow_nonneg hLp.le 3]

end ZhangLS.Spec
