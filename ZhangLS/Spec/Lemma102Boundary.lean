import ZhangLS.Spec.Lemma102Interior
import ZhangLS.Spec.Lemma102BoundaryPerron
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Topology
set_option maxHeartbeats 2000000

noncomputable def lemma102LogMainBound : ℝ := 1+6*Real.pi+(9/2)*Real.pi^2

lemma lemma102_log_main_bound_pos : 0<lemma102LogMainBound := by
  unfold lemma102LogMainBound
  positivity

lemma lemma102_log_main_bound {D : ℕ} (hL : 100≤lemma23PaperL D)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) {x : ℝ} (hx : 1≤x) (hxP : x<lemma23PaperP D) :
    ‖lemma102LogMain D c j x‖≤lemma102LogMainBound := by
  have hLp : 0< lemma23PaperL D := by linarith
  have hα := (lemma83_alpha_small hL).1
  have hb := lemma83_paper_beta_norm (by linarith : 3≤lemma23PaperL D) hc hsmall
  have hx0 : 0<x := by linarith
  have hlog := Real.log_nonneg hx
  have hscale := lemma84_alpha_log_x_le_pi hLp hx0 hxP
  have hlin : ‖(lemma83PaperBeta D c (j+1)+lemma83PaperBeta D c (j+2))*(Real.log x:ℂ)‖≤6*Real.pi := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
    have hb' := (norm_add_le _ _).trans (add_le_add (hb (j+1)) (hb (j+2)))
    have hh := mul_le_mul_of_nonneg_right hb' hlog
    nlinarith only [hh,hscale]
  have hquad : ‖lemma83PaperBeta D c (j+1)*lemma83PaperBeta D c (j+2)/2*(Real.log x:ℂ)^2‖≤
      (9/2)*Real.pi^2 := by
    rw [norm_mul,norm_div,norm_mul,Complex.norm_ofNat,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hlog]
    have hh := mul_le_mul (hb (j+1)) (hb (j+2)) (norm_nonneg _) (by positivity)
    have hh' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤2)) (sq_nonneg (Real.log x))
    have hs := pow_le_pow_left₀ (mul_nonneg hα.le hlog) hscale 2
    nlinarith only [hh',hs]
  unfold lemma102LogMain lemma102LogMainBound
  have hh := (norm_add_le
    (1+(lemma83PaperBeta D c (j+1)+lemma83PaperBeta D c (j+2))*(Real.log x:ℂ))
    (lemma83PaperBeta D c (j+1)*lemma83PaperBeta D c (j+2)/2*(Real.log x:ℂ)^2)).trans
      (add_le_add (norm_add_le (1:ℂ)
        ((lemma83PaperBeta D c (j+1)+lemma83PaperBeta D c (j+2))*(Real.log x:ℂ))) le_rfl)
  simp only [norm_one] at hh
  linarith only [hh,hlin,hquad]

/-- Fully explicit bound used on the three literal transition bands. It is
kept separate from the source O(L⁻⁷) claim, which is not proved here. -/
noncomputable def lemma102BoundaryBound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (d r : ℕ) : ℝ :=
  (2000/lemma23PaperL D^9)*
    (lemma84BoundaryXiConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent*
       (Real.log (lemma56PaperT D))^4 +
     16*Real.exp 1*lemma102LogMainBound*lemma23PaperL D^2*‖lemma83Pi χ d r‖ +
     (2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-6:ℤ))

/-- Real pointwise control of the actual tent sum on every original boundary
band, including the first two upper endpoints and excluding the final one.
This bound retains the true small-x Perron mass and the actual Π factor. -/
theorem lemma102_genuine_boundary_bound :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ d r : ℕ, 0<d → 0<r → Lemma101Transition D (d*r:ℝ) →
        ‖lemma102Sum χ c j d r‖≤lemma102BoundaryBound χ d r := by
  intro c hc
  obtain ⟨N,hN,hpoint⟩ := lemma102_unshifted_error_with_pi c hc
  obtain ⟨Nc,hNc,hsmall⟩ := lemma101_uniform_threshold c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      N≤D ∧ Nc≤D ∧ 2≤D ∧ 2000≤lemma23PaperL D ∧
      lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) from by
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop Nc,lemma84_section8_cutoffs_eventually,
      ht.eventually_ge_atTop 2000] with D hN hNc hcut hL
    exact ⟨hN,hNc,hcut.1,hL,by simpa [lemma84Section8Cutoff,lemma84Section8P1] using (hcut.2.2 6).2.1⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.2.1,?_⟩
  intro D hDD χ hA j d r hd hr hband
  obtain ⟨hND,hNcD,hD2,hL,hPcut⟩ := hD₀ D hDD
  have hD : 1<D := by omega
  have hLp : 0<lemma23PaperL D := by linarith
  have hy : (0:ℝ)<d*r := by positivity
  have hy1 : (1:ℝ)≤d*r := by exact_mod_cast Nat.mul_pos hd hr
  have hupper : (d*r:ℝ)≤lemma23PaperP D^(63/125:ℝ) := by
    rcases hband with ((h|h)|h)
    · exact h.2.trans (Real.rpow_le_rpow_of_exponent_le (lemma101_P_gt_one hD).le (by norm_num))
    · exact h.2.trans (Real.rpow_le_rpow_of_exponent_le (lemma101_P_gt_one hD).le (by norm_num))
    · exact h.2.le
  have hcut := hupper.trans_lt hPcut
  have hcsmall := (hsmall D hNcD).2.2.1
  let X := lemma84BoundaryXiConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent*
    (Real.log (lemma56PaperT D))^4
  let Y := 16*Real.exp 1*lemma102LogMainBound*lemma23PaperL D^2*‖lemma83Pi χ d r‖
  let E := (2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-6:ℤ)
  have hlogL := Real.log_nonneg (by linarith : 1≤lemma23PaperL D)
  have hX : 0≤X := by dsimp [X]; positivity [lemma84_boundary_xi_constant_pos,hlogL]
  have hY : 0≤Y := by dsimp [Y]; positivity [lemma102_log_main_bound_pos]
  have hE : 0≤E := by dsimp [E]; positivity [lemma84_circle_constants_pos.1]
  have hall {x : ℝ} (hx : 0<x) (hxP : x<lemma23PaperP D) :
      ‖lemma102LogSum χ c j d r x‖≤X+Y+E := by
    by_cases hx1 : x≤1
    · rw [lemma102_log_sum_zero_of_le_one χ c j d r hx hx1,norm_zero]
      linarith
    have h1x : 1≤x := (lt_of_not_ge hx1).le
    by_cases hxT : x≤lemma56PaperT D
    · have hh := lemma102_boundary_xi_small_x χ hD (by linarith) c j d r hd hr
        (by simpa only [Nat.cast_mul] using lemma83_paper_cutoff_log (by linarith : 100≤lemma23PaperL D) hd hr hcut) h1x hxT
      exact hh.trans (by change X≤X+Y+E; linarith)
    · have herr := hpoint D hND χ hA j d r hd hr hcut x (lt_of_not_ge hxT).le hxP
      have hg := lemma102_log_main_bound (by linarith : 100≤lemma23PaperL D) hc hcsmall j h1x hxP
      have hd' := lemma84_actual_derivative_norm_upper χ hD (by linarith : 2≤lemma23PaperL D)
      have hm : ‖LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x‖≤Y := by
        rw [norm_mul,norm_mul]
        have hh := mul_le_mul
          (mul_le_mul_of_nonneg_right hd' (norm_nonneg (lemma83Pi χ d r))) hg
          (norm_nonneg (lemma102LogMain D c j x))
          (show 0≤(16*Real.exp 1*lemma23PaperL D^2)*‖lemma83Pi χ d r‖ by positivity)
        exact hh.trans_eq (by dsimp [Y]; ring)
      have hh := norm_sub_le (lemma102LogSum χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x)
        (-(LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x))
      simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hh
      change _≤E at herr
      linarith only [hh,herr,hm,hX]
  have h₁ := hall (lemma101_cutoff_pos D hy (63/125)) (lemma101_cutoff_lt_P hD hy1 (by norm_num : (63/125:ℝ)<1))
  have h₂ := hall (lemma101_cutoff_pos D hy (251/500)) (lemma101_cutoff_lt_P hD hy1 (by norm_num : (251/500:ℝ)<1))
  have h₃ := hall (lemma101_cutoff_pos D hy (1/2)) (lemma101_cutoff_lt_P hD hy1 (by norm_num : (1/2:ℝ)<1))
  have hn := lemma102_second_difference_norm _ _ _ 0 0 0
    (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
  simp only [mul_zero,sub_zero,add_zero] at hn
  rw [← one_div (2:ℝ)] at hn
  rw [lemma102_sum_exact_bridge χ hD c j d r hd hr,norm_mul,lemma101_prefactor_norm hLp]
  apply (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq
  dsimp [lemma102BoundaryBound,X,Y,E]
  ring

end ZhangLS.Spec
