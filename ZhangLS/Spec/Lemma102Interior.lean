import ZhangLS.Spec.Lemma102UnshiftedEstimates
import ZhangLS.Spec.Lemma102MainAlgebra
import ZhangLS.Spec.Lemma84Section8Cutoffs
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Topology
set_option maxHeartbeats 3000000

/-- Actual tent-weighted ξ estimates in all three interior ranges. The
arithmetic Π loss is displayed; this is not the original uniform L⁻¹⁵ target.
The cutoff dr=P^a/T is included using the closed unshifted Perron transfer. -/
theorem lemma102_genuine_interior_error_with_pi :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3, ∀ d r : ℕ, 0<d → 0<r →
      let E := 2000*(2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖)*lemma23PaperL D^(-15:ℤ)
      ((d*r:ℝ)≤lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D →
        ‖lemma102Sum χ c j d r-lemma102MainInitial χ c j d r‖≤E) ∧
      (lemma23PaperP D^(1/2:ℝ)<(d*r:ℝ) →
        (d*r:ℝ)≤lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D →
        ‖lemma102Sum χ c j d r-lemma102MainLower χ c j d r‖≤E) ∧
      (lemma23PaperP D^(251/500:ℝ)<(d*r:ℝ) →
        (d*r:ℝ)≤lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D →
        ‖lemma102Sum χ c j d r-lemma102MainUpper χ c j d r‖≤E) := by
  intro c hc
  obtain ⟨N,hN,hpoint⟩ := lemma102_unshifted_error_with_pi c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      N≤D ∧ 2≤D ∧ 2000≤lemma23PaperL D ∧
      lemma23PaperP D^(63/125:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) from by
    filter_upwards [eventually_ge_atTop N,lemma84_section8_cutoffs_eventually,
      ht.eventually_ge_atTop 2000] with D hN hcut hL
    exact ⟨hN,hcut.1,hL,by simpa [lemma84Section8Cutoff,lemma84Section8P1] using (hcut.2.2 6).2.1⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.1,?_⟩
  intro D hDD χ hA j d r hd hr
  dsimp only
  obtain ⟨hND,hD2,hL,hPcut⟩ := hD₀ D hDD
  have hD : 1<D := by omega
  have hLp : 0< lemma23PaperL D := by linarith
  have hy : (0:ℝ)<d*r := by positivity
  have hy1 : (1:ℝ)≤d*r := by exact_mod_cast Nat.mul_pos hd hr
  have hT1 := (lemma101_T_gt_one hD).le
  have hP1 := (lemma101_P_gt_one hD).le
  let B := 2+lemma84TaylorCircleConstant*‖lemma83Pi χ d r‖
  have hB : 0≤B := by dsimp [B]; positivity [lemma84_circle_constants_pos.1]
  have hlarge {a : ℝ} (ha : a≤63/125)
      (hupper : (d*r:ℝ)≤lemma23PaperP D^a/lemma56PaperT D) :
      (d*r:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) := by
    have hh : (d*r:ℝ)≤lemma23PaperP D^(63/125:ℝ) :=
      hupper.trans ((div_le_self (Real.rpow_nonneg (Real.exp_pos _).le _) hT1).trans
        (Real.rpow_le_rpow_of_exponent_le hP1 ha))
    exact hh.trans_lt hPcut
  have hbound {a t : ℝ} (ha : a<1) (hat : t≤a)
      (hupper : (d*r:ℝ)≤lemma23PaperP D^t/lemma56PaperT D)
      (hcut : (d*r:ℝ)<lemma23PaperP D*lemma56PaperT D^(-2:ℤ)) :
      ‖lemma102LogSum χ c j d r (lemma101Cutoff D (d*r:ℝ) a)-
        LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j (lemma101Cutoff D (d*r:ℝ) a)‖≤
          B*lemma23PaperL D^(-6:ℤ) := by
    exact hpoint D hND χ hA j d r hd hr hcut _
      ((lemma101_cutoff_ge_T hy hupper).trans (lemma101_cutoff_mono hD hy hat))
      (lemma101_cutoff_lt_P hD hy1 ha)
  have hscale (z : ℂ) (hz : ‖z‖≤4*(B*lemma23PaperL D^(-6:ℤ))) :
      ‖(500/(Real.log (lemma23PaperP D):ℂ))*z‖≤
        2000*B*lemma23PaperL D^(-15:ℤ) := by
    have hh := lemma102_scale_error hLp z (E:=4*B) (by nlinarith only [hz])
    exact hh.trans_eq (by ring)
  refine ⟨?_,?_,?_⟩
  · intro hupper
    have hcut := hlarge (by norm_num : (1/2:ℝ)≤63/125) hupper
    have h₁ := hbound (by norm_num : (63/125:ℝ)<1) (by norm_num : (1/2:ℝ)≤63/125) hupper hcut
    have h₂ := hbound (by norm_num : (251/500:ℝ)<1) (by norm_num : (1/2:ℝ)≤251/500) hupper hcut
    have h₃ := hbound (by norm_num : (1/2:ℝ)<1) le_rfl hupper hcut
    rw [lemma102_sum_exact_bridge χ hD c j d r hd hr,
      ←lemma102_initial_main_identity χ hD c j d r hd hr,←mul_sub]
    exact hscale _ (lemma102_second_difference_norm _ _ _ _ _ _ h₁ h₂ h₃)
  · intro hlower hupper
    have hcut := hlarge (by norm_num : (251/500:ℝ)≤63/125) hupper
    have h₁ := hbound (by norm_num : (63/125:ℝ)<1) (by norm_num : (251/500:ℝ)≤63/125) hupper hcut
    have h₂ := hbound (by norm_num : (251/500:ℝ)<1) le_rfl hupper hcut
    have hzero := lemma102_log_sum_zero_of_le_one χ c j d r
      (lemma101_cutoff_pos D hy (1/2)) (lemma101_cutoff_le_one hy hlower.le)
    rw [lemma102_sum_exact_bridge χ hD c j d r hd hr,hzero,add_zero,
      ←lemma102_lower_main_identity χ c j d r hd hr,←mul_sub]
    exact hscale _ (lemma102_two_term_norm _ _ _ _ (by positivity) h₁ h₂)
  · intro hlower hupper
    have hcut := hlarge le_rfl hupper
    have h₁ := hbound (by norm_num : (63/125:ℝ)<1) le_rfl hupper hcut
    have hzero₂ := lemma102_log_sum_zero_of_le_one χ c j d r
      (lemma101_cutoff_pos D hy (251/500)) (lemma101_cutoff_le_one hy hlower.le)
    have hzero₃ := lemma102_log_sum_zero_of_le_one χ c j d r
      (lemma101_cutoff_pos D hy (1/2)) (lemma101_cutoff_le_one hy
        ((lemma101_half_power_le_power hD (by norm_num : (1/2:ℝ)≤251/500)).trans hlower.le))
    rw [lemma102_sum_exact_bridge χ hD c j d r hd hr,hzero₂,hzero₃,mul_zero,sub_zero,add_zero,
      ←lemma102_upper_main_identity χ c j d r,←mul_sub]
    apply hscale
    nlinarith only [h₁,mul_nonneg hB (show 0≤lemma23PaperL D^(-6:ℤ) by positivity)]

end ZhangLS.Spec
