import ZhangLS.Spec.Lemma61HorizontalKernel

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_actual_shifted_L_positive_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20)
    (hz : 1 / 4 ≤ (s + w).re) :
    ‖DirichletCharacter.LFunction ψ (s + w)‖ ≤
      128 * lemma23PaperP D * lemma23PaperL D ^ 519 := by
  have hn := (lemma61_shifted_argument_norm_bounds hL hs hwr hwi).1
  have hp := lemma61_family_modulus_bound ψ hL hψ
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have ht := lemma61_actual_L_quarter_plane_bound ψ (lemma61_family_nonprincipal ψ hψ) hz
  apply ht.trans
  calc
    _ ≤ (4 * (2 * lemma23PaperP D)) * (16 * lemma23PaperL D ^ 519) := by
      gcongr <;> positivity
    _ = _ := by ring

lemma lemma61_actual_shifted_L_dual_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20)
    (hz : (s + w).re < 1 / 4) :
    ‖DirichletCharacter.LFunction ψ⁻¹ (1 - (s + w))‖ ≤
      136 * lemma23PaperP D * lemma23PaperL D ^ 519 := by
  have hn := (lemma61_shifted_argument_norm_bounds hL hs hwr hwi).2
  have hp := lemma61_family_modulus_bound ψ hL hψ
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hne : ψ⁻¹ ≠ 1 := inv_ne_one.mpr (lemma61_family_nonprincipal ψ hψ)
  have hre : 1 / 4 ≤ (1 - (s + w)).re := by simp only [sub_re,one_re]; linarith only [hz]
  have ht := lemma61_actual_L_quarter_plane_bound ψ⁻¹ hne hre
  apply ht.trans
  calc
    _ ≤ (4 * (2 * lemma23PaperP D)) * (17 * lemma23PaperL D ^ 519) := by
      gcongr <;> positivity
    _ = _ := by ring

lemma lemma61_actual_positive_L_P4_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20)
    (hz : 1 / 4 ≤ (s + w).re) :
    ‖DirichletCharacter.LFunction ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤
      128 * lemma23PaperL D ^ 519 * Real.exp (5 * lemma23PaperL D ^ 9) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  rw [norm_mul]
  calc
    _ ≤ (128 * lemma23PaperP D * lemma23PaperL D ^ 519) *
        Real.exp (4 * lemma23PaperL D ^ 9) :=
      mul_le_mul (lemma61_actual_shifted_L_positive_bound ψ hψ hL hs hwr hwi hz)
        (lemma61_P4_exponential_rectangle_bound hL hwr.2) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [lemma23PaperP,show 5 * lemma23PaperL D ^ 9 =
        lemma23PaperL D ^ 9 + 4 * lemma23PaperL D ^ 9 by ring,Real.exp_add]
      ring

lemma lemma61_actual_negative_L_P4_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20)
    (hz : (s + w).re < 1 / 4) :
    ‖DirichletCharacter.LFunction ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤
      136 * Real.exp (1 + 4 * Real.pi) * lemma23PaperL D ^ 519 *
        Real.exp (3 * lemma23PaperL D ^ 9) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ (by linarith)
  have hwide : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2 :=
    ⟨by linarith only [hwr.1,h9],hwr.2⟩
  have hd := lemma61_large_shift_rectangle_bounds hL hs hwide hwi
  have him : 0 < (s + w).im := by linarith only [(lemma61_wide_height_data hL hd.2.1).2.1]
  have hz' := (lemma61_actual_Z_P4_cancellation ψ hψ hL hs hwide hwi).trans
    (mul_le_mul_of_nonneg_left (lemma61_T_left_rectangle_exponential_bound hL hwr.1) (Real.exp_nonneg _))
  have hd' := lemma61_actual_shifted_L_dual_bound ψ hψ hL hs hwr hwi hz
  calc
    _ = ‖lemma23DirichletZ ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ *
        ‖DirichletCharacter.LFunction ψ⁻¹ (1 - (s + w))‖ := by
      rw [lemma61_actual_single_functional_equation ψ hψ him]
      simp only [norm_mul]; ring
    _ ≤ (Real.exp (1 + 4 * Real.pi) * Real.exp (2 * lemma23PaperL D ^ 9)) *
        (136 * lemma23PaperP D * lemma23PaperL D ^ 519) :=
      mul_le_mul hz' hd' (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [lemma23PaperP,show 3 * lemma23PaperL D ^ 9 =
        2 * lemma23PaperL D ^ 9 + lemma23PaperL D ^ 9 by ring]
      simp only [Real.exp_add]
      ring

lemma lemma61_actual_L_P4_rectangle_bound {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    (hL : 3 ≤ lemma23PaperL D) {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20) :
    ‖DirichletCharacter.LFunction ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤
      136 * Real.exp (1 + 4 * Real.pi) * lemma23PaperL D ^ 519 *
        Real.exp (5 * lemma23PaperL D ^ 9) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hA : 1 ≤ Real.exp (1 + 4 * Real.pi) := Real.one_le_exp_iff.mpr (by positivity)
  by_cases hz : 1 / 4 ≤ (s + w).re
  · apply (lemma61_actual_positive_L_P4_bound ψ hψ hL hs hwr hwi hz).trans
    have hcoeff : (128 : ℝ) ≤ 136 * Real.exp (1 + 4 * Real.pi) := by linarith only [hA]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0.le 519))
      (Real.exp_nonneg _)
  · apply (lemma61_actual_negative_L_P4_bound ψ hψ hL hs hwr hwi (lt_of_not_ge hz)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith only [pow_nonneg h0.le 9])

end ZhangLS.Spec
