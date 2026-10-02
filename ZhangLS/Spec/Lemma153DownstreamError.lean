import ZhangLS.Spec.Lemma153DownstreamBounds
/-! Explicit error budget for the genuine shifted residue. The only arithmetic
smallness input is the paper's original assumption (A), through L(1,χ). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 2000000

lemma lemma153_actual_shifted_residue_error_bound {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (hA : NormalizedAssumptionA χ) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (hγ : ‖γ‖≤1/(4*lemma23PaperL D)) :
    let B := 16*Real.exp 1*lemma23PaperL D^2
    let E := 128*Real.exp 1*lemma23PaperL D^3
    let V := lemma23PaperL D^(-2022 : ℤ)+B*‖γ‖
    let t := lemma23PaperL D^(11/10 : ℝ)
    ‖lemma153ActualResidue χ β γ - lemma153EulerProduct χ β γ 1 * LDerivAtOne χ^2‖ ≤
      lemma153LocalPrefactorBound D*(2*B*E*‖γ‖+V*(E+16*t*B+64*t^2*V)) := by
  dsimp only
  let L := lemma23PaperL D
  let B := 16*Real.exp 1*L^2
  let E := 128*Real.exp 1*L^3
  let V := L^(-2022 : ℤ)+B*‖γ‖
  let t := L^(11/10 : ℝ)
  let F := lemma153LocalPrefactorBound D
  have hL0 : 0<L := by dsimp [L]; linarith
  have hB : 0≤B := by dsimp [B]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have ht : 0≤t := Real.rpow_nonneg hL0.le _
  have hF : 0≤F := lemma153_local_prefactor_bound_nonneg D
  have hD' : 1<D := by omega
  have hs : ‖(1-γ)-1‖≤1/(4*L) := by simpa using hγ
  have hb : ‖deriv (dirichletLFunction χ) (1-γ)‖≤B :=
    lemma32_actual_first_derivative_bound χ hD' hL hs
  have hd : ‖LDerivAtOne χ‖≤B :=
    lemma32_actual_first_derivative_bound χ hD' hL (by simp; positivity)
  have he : ‖deriv (dirichletLFunction χ) (1-γ)-LDerivAtOne χ‖≤E*‖γ‖ := by
    simpa using lemma55_actual_first_derivative_variation χ hD' hL hs
  have hc : ‖iteratedDeriv 2 (dirichletLFunction χ) (1-γ)‖≤E := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      lemma55_actual_second_derivative_bound χ hD' hL hs
  have hv : ‖dirichletLFunction χ (1-γ)‖≤V := by
    have hh := lemma32_actual_L_difference_near_one χ hD' hL hs
    have h1 := lemma32_actual_value_at_one_small χ hD' hA
    calc
      _ ≤ ‖dirichletLFunction χ (1-γ)-LAtOne χ‖+‖LAtOne χ‖ := by
        simpa using norm_add_le (dirichletLFunction χ (1-γ)-LAtOne χ) (LAtOne χ)
      _ ≤ B*‖γ‖+L^(-2022 : ℤ) := by
        simpa only [sub_sub_cancel_left,norm_neg,L,B] using add_le_add hh h1
      _ = V := by dsimp [V]; ring
  have hu : ‖lemma153EulerProduct χ β γ 1‖≤F := by
    have hu := lemma153_actual_U_local_bound hD χ hL β γ hpar 0 (by
      simpa using (lemma153_residue_radius_properties hL).1.le)
    have hu' : ‖lemma153EulerProduct χ β γ 1‖≤lemma153LocalUBound D := by simpa using hu
    exact hu'.trans (lemma153_U_bound_le_prefactor_bound D)
  have hp1 : ‖deriv (lemma153ResiduePrefactor χ β γ) 0‖≤8*t*F :=
    lemma153_actual_prefactor_first_derivative_bound hD χ hL β γ hpar
  have hp2 : ‖iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0‖≤128*t^2*F :=
    lemma153_actual_prefactor_second_derivative_bound hD χ hL β γ hpar
  have hsq : ‖(deriv (dirichletLFunction χ) (1-γ))^2-LDerivAtOne χ^2‖≤2*B*E*‖γ‖ := by
    rw [show (deriv (dirichletLFunction χ) (1-γ))^2-LDerivAtOne χ^2=
      (deriv (dirichletLFunction χ) (1-γ)-LDerivAtOne χ)*
        (deriv (dirichletLFunction χ) (1-γ)+LDerivAtOne χ) by ring,norm_mul]
    have hsum : ‖deriv (dirichletLFunction χ) (1-γ)+LDerivAtOne χ‖≤2*B :=
      (norm_add_le _ _).trans (by linarith)
    calc
      _ ≤ (E*‖γ‖)*(2*B) := by gcongr
      _ = _ := by ring
  have hinner : ‖lemma153EulerProduct χ β γ 1*iteratedDeriv 2 (dirichletLFunction χ) (1-γ)+
      2*deriv (lemma153ResiduePrefactor χ β γ) 0*deriv (dirichletLFunction χ) (1-γ)+
      iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0*dirichletLFunction χ (1-γ)/2‖≤
      F*(E+16*t*B+64*t^2*V) := by
    calc
      _ ≤ ‖lemma153EulerProduct χ β γ 1*iteratedDeriv 2 (dirichletLFunction χ) (1-γ)‖+
        ‖2*deriv (lemma153ResiduePrefactor χ β γ) 0*deriv (dirichletLFunction χ) (1-γ)‖+
        ‖iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0*dirichletLFunction χ (1-γ)/2‖ := norm_add₃_le
      _ ≤ F*E+2*(8*t*F)*B+(128*t^2*F)*V/2 := by
        simp only [norm_mul,norm_div,norm_ofNat]
        gcongr
      _ = _ := by ring
  rw [lemma153_actual_residue_decomposition χ hD' β γ hpar]
  rw [show lemma153EulerProduct χ β γ 1*(deriv (dirichletLFunction χ) (1-γ))^2+
      dirichletLFunction χ (1-γ)*
        (lemma153EulerProduct χ β γ 1*iteratedDeriv 2 (dirichletLFunction χ) (1-γ)+
          2*deriv (lemma153ResiduePrefactor χ β γ) 0*deriv (dirichletLFunction χ) (1-γ)+
          iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0*dirichletLFunction χ (1-γ)/2)-
        lemma153EulerProduct χ β γ 1*LDerivAtOne χ^2 =
      lemma153EulerProduct χ β γ 1*((deriv (dirichletLFunction χ) (1-γ))^2-LDerivAtOne χ^2)+
      dirichletLFunction χ (1-γ)*
        (lemma153EulerProduct χ β γ 1*iteratedDeriv 2 (dirichletLFunction χ) (1-γ)+
          2*deriv (lemma153ResiduePrefactor χ β γ) 0*deriv (dirichletLFunction χ) (1-γ)+
          iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0*dirichletLFunction χ (1-γ)/2) by ring]
  calc
    _ ≤ ‖lemma153EulerProduct χ β γ 1*((deriv (dirichletLFunction χ) (1-γ))^2-LDerivAtOne χ^2)‖+
      ‖dirichletLFunction χ (1-γ)*
        (lemma153EulerProduct χ β γ 1*iteratedDeriv 2 (dirichletLFunction χ) (1-γ)+
          2*deriv (lemma153ResiduePrefactor χ β γ) 0*deriv (dirichletLFunction χ) (1-γ)+
          iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0*dirichletLFunction χ (1-γ)/2)‖ := norm_add_le _ _
    _ ≤ F*(2*B*E*‖γ‖)+V*(F*(E+16*t*B+64*t^2*V)) := by
      simp only [norm_mul]
      gcongr
    _ = _ := by change _=F*(2*B*E*‖γ‖+V*(E+16*t*B+64*t^2*V)); ring

end ZhangLS.Spec
