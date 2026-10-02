import ZhangLS.Spec.Lemma153DownstreamResidue
import ZhangLS.Spec.PaperErrorScaleBudget

/-! Quantitative bounds on the actual shifted residue, preserving the thin-strip
polylogarithmic dependence. These are local analytic facts, not contour or
sharp-cutoff claims. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 2000000

noncomputable def lemma153ResidueRadius (D : ℕ) : ℝ :=
  1/(8*lemma23PaperL D^(11/10 : ℝ))
noncomputable def lemma153LocalUBound (D : ℕ) : ℝ :=
  lemma153StripConstant*(1+Real.log (lemma23PaperL D))^18
noncomputable def lemma153LocalPrefactorBound (D : ℕ) : ℝ :=
  64*Real.exp 1*lemma153LocalUBound D

lemma lemma153_residue_radius_properties {D : ℕ} (hL : 2≤lemma23PaperL D) :
    0<lemma153ResidueRadius D ∧ lemma153ResidueRadius D≤1/8 ∧
      lemma153ResidueRadius D≤(lemma23PaperL D)⁻¹ ∧
      lemma23PaperL D^(11/10 : ℝ)*lemma153ResidueRadius D=1/8 := by
  let L := lemma23PaperL D
  have hL0 : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have ht0 : 0<L^(11/10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have ht1 : 1≤L^(11/10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hLt : L≤L^(11/10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1:ℝ)≤11/10)
  change 0<1/(8*L^(11/10 : ℝ)) ∧ _
  refine ⟨by positivity,?_,?_,?_⟩
  · change 1/(8*L^(11/10 : ℝ))≤1/8
    apply (div_le_iff₀ (by positivity : 0<8*L^(11/10 : ℝ))).mpr
    linarith
  · change 1/(8*L^(11/10 : ℝ))≤L⁻¹
    rw [← one_div]
    apply one_div_le_one_div_of_le hL0
    linarith
  · change L^(11/10 : ℝ)*(1/(8*L^(11/10 : ℝ)))=1/8
    field_simp

lemma lemma153_local_U_bound_nonneg (D : ℕ) : 0≤lemma153LocalUBound D := by
  unfold lemma153LocalUBound
  exact mul_nonneg lemma153_strip_constant_pos.le (by positivity)

lemma lemma153_local_prefactor_bound_nonneg (D : ℕ) : 0≤lemma153LocalPrefactorBound D := by
  unfold lemma153LocalPrefactorBound
  exact mul_nonneg (by positivity) (lemma153_local_U_bound_nonneg D)

lemma lemma153_U_bound_le_prefactor_bound (D : ℕ) :
    lemma153LocalUBound D≤lemma153LocalPrefactorBound D := by
  have he : 1≤Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold lemma153LocalPrefactorBound
  nlinarith [lemma153_local_U_bound_nonneg D]

lemma lemma153_gaussian_factor_residue_bound {D : ℕ} (hL : 2≤lemma23PaperL D)
    (w : ℂ) (hw : ‖w‖≤lemma153ResidueRadius D) :
    ‖lemma171GaussianMellinFactor D w‖≤Real.exp 1 := by
  let L := lemma23PaperL D
  have hL0 : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hR := lemma153_residue_radius_properties hL
  have ht0 : 0≤L^(11/10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlin : ‖((L^(11/10 : ℝ) : ℝ) : ℂ)*w‖≤1/8 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hw ht0).trans hR.2.2.2.le
  have hden : ‖(4 : ℂ)*(L : ℂ)^30‖=4*L^30 := by
    simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  have hquad : ‖w^2/((4 : ℂ)*(L : ℂ)^30)‖≤1/4 := by
    rw [norm_div,norm_pow,hden]
    apply (div_le_iff₀ (by positivity : 0<4*L^30)).mpr
    have hw1 : ‖w‖≤1 := hw.trans (hR.2.1.trans (by norm_num))
    have hs : ‖w‖^2≤1 := pow_le_one₀ (norm_nonneg _) hw1
    have h30 : 1≤L^30 := one_le_pow₀ hL1
    nlinarith
  unfold lemma171GaussianMellinFactor
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  change ((((L^(11/10 : ℝ) : ℝ) : ℂ)*w)+w^2/((4 : ℂ)*(L : ℂ)^30)).re≤1
  have hr := Complex.re_le_norm (((L^(11/10 : ℝ) : ℝ) : ℂ)*w+w^2/((4 : ℂ)*(L : ℂ)^30))
  have hn := norm_add_le ((((L^(11/10 : ℝ) : ℝ) : ℂ)*w)) (w^2/((4 : ℂ)*(L : ℂ)^30))
  linarith

lemma lemma153_actual_U_local_bound {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (w : ℂ) (hw : ‖w‖≤lemma153ResidueRadius D) :
    ‖lemma153EulerProduct χ β γ (1+w)‖≤lemma153LocalUBound D := by
  have hR := lemma153_residue_radius_properties hL
  have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
  have hre : 3/4≤(1+w).re := by simp only [Complex.add_re,Complex.one_re]; linarith [hR.2.1]
  have hstrip : 1-(Real.log D)⁻¹≤(1+w).re := by
    simp only [Complex.add_re,Complex.one_re]
    change 1-(lemma23PaperL D)⁻¹≤1+w.re
    linarith [hR.2.2.1]
  exact lemma153_euler_product_strip_bound hD χ β γ hpar (1+w) hre hstrip

lemma lemma153_actual_prefactor_local_bound {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (w : ℂ) (hw : ‖w‖≤lemma153ResidueRadius D) :
    ‖lemma153ResiduePrefactor χ β γ w‖≤lemma153LocalPrefactorBound D := by
  have hu := lemma153_actual_U_local_bound hD χ hL β γ hpar w hw
  have hz := lemma32_zeta_pole_removed_local_bound (1+w) (by
    simpa using hw.trans ((lemma153_residue_radius_properties hL).2.1.trans (by norm_num : (1:ℝ)/8≤1/4)))
  have hg := lemma153_gaussian_factor_residue_bound hL w hw
  have hK := lemma153_local_U_bound_nonneg D
  unfold lemma153ResiduePrefactor lemma153LocalPrefactorBound
  rw [norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ lemma153LocalUBound D*8^2*Real.exp 1 := by gcongr
    _ = _ := by ring

lemma lemma153_actual_prefactor_diffContOnCl {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) :
    DiffContOnCl ℂ (lemma153ResiduePrefactor χ β γ) (ball 0 (lemma153ResidueRadius D)) := by
  have hd : DifferentiableOn ℂ (lemma153ResiduePrefactor χ β γ) (closedBall 0 (lemma153ResidueRadius D)) := by
    intro w hw
    have hn : ‖w‖≤lemma153ResidueRadius D := by simpa [mem_closedBall,dist_eq_norm] using hw
    have hb := (abs_le.mp ((Complex.abs_re_le_norm w).trans
      (hn.trans (lemma153_residue_radius_properties hL).2.1))).1
    exact (lemma153_residue_prefactor_differentiableAt (by omega) χ β γ hpar w (by linarith)).differentiableWithinAt
  exact hd.diffContOnCl_ball subset_rfl

lemma lemma153_actual_prefactor_first_derivative_bound {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) :
    ‖deriv (lemma153ResiduePrefactor χ β γ) 0‖≤
      8*lemma23PaperL D^(11/10 : ℝ)*lemma153LocalPrefactorBound D := by
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (lemma153_residue_radius_properties hL).1 (lemma153_actual_prefactor_diffContOnCl hD χ hL β γ hpar)
    (fun w hw => lemma153_actual_prefactor_local_bound hD χ hL β γ hpar w (by
      exact le_of_eq (by simpa [mem_sphere,dist_eq_norm] using hw)))
  calc
    _ ≤ lemma153LocalPrefactorBound D/lemma153ResidueRadius D := hc
    _ = _ := by unfold lemma153ResidueRadius; field_simp

lemma lemma153_actual_prefactor_second_derivative_bound {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (hL : 2≤lemma23PaperL D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) :
    ‖iteratedDeriv 2 (lemma153ResiduePrefactor χ β γ) 0‖≤
      128*(lemma23PaperL D^(11/10 : ℝ))^2*lemma153LocalPrefactorBound D := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 (lemma153_residue_radius_properties hL).1 (lemma153_actual_prefactor_diffContOnCl hD χ hL β γ hpar)
    (fun w hw => lemma153_actual_prefactor_local_bound hD χ hL β γ hpar w (by
      exact le_of_eq (by simpa [mem_sphere,dist_eq_norm] using hw)))
  calc
    _ ≤ 2*lemma153LocalPrefactorBound D/lemma153ResidueRadius D^2 := by
      simpa [Nat.factorial] using hc
    _ = _ := by unfold lemma153ResidueRadius; field_simp; ring

end ZhangLS.Spec
