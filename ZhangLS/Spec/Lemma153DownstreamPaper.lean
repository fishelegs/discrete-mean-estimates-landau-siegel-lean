import ZhangLS.Spec.Lemma153DownstreamRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Paper-shift consequences of the genuine local residue reconstruction.
The final theorem is a residue estimate; no sharp finite sum or contour
identity is silently included. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Asymptotics
set_option maxHeartbeats 2000000

lemma lemma153_log_power_eventual_absorption :
    ∀ᶠ L : ℝ in atTop, 2≤L ∧
      (1+Real.log L)^18*L^(-39/10:ℝ)≤(2:ℝ)^18*L^(-3:ℤ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (18:ℝ) (by norm_num : (0:ℝ)<9/10)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,hh] with L hL hlog hbound
  refine ⟨hL,?_⟩
  have hL0 : 0<L := by linarith
  have hp : (Real.log L)^18≤L^(9/10:ℝ) := by
    rw [←Real.rpow_natCast]
    simpa only [Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤Real.log L) _),
      abs_of_nonneg (Real.rpow_nonneg hL0.le _)] using hbound
  have hbase : 1+Real.log L≤2*Real.log L := by linarith
  calc
    _ ≤ (2*Real.log L)^18*L^(-39/10:ℝ) := by gcongr
    _ = (2:ℝ)^18*((Real.log L)^18*L^(-39/10:ℝ)) := by rw [mul_pow]; ring
    _ ≤ (2:ℝ)^18*(L^(9/10:ℝ)*L^(-39/10:ℝ)) := by gcongr
    _ = _ := by
      rw [←Real.rpow_add hL0]
      norm_num

lemma lemma153_paper_log_absorption_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → 2≤lemma23PaperL D ∧
      (1+Real.log (lemma23PaperL D))^18*lemma23PaperL D^(-39/10:ℝ)≤
        (2:ℝ)^18*lemma23PaperL D^(-3:ℤ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually lemma153_log_power_eventual_absorption)

/-- One absolute constant, chosen before the shared shift constant c′. -/
noncomputable def lemma153PaperResidueErrorConstant : ℝ :=
  (2:ℝ)^18*lemma153ResidueRateConstant

lemma lemma153_paper_residue_error_constant_pos : 0<lemma153PaperResidueErrorConstant := by
  unfold lemma153PaperResidueErrorConstant
  exact mul_pos (by positivity) lemma153_residue_rate_constant_pos

/-- The shifted-L repair preserves the originally needed local residue main term
at absolute O(L^-3). This proves no contour-shift or sharp-cutoff statement. -/
theorem lemma153_paper_actual_residue_estimate {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖lemma153ActualResidue χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) -
        lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) 1 *
          LDerivAtOne χ^2‖≤lemma153PaperResidueErrorConstant*lemma23PaperL D^(-3:ℤ) := by
  obtain ⟨D₁,hD1,hpar⟩ := lemma153_small_parameters_threshold hc
  obtain ⟨D₂,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₃,hsection₃,hbudget⟩ := lemma52_exists_shift_threshold (by norm_num : (0:ℝ)<12)
  obtain ⟨D₄,habsorb⟩ := lemma153_paper_log_absorption_threshold
  refine ⟨max 3 (max D₁ (max D₂ (max D₃ D₄))),le_max_left _ _,?_⟩
  intro D hD χ hA j
  have hDthree : 3≤D := (le_max_left _ _).trans hD
  have hD1' : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hD2' : D₂≤D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hD3' : D₃≤D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD)))
  have hD4' : D₄≤D := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD)))
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD2')).1
  have hL0 : 0<lemma23PaperL D := by linarith
  have hγscale := lemma153_paper_beta_norm_le hL hc (hsmall D hD2') j
  have hγ : ‖lemma83PaperBeta D c j‖≤1/(4*lemma23PaperL D) := by
    apply hγscale.trans
    apply (le_div_iff₀ (by positivity : 0<4*lemma23PaperL D)).mpr
    have hh := hbudget D hD3'
    nlinarith only [hh]
  have he := lemma153_actual_shifted_residue_rate hDthree χ (by linarith) hA _ _ (hpar D hD1' j) hγ hγscale
  have hab := (habsorb D hD4').2
  calc
    _ ≤ lemma153ResidueRateConstant*(1+Real.log (lemma23PaperL D))^18*lemma23PaperL D^(-39/10:ℝ) := he
    _ ≤ lemma153ResidueRateConstant*((2:ℝ)^18*lemma23PaperL D^(-3:ℤ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hab lemma153_residue_rate_constant_pos.le
    _ = _ := by unfold lemma153PaperResidueErrorConstant; ring

end ZhangLS.Spec
