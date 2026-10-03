import ZhangLS.Spec.Lemma151ActualWeightedEulerBudget
import ZhangLS.Spec.Lemma151ActualWeightedPrefix
import ZhangLS.Spec.Lemma153PaperParameters
import ZhangLS.Spec.Lemma34TupleConvolution

/-! Quantitative weighted finite prefixes for the actual Section 15 varpi.
This package estimates prefixes only. It does not assert the separate smooth
Rankin tail truncation in (15.20) or deletion of N(Q) after (15.22). -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical

noncomputable def actual151WeightedPrefixConstant : ℝ :=
  16*Real.exp 1*actual151WeightedEulerConstant

lemma actual151_weighted_prefix_constant_pos : 0<actual151WeightedPrefixConstant := by
  unfold actual151WeightedPrefixConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) actual151_weighted_euler_constant_pos

/-- The actual coefficient has a fourth-logarithmic absolute prefix bound,
with no smoothness restriction needed and with every original local factor. -/
theorem actual151_actual_coefficient_prefix_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (hL : 1≤lemma23PaperL D)
    (S : Finset ℕ) (hS : ∀ n∈S,0<n ∧ (n:ℝ)≤lemma56PaperT D) :
    (∑ n∈S,‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) n‖/(n:ℝ))≤
      actual151WeightedPrefixConstant*lemma23PaperL D^(22/5:ℝ) := by
  have hT : 1<lemma56PaperT D := by
    unfold lemma56PaperT
    apply Real.one_lt_exp_iff.mpr
    exact Real.rpow_pos_of_pos (by linarith : 0<lemma23PaperL D) _
  have hlog : Real.log (lemma56PaperT D)=lemma23PaperL D^(11/10:ℝ) := by
    simp only [lemma56PaperT,Real.log_exp]
  have hσ := actual151_rankin_sigma_gt_one hT
  have hs : Summable (fun n : ℕ =>
      ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) n‖/
        (n:ℝ)^(1+1/Real.log (lemma56PaperT D))) :=
    actual151_abs_real_series_summable _ (by linarith)
      (lemma153_actual_lseries_summable χ β γ hpar hM _ (by simpa using hσ))
  simpa only [actual151WeightedPrefixConstant] using
    actual151_finite_prefix_L_22_5_of_zeta
      (fun n => ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) n‖)
      hT hL hlog actual151_weighted_euler_constant_pos.le (fun _ => norm_nonneg _) S hS hs
      (actual151_weighted_abs_real_series_bound χ β γ hpar hM _ hσ)

/-- Character-retaining varpi/divisor weight, exactly the weight needed when
summing the repaired pointwise Lemma 15.1 error over the small factor n1. -/
theorem actual151_actual_varpi_weight_prefix_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2→ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ)≠0) (hL : 1≤lemma23PaperL D)
    (S : Finset ℕ) (hS : ∀ n∈S,0<n ∧ (n:ℝ)≤lemma56PaperT D) :
    (∑ n∈S,‖χ.evalNat n‖*(n.divisors.card:ℝ)*
      ‖lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) n‖/(n:ℝ))≤
      actual151WeightedPrefixConstant*lemma23PaperL D^(22/5:ℝ) := by
  simpa only [lemma153Coefficient,norm_mul,Complex.norm_natCast,
    lemma34_tau2_eq_divisor_card] using
    actual151_actual_coefficient_prefix_bound χ β γ hpar hM hL S hS

/-- All actual paper shifts satisfy the prefix estimate after one common
modulus threshold, independent of character and the three shift indices. -/
theorem actual151_actual_paper_varpi_prefix (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ,∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,∀ j : Fin 3,
      ∀ S : Finset ℕ,(∀ n∈S,0<n ∧ (n:ℝ)≤lemma56PaperT D) →
      (∑ n∈S,‖χ.evalNat n‖*(n.divisors.card:ℝ)*
        ‖lemma153Varpi χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)
          (lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c)) n‖/(n:ℝ))≤
        actual151WeightedPrefixConstant*lemma23PaperL D^(22/5:ℝ) := by
  obtain ⟨D₁,hD₁,hpar⟩ := lemma153_small_parameters_threshold hc
  obtain ⟨D₂,hD₂,hM⟩ := lemma153_normalization_nonzero_threshold hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨D₃,hL⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨max D₁ (max D₂ D₃),?_⟩
  intro D hD χ j S hS
  have h1 : D₁≤D := (le_max_left _ _).trans hD
  have h2 : D₂≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have h3 : D₃≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  exact actual151_actual_varpi_weight_prefix_bound χ _ _ (hpar D h1 j) (hM D h2 χ j)
    (hL D h3) S hS

/-- The pointwise L^-7.9 scale survives this exact weighted prefix with the
stronger L^-3.5 saving; the normalization M is handled separately. -/
theorem actual151_weighted_prefix_error_scale {L E : ℝ} (hL : 1≤L) :
    (E*L^(-79/10:ℝ))*(actual151WeightedPrefixConstant*L^(22/5:ℝ)) =
      (E*actual151WeightedPrefixConstant)*L^(-7/2:ℝ) := by
  have hL0 : 0<L := by linarith
  calc
    _ = (E*actual151WeightedPrefixConstant)*(L^(-79/10:ℝ)*L^(22/5:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hL0]; norm_num

end ZhangLS.Spec
