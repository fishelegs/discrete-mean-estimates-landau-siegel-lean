import ZhangLS.Spec.Lemma153CenterProductComparison
/-! Fixed-neighborhood and original-paper-shift consequences of the repaired
center perturbation.  Only numerical hypotheses on the actual shifts remain;
the paper-level theorem discharges all of them beyond one modulus threshold. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

/-- An explicit absolute neighborhood, independent of the modulus and character. -/
noncomputable def lemma153CenterShiftRadius : ℝ :=
  min (1/10) (1/(60*lemma152CorrectionConstant))

lemma lemma153_center_shift_radius_pos : 0 < lemma153CenterShiftRadius := by
  have := lemma152_correction_constant_pos
  unfold lemma153CenterShiftRadius
  positivity

lemma lemma153_small_parameters_of_radius (β : Fin 2 → ℂ) (γ : ℂ)
    (hβre : ∀ i, (β i).re = 0) (hγre : γ.re = 0)
    (hβ : ∀ i, ‖β i‖ ≤ lemma153CenterShiftRadius)
    (hγ : ‖γ‖ ≤ lemma153CenterShiftRadius) : Lemma153SmallParameters β γ := by
  have hC := lemma152_correction_constant_pos
  have hr1 : lemma153CenterShiftRadius ≤ 1/10 := min_le_left _ _
  have hr2 : lemma153CenterShiftRadius ≤ 1/(60*lemma152CorrectionConstant) := min_le_right _ _
  refine ⟨hβre,fun i => (hβ i).trans hr1,hγre,hγ.trans hr1,?_⟩
  have hb0 := (hβ 0).trans hr2
  have hb1 := (hβ 1).trans hr2
  have hgg := hγ.trans hr2
  have hden : 0 < 60*lemma152CorrectionConstant := by positivity
  have he : 10*lemma152CorrectionConstant*(3*(1/(60*lemma152CorrectionConstant))) = 1/2 := by
    field_simp
    <;> ring
  calc
    _ ≤ 10*lemma152CorrectionConstant*(3*(1/(60*lemma152CorrectionConstant))) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 1/2 := he

lemma lemma153_repaired_center_neighborhood_comparison {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hβre : ∀ i, (β i).re = 0) (hγre : γ.re = 0)
    (hβ : ∀ i, ‖β i‖ ≤ lemma153CenterShiftRadius)
    (hγ : ‖γ‖ ≤ lemma153CenterShiftRadius) :
    ‖lemma153EulerProduct χ β γ 1 - lemma153MainTerm χ‖ ≤
      lemma153CenterVariationConstant*(‖β 0‖+‖β 1‖+‖γ‖) :=
  lemma153_repaired_center_main_comparison hD χ β γ
    (lemma153_small_parameters_of_radius β γ hβre hγre hβ hγ)

noncomputable def lemma153PaperCenterConstant : ℝ :=
  9*lemma153CenterVariationConstant

lemma lemma153_paper_center_constant_pos : 0 < lemma153PaperCenterConstant :=
  mul_pos (by norm_num) lemma153_center_variation_constant_pos

lemma lemma153_paper_shift_norm_sum_le {D : ℕ} {c : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10) (j : Fin 3) :
    ‖lemma152PaperBeta D c 0‖+‖lemma152PaperBeta D c 1‖+‖lemma83PaperBeta D c j‖ ≤
      9*lemma44PaperAlpha D := by
  linarith [lemma152_paper_beta_norm_le hL hc hsmall (0 : Fin 2),
    lemma152_paper_beta_norm_le hL hc hsmall (1 : Fin 2),
    lemma153_paper_beta_norm_le hL hc hsmall j]

/-- The original shared c′ and each of the original three gamma shifts satisfy
the O(alpha) estimate for the repaired U.  Its absolute constant has no D, chi,
c′ or j dependence. -/
lemma lemma153_paper_repaired_center_estimate {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3,
        ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) 1 -
          lemma153MainTerm χ‖ ≤ lemma153PaperCenterConstant*lemma44PaperAlpha D := by
  obtain ⟨D₁,hD1,hpar⟩ := lemma153_small_parameters_threshold hc
  obtain ⟨D₂,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max D₁ D₂,hD1.trans (le_max_left _ _),?_⟩
  intro D hD χ j
  have hD₁ : D₁≤D := (le_max_left _ _).trans hD
  have hD₂ : D₂≤D := (le_max_right _ _).trans hD
  have hDne : D ≠ 0 := by omega
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD₂)).1
  apply (lemma153_repaired_center_main_comparison hDne χ _ _ (hpar D hD₁ j)).trans
  calc
    _ ≤ lemma153CenterVariationConstant*(9*lemma44PaperAlpha D) :=
      mul_le_mul_of_nonneg_left (lemma153_paper_shift_norm_sum_le hL hc (hsmall D hD₂) j)
        lemma153_center_variation_constant_pos.le
    _ = _ := by unfold lemma153PaperCenterConstant; ring

/-- Paper-level form with the totient and actual ramification exclusion shown. -/
lemma lemma153_paper_repaired_center_explicit {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3,
        ‖lemma153EulerProduct χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j) 1 -
          (Nat.totient D:ℂ)^2/(D:ℂ)^2 *
            ∏' q : {q : Nat.Primes // ¬q.val ∣ D},
              (1-(q.val.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ))‖ ≤
          lemma153PaperCenterConstant*lemma44PaperAlpha D :=
  lemma153_paper_repaired_center_estimate hc

end ZhangLS.Spec
