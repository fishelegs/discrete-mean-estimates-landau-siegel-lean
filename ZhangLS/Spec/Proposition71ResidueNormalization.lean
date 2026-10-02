import ZhangLS.Spec.Proposition71ResidueCorrection
import ZhangLS.Spec.Proposition71ResidueScalar

/-! Quantitative normalization of the actual Proposition 7.1 residues.
The original shift parameter is fixed before the constant and threshold. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology
set_option maxHeartbeats 2000000

noncomputable def proposition71ResidueNormalizationConstant (c : ℝ) : ℝ :=
  proposition71ResidueScalarConstant c+150*proposition71ResidueFactorConstant

lemma proposition71_residue_normalization_constant_pos {c : ℝ} (hc : 0<c) :
    0<proposition71ResidueNormalizationConstant c := by
  unfold proposition71ResidueNormalizationConstant
  exact add_pos (proposition71_residue_scalar_constant_pos hc)
    (mul_pos (by norm_num) proposition71_residue_factor_constant_pos)

/-- Explicit O_c(L) error with all local analytic factors retained. -/
theorem proposition71_actual_residue_normalization_bound {D p : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hδ : ∀ j : Fin 3, ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤
      lemma54Constant*lemma44PaperAlpha D*lemma23PaperL D)
    (hbudget : proposition71ResidueFactorConstant*lemma44PaperAlpha D*lemma23PaperL D≤1)
    (hp : p∈lemma56PaperPrimes D) (j : Fin 3) :
    ‖I*proposition71ActualR D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
      proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ)‖≤
        proposition71ResidueNormalizationConstant c*lemma23PaperL D := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have ha := (lemma44_alpha_pos_le_one hL3).1
  have hG := proposition71_residue_geometric_norm hL3 hc hsmall j
  have hscalar := proposition71_residue_scalar_normalization hp hL3 hc hsmall j
  have hcor := proposition71_actual_correction_error hL3 hc hsmall hδ hbudget j
  have hphase := proposition71_residue_prime_phase_norm hp c j
  have heq : I*proposition71ActualR D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
      proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ) =
      (proposition71ResidueGeometric D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
        proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ)) +
      proposition71ResidueGeometric D c j*(p:ℂ)^(-lemma83PaperBeta D c j)*
        (proposition71ResidueCorrection D c j-1) := by
    rw [proposition71_actual_residue_regular_formula hD hL hc hsmall j]
    unfold proposition71ResidueGeometric
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,hphase,mul_one]
  have herr : ‖proposition71ResidueGeometric D c j‖*‖proposition71ResidueCorrection D c j-1‖≤
      150*proposition71ResidueFactorConstant*lemma23PaperL D := by
    calc
      _ ≤ (10/lemma44PaperAlpha D)*
        (15*proposition71ResidueFactorConstant*lemma44PaperAlpha D*lemma23PaperL D) :=
          mul_le_mul hG hcor (norm_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  unfold proposition71ResidueNormalizationConstant
  nlinarith only [hscalar,herr]

/-- The three actual residues satisfy the three source normalizations, with
c fixed first and one common positive constant and natural threshold. -/
theorem proposition71_actual_residue_normalization {c : ℝ} (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ p∈lemma56PaperPrimes D, ∀ j : Fin 3,
        ‖I*proposition71ActualR D c j*(p:ℂ)^(-lemma83PaperBeta D c j)-
          proposition71ResidueWeight j/(lemma44PaperAlpha D:ℂ)‖≤C*Real.log (D:ℝ) := by
  obtain ⟨D₀,hD₀,hpar⟩ := proposition71_residue_parameters_threshold hc
  refine ⟨proposition71ResidueNormalizationConstant c,
    proposition71_residue_normalization_constant_pos hc,D₀,hD₀,?_⟩
  intro D hD p hp j
  have h := hpar D hD
  exact proposition71_actual_residue_normalization_bound (by omega) h.1 hc h.2.1 h.2.2.1 h.2.2.2 hp j

/-- The actual residues are nonzero; the three certified local singularities
are genuine simple poles, rather than merely removable candidates. -/
theorem proposition71_actual_residue_nonzero {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ j : Fin 3,
      proposition71ActualR D c j≠0 := by
  obtain ⟨Da,hDa,hpar⟩ := proposition71_residue_parameters_threshold hc
  have hK : 0<15*proposition71ResidueFactorConstant :=
    mul_pos (by norm_num) proposition71_residue_factor_constant_pos
  obtain ⟨Db,hDb,hbudget⟩ := lemma52_exists_shift_threshold hK
  refine ⟨max Da Db,le_trans hDa (le_max_left _ _),?_⟩
  intro D hD j
  have haD : Da≤D := (le_max_left _ _).trans hD
  have hbD : Db≤D := (le_max_right _ _).trans hD
  have h := hpar D haD
  have hL : 3≤lemma23PaperL D := by linarith [h.1]
  have hshift := section15_actual_shift_data hL hc h.2.1
  have hcor := proposition71_actual_correction_error hL hc h.2.1 h.2.2.1 h.2.2.2 j
  have hcn : proposition71ResidueCorrection D c j≠0 :=
    section15_ne_zero_of_near_one hcor (by linarith [hbudget D hbD])
  have hg1 : lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have hh := hshift.2 he; fin_cases j <;> simp at hh)
  have hg2 : lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have hh := hshift.2 he; fin_cases j <;> simp at hh)
  have hgn := div_ne_zero (mul_ne_zero I_ne_zero (neg_ne_zero.mpr (hshift.1 j)))
    (mul_ne_zero hg1 hg2)
  have he := proposition71_actual_residue_regular_formula (by omega) h.1 hc h.2.1 j
  intro hr
  rw [hr,mul_zero] at he
  exact (mul_ne_zero hgn hcn) he.symm

end ZhangLS.Spec
