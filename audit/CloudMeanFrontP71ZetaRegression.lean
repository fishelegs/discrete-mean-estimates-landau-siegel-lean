import ZhangLS.Spec.Proposition71ZetaAuxiliaryHeight
import ZhangLS.Spec.Proposition71HorizontalLogNorm
import ZhangLS.Spec.Proposition71ZetaAuxiliaryStrip
import ZhangLS.Spec.Proposition71ZetaRightAnchor
import ZhangLS.Spec.Proposition71ZetaStripBounds
import ZhangLS.Spec.Proposition71ZetaPaperStrip
import ZhangLS.Spec.Proposition71ZetaRegularizedReciprocal

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
-- The exact original alpha normalization, rather than alpha=L^(-9).
example (D : ℕ) : lemma44PaperAlpha D=Real.pi/(lemma23PaperL D^9) := by
  simp [lemma44PaperAlpha,lemma23PaperP]
-- The actual pole-removed value is retained at the pole.
example : zetaPoleRemoved 1=1 := lemma55_actual_zeta_pole_removed_at_one
example : proposition71RegularizedZetaReciprocal 1=0 :=
  proposition71_regularized_zeta_reciprocal_at_one
-- Exact original reciprocal on every genuine contour point away from 0 and 1.
example (s : ℂ) (hs0 : s≠0) (hs1 : s≠1) :
    proposition71RegularizedZetaReciprocal s=(riemannZeta s)⁻¹ :=
  proposition71_regularized_zeta_reciprocal_eq hs0 hs1
-- Both closed-rectangle and two-direction transport quantifiers are printed.
#check proposition71_zeta_auxiliary_horizontal_ratios
#check proposition71_regularized_zeta_reciprocal_strip
end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition71ZetaAuxHeight
#print axioms ZhangLS.Spec.proposition71ZetaAuxInteger
#print axioms ZhangLS.Spec.proposition71_zeta_aux_height_pos
#print axioms ZhangLS.Spec.proposition71_zeta_aux_integer_bounds
#print axioms ZhangLS.Spec.proposition71_zeta_aux_log_bounds
#print axioms ZhangLS.Spec.proposition71_zeta_aux_root_tendsto
#print axioms ZhangLS.Spec.proposition71_zeta_aux_height_tendsto
#print axioms ZhangLS.Spec.proposition71_zeta_auxiliary_geometry
#print axioms ZhangLS.Spec.proposition71_horizontal_log_norm_difference
#print axioms ZhangLS.Spec.proposition71_horizontal_norm_ratio_bound
#print axioms ZhangLS.Spec.proposition71ZetaAuxLogDerivativeBound
#print axioms ZhangLS.Spec.proposition71_zeta_auxiliary_strip
#print axioms ZhangLS.Spec.proposition71_zeta_auxiliary_horizontal_ratios
#print axioms ZhangLS.Spec.proposition71_real_zeta_norm_mass
#print axioms ZhangLS.Spec.proposition71_bounded_lseries_norm_zeta
#print axioms ZhangLS.Spec.proposition71_real_zeta_elementary_bound
#print axioms ZhangLS.Spec.proposition71_zeta_right_half_bounds
#print axioms ZhangLS.Spec.proposition71_norm_quotient_displacement
#print axioms ZhangLS.Spec.proposition71_zeta_repaired_strip_bounds
#print axioms ZhangLS.Spec.proposition71_zeta_paper_alpha_budget
#print axioms ZhangLS.Spec.proposition71_zeta_paper_strip_bounds
#print axioms ZhangLS.Spec.proposition71RegularizedZetaReciprocal
#print axioms ZhangLS.Spec.proposition71_regularized_zeta_reciprocal_at_one
#print axioms ZhangLS.Spec.proposition71_regularized_zeta_reciprocal_eq
#print axioms ZhangLS.Spec.proposition71_regularized_zeta_reciprocal_analytic
#print axioms ZhangLS.Spec.proposition71_regularized_zeta_reciprocal_strip
#print ZhangLS.Spec.proposition71ZetaAuxHeight
#print ZhangLS.Spec.proposition71ZetaAuxInteger
#print ZhangLS.Spec.proposition71ZetaAuxLogDerivativeBound
#print ZhangLS.Spec.proposition71_zeta_auxiliary_geometry
#print ZhangLS.Spec.proposition71_zeta_auxiliary_strip
#print ZhangLS.Spec.proposition71_zeta_auxiliary_horizontal_ratios
#print ZhangLS.Spec.proposition71_zeta_right_half_bounds
#print ZhangLS.Spec.proposition71_zeta_repaired_strip_bounds
#print ZhangLS.Spec.proposition71_zeta_paper_strip_bounds
#print ZhangLS.Spec.proposition71RegularizedZetaReciprocal
#print ZhangLS.Spec.proposition71_regularized_zeta_reciprocal_strip
#print ZhangLS.Spec.lemma81_uniform_zeta_pole_removed_thin_strip
#print ZhangLS.Spec.lemma81_zeta_removed_paper_rectangle_bound
