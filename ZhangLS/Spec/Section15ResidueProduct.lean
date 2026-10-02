import ZhangLS.Spec.Section15ActualResidues
import ZhangLS.Spec.Section15SmallFactors
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
set_option maxHeartbeats 2000000

/-- All eight analytic factors in the exact r₁*r₁ⱼ product, including
both harmless value-one zeta factors when j=1 or j=2. -/
noncomputable def section15Correction {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) : ℂ :=
  section15LFactor χ (β 0)*section15LFactor χ (β 1)*lemma54PaperDeltaMellin D 1*
    (section15LFactor χ (-β j))⁻¹ *
    zetaPoleRemoved (1-β j+β 0)*zetaPoleRemoved (1-β j+β 1)*
    (zetaPoleRemoved (1-β j))⁻¹*lemma57OmegaOne D (β 2-β j)

noncomputable def section15Geometric (β : Fin 3 → ℂ) (B : ℝ) (j : Fin 3) : ℂ :=
  β 0*β 1/((β (j+1)-β j)*(β (j+2)-β j))*(B:ℂ)^(β 2-β j)

lemma section15_exact_residue_product {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    {B : ℝ} (hB : 0<B) (j : Fin 3) (hβ0 : ∀ k, β k≠0)
    (hinj : Function.Injective β)
    (hZ : zetaPoleRemoved (1-β j)≠0) (hL : dirichletLFunction χ (1-β j)≠0)
    (hd : LDerivAtOne χ≠0) :
    section15ActualRStar χ β*section15ActualR χ β B j =
      section15Geometric β B j*section15Correction χ β j := by
  rw [section15_actual_residue_formula χ hD β hβ hB j (hβ0 j) hinj hZ hL]
  unfold section15ActualRStar section15Geometric section15Correction section15LFactor
  simp only [←sub_eq_add_neg]
  field_simp [hd,hβ0 0,hβ0 1,hβ0 j,hZ,hL]

noncomputable def section15FactorConstant : ℝ :=
  1+2*section15LRelativeConstant+60*Real.pi+lemma54Constant*Real.pi+18*Real.pi^2

lemma section15_factor_constant_bounds :
    0<section15FactorConstant ∧ 2*section15LRelativeConstant≤section15FactorConstant ∧
    30*Real.pi≤section15FactorConstant ∧ lemma54Constant*Real.pi≤section15FactorConstant ∧
    18*Real.pi^2≤section15FactorConstant := by
  unfold section15FactorConstant
  have hc := section15_l_relative_constant_pos
  have hd := lemma54_constant_pos
  have hp := Real.pi_pos
  have hs := sq_nonneg Real.pi
  have hdpi : 0≤lemma54Constant*Real.pi := mul_nonneg hd.le hp.le
  constructor
  · positivity
  constructor
  · linarith only [hc,hp,hs,hdpi]
  constructor
  · linarith only [hc,hp,hs,hdpi]
  constructor
  · linarith only [hc,hp,hs,hdpi]
  · linarith only [hc,hp,hs,hdpi]

lemma section15_actual_correction_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hδ : ‖lemma54PaperDeltaMellin D 1-1‖≤(lemma54Constant*Real.pi)*lemma23PaperL D^(-6:ℤ))
    (hbudget : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2) (j : Fin 3) :
    ‖section15Correction χ (lemma83PaperBeta D c) j-1‖≤
      (255*section15FactorConstant)*lemma23PaperL D^(-6:ℤ) := by
  let q := lemma23PaperL D^(-6:ℤ)
  let e := section15FactorConstant*q
  have hL : 3≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith
  have hq : 0≤q := by dsimp [q]; positivity
  have hC := section15_factor_constant_bounds
  have hC1 : section15LRelativeConstant≤section15FactorConstant := by linarith [section15_l_relative_constant_pos]
  have hC15 : 15*Real.pi≤section15FactorConstant := by linarith [Real.pi_pos]
  have hl (k : Fin 3) := section15_actual_beta_L_relative_error χ hDN hA hc hsmall k
  have hz (k : Fin 3) := section15_actual_zeta_factor_errors hL hc hsmall j k
  have hl1 (k : Fin 3) : ‖section15LFactor χ (lemma83PaperBeta D c k)-1‖≤e :=
    (hl k).1.trans (mul_le_mul_of_nonneg_right hC1 hq)
  have hlminus : ‖section15LFactor χ (-lemma83PaperBeta D c j)-1‖≤section15LRelativeConstant*q := (hl j).2
  have hlminv : ‖(section15LFactor χ (-lemma83PaperBeta D c j))⁻¹-1‖≤e := by
    have hh := section15_inverse_error hlminus ((mul_le_mul_of_nonneg_right hC1 hq).trans hbudget)
    apply hh.trans
    dsimp [e]
    convert mul_le_mul_of_nonneg_right hC.2.1 hq using 1; ring
  have hz1 (k : Fin 3) : ‖zetaPoleRemoved (1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1‖≤e :=
    (hz k).1.trans (mul_le_mul_of_nonneg_right hC.2.2.1 hq)
  have hzinv : ‖(zetaPoleRemoved (1-lemma83PaperBeta D c j))⁻¹-1‖≤e := by
    have hh := section15_inverse_error (hz 0).2 ((mul_le_mul_of_nonneg_right hC15 hq).trans hbudget)
    apply hh.trans
    dsimp [e]
    convert mul_le_mul_of_nonneg_right hC.2.2.1 hq using 1; ring
  have hδ' : ‖lemma54PaperDeltaMellin D 1-1‖≤e := hδ.trans (mul_le_mul_of_nonneg_right hC.2.2.2.1 hq)
  have ho : ‖lemma57OmegaOne D (lemma83PaperBeta D c 2-lemma83PaperBeta D c j)-1‖≤e :=
    (section15_actual_omega_error hL hc hsmall j).trans (mul_le_mul_of_nonneg_right hC.2.2.2.2 hq)
  have hprod := section15_eight_factor_error _ _ _ _ _ _ _ _
    (hl1 0) (hl1 1) hδ' hlminv (hz1 0) (hz1 1) hzinv ho (by dsimp [e]; linarith)
  simpa only [section15Correction,e,q,mul_assoc] using hprod

end ZhangLS.Spec
