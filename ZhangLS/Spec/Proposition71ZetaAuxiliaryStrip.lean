import ZhangLS.Spec.Proposition71ZetaAuxiliaryHeight
import ZhangLS.Spec.Proposition71HorizontalLogNorm

/-! # Genuine unconditional zeta control on the repaired Section7 rectangle

The original arithmetic modulus D only sets L=log D. The independent integer
height parameter feeds the unconditional zero-free theorem, with every radius,
height and threshold inclusion proved. No character or (A) is substituted.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 3000000

noncomputable def proposition71ZetaAuxLogDerivativeBound (D : ℕ) : ℝ :=
  360000000*Real.log (proposition71ZetaAuxInteger D : ℝ)^2+
    21600*Real.log (proposition71ZetaAuxInteger D : ℝ)

/-- The actual pole-removed zeta is nonzero on the full closed repaired
rectangle, including the pole height. Its horizontal transport cost is ≤1. -/
theorem proposition71_zeta_auxiliary_strip :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤Real.log (D : ℝ) ∧
      (2/Real.log (D : ℝ))*proposition71ZetaAuxLogDerivativeBound D≤1 ∧
      ∀ z : ℂ, 1-1/Real.log (D : ℝ)≤z.re → z.re≤2 →
        |z.im|≤proposition71ZetaAuxHeight D →
        zetaPoleRemoved z≠0 ∧ ‖logDeriv zetaPoleRemoved z‖≤proposition71ZetaAuxLogDerivativeBound D := by
  obtain ⟨M₀,hM₀⟩ := lemma81_uniform_zeta_pole_removed_thin_strip
  obtain ⟨D₁,hD₁⟩ := eventually_atTop.mp (proposition71_zeta_auxiliary_geometry M₀)
  refine ⟨max 2 D₁,le_max_left _ _,?_⟩
  intro D hD
  obtain ⟨hDpos,hL,hM,hM4,hML,hwidth,hheight,hcost⟩ := hD₁ D ((le_max_right _ _).trans hD)
  obtain ⟨_,_,hfree⟩ := hM₀ (proposition71ZetaAuxInteger D) hM
  refine ⟨hL,hcost,?_⟩
  intro z hre hre2 him
  apply lemma81_zeta_removed_paper_rectangle_bound hM4 hML hfree
  · linarith only [hre,hwidth]
  · exact hre2
  · exact him.trans hheight

/-- Both directions of actual pole-removed zeta transport are bounded by exp(1)
throughout every short horizontal path in the repaired rectangle. -/
theorem proposition71_zeta_auxiliary_horizontal_ratios :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      3≤Real.log (D : ℝ) ∧
      ∀ a b t : ℝ, 1-1/Real.log (D : ℝ)≤a → a≤b → b≤2 →
        b-a≤2/Real.log (D : ℝ) → |t|≤proposition71ZetaAuxHeight D →
        ‖zetaPoleRemoved ((a : ℂ)+I*(t : ℂ))/zetaPoleRemoved ((b : ℂ)+I*(t : ℂ))‖≤Real.exp 1 ∧
        ‖zetaPoleRemoved ((b : ℂ)+I*(t : ℂ))/zetaPoleRemoved ((a : ℂ)+I*(t : ℂ))‖≤Real.exp 1 := by
  obtain ⟨D₀,hD₀,hstrip⟩ := proposition71_zeta_auxiliary_strip
  refine ⟨D₀,hD₀,?_⟩
  intro D hD
  obtain ⟨hL,hcost,hbound⟩ := hstrip D hD
  refine ⟨hL,?_⟩
  intro a b t ha hab hb hwidth ht
  have hLp : 0<Real.log (D : ℝ) := by linarith
  have hhalf : 1/Real.log (D : ℝ)≤1/2 := by
    apply (div_le_div_iff₀ hLp (by norm_num : (0 : ℝ)<2)).mpr
    linarith
  have hre (x : ℝ) (hx : x∈Icc a b) :
      1-1/Real.log (D : ℝ)≤((x : ℂ)+I*(t : ℂ)).re := by simpa using ha.trans hx.1
  have hre2 (x : ℝ) (hx : x∈Icc a b) : ((x : ℂ)+I*(t : ℂ)).re≤2 := by simpa using hx.2.trans hb
  have him (x : ℝ) : |((x : ℂ)+I*(t : ℂ)).im|≤proposition71ZetaAuxHeight D := by simpa using ht
  have hz (x : ℝ) (hx : x∈Icc a b) := hbound _ (hre x hx) (hre2 x hx) (him x)
  have hf (x : ℝ) (hx : x∈Icc a b) : DifferentiableAt ℂ zetaPoleRemoved ((x : ℂ)+I*(t : ℂ)) :=
    (lemma55_actual_zeta_pole_removed_analyticAt (by have hh := hre x hx; linarith)).differentiableAt
  have hratios := proposition71_horizontal_norm_ratio_bound hab hf
    (fun x hx => (hz x hx).1) (fun x hx => (hz x hx).2)
  have hK : 0≤proposition71ZetaAuxLogDerivativeBound D :=
    (norm_nonneg _).trans (hz a ⟨le_rfl,hab⟩).2
  have he : Real.exp (proposition71ZetaAuxLogDerivativeBound D*(b-a))≤Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left hwidth hK).trans (by simpa only [mul_comm] using hcost)
  exact ⟨hratios.1.trans he,hratios.2.trans he⟩

end ZhangLS.Spec
