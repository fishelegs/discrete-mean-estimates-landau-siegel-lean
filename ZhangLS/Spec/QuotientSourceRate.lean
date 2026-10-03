import ZhangLS.Spec.QuotientSourceDomination
import ZhangLS.Spec.PrimitiveConductorGaussBound

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- The actual inverse induced Gauss factor has precisely the frozen source
weight. This statement includes imprimitive common levels and conductor 1. -/
theorem quotientSource_actual_induced_gauss_weight {D D₁ D₂ d k : ℕ}
    [NeZero (D₂*k)] (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ)
    (i : primitiveConductorFamilyIndex (D₂*k)) :
    ‖a (d*k)‖ *
      (‖gaussSum (primitiveConductorFamilyLift (D₂*k) i)⁻¹ ZMod.stdAddChar‖ /
        ((d:ℝ)*(k:ℝ)*((D₂*k).totient:ℝ))) *
      ‖proposition141Sigma χ i.2.val β κ D₁ d (D₂*k/i.1.val)‖ ≤
    ‖a (d*k)‖ *
      (Real.sqrt (i.1.val:ℝ)/((d:ℝ)*(k:ℝ)*((D₂*k).totient:ℝ))) *
      ‖proposition141Sigma χ i.2.val β κ D₁ d (D₂*k/i.1.val)‖ := by
  have hb := inducedGauss_inverse_norm_le_sqrt_conductor (primitiveConductorFamilyLift (D₂*k) i)
  rw [primitiveConductorFamily_lift_conductor] at hb
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by positivity)) (norm_nonneg _)) (norm_nonneg _)

/-- Literal expanded original normalized source wrapper for direct attachment
to the front/character calculation. -/
theorem quotientSource_original_normalized_le_complete_conductor {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
      (∑D₁∈D.divisors, ∑'d : ℕ+, ∑'k : ℕ+,
        ∑i : primitiveConductorFamilyIndex ((D/D₁)*(k:ℕ)),
          quotientConductorSourceTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨k,i⟩) ≤
      proposition141CompleteConductorMajorant χ β κ a :=
  quotientSource_normalized_le_complete_conductor χ β κ ha hD hmod

/-- The identical domination on the exact quotient-conductor side of the
transport, including the h-divisibility subtype and primitive character. -/
theorem quotientSource_normalized_target_le_complete_conductor {D : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a)
    (hD : 1<D) (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) :
    ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
      (∑D₁∈D.divisors, ∑'d : ℕ+, ∑'r : ℕ+,
        ∑'h : {h : ℕ+ // D/D₁∣(r:ℕ)*(h:ℕ)},
          ∑θ : {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive},
            quotientConductorTargetTerm χ β κ a D₁ (D/D₁) (d:ℕ) ⟨r,h,θ⟩) ≤
      proposition141CompleteConductorMajorant χ β κ a := by
  rw [←quotientConductor_normalized_outer_reindex χ β κ ha (by omega)]
  exact quotientSource_original_normalized_le_complete_conductor χ β κ ha hD hmod

/-- The original coefficient constants and epsilon precede one threshold;
D, chi, kappa*, a*, and the full complex beta disk follow it. -/
theorem quotientSource_normalized_little_o (Bκ Ba : ℝ) (hBκ : 0<Bκ) (hBa : 0<Ba)
    (ε : ℝ) (hε : 0<ε) :
    ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D → ∀χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀κ a : ℕ→ℂ, Proposition141KappaBound Bκ κ →
        Proposition141AdmissibleSequence D Ba a → ∀β : ℂ, ‖β‖<5*lemma44PaperAlpha D →
          quotientSourceNormalizedSource χ β κ a≤ε*lemma33ActualPrimeMass D := by
  obtain ⟨N₁,hN₁,hbound⟩ := proposition141_complete_conductor_little_o Bκ Ba hBκ hBa ε hε
  obtain ⟨N₂,hN₂,hmod⟩ := proposition141_uniform_support_modulus_bound
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA κ a hκ ha β hβ
  have hN1 : N₁≤D := (le_max_left _ _).trans hDN
  have hN2 : N₂≤D := (le_max_right _ _).trans hDN
  exact (quotientSource_normalized_le_complete_conductor χ β κ ha
    (by have := hN₁.trans hN1; omega) (hmod D hN2)).trans
      (hbound D hN1 χ hA κ a hκ ha β hβ)

end ZhangLS.Spec
