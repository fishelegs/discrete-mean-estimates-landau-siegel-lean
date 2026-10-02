import ZhangLS.Spec.Proposition141UniformLargeSaving
import ZhangLS.Spec.ConductorTotientWeight

/-! # The original D₂ conductor weight attached to the actual large mean

D₂ is kept explicitly (D₂=D in the main case). Composite φ(hr), the true
r/φ(r) weight and τ₅(D₁)τ₅(d) remain until the appropriate outer sums.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition141_localized_mean_expanded {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ d h:ℕ) (R:ℝ) (Q:Finset ℕ) :
    proposition141LocalizedWeightedMean χ β κ D₁ d h R Q =
      ∑r∈Q,((r:ℝ)/r.totient)*
        ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
          ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)‖ := by
  simp only [proposition141LocalizedWeightedMean,proposition141WeightedFiniteMean,
    proposition141PrimitiveModulusPairs,sum_sigma,mul_sum]

noncomputable def proposition141LocalizedConductorBlock {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ D₂ d h:ℕ) (R:ℝ) (Q:Finset ℕ) : ℝ :=
  ∑r∈Q,(D₂:ℝ)*((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹*
    ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
      ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)‖

lemma proposition141_localized_block_nonneg {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ D₂ d h:ℕ) (R:ℝ) (Q:Finset ℕ) :
    0≤proposition141LocalizedConductorBlock χ β κ D₁ D₂ d h R Q := by
  unfold proposition141LocalizedConductorBlock
  exact sum_nonneg (fun _ _=>mul_nonneg (by positivity) (sum_nonneg (fun _ _=>norm_nonneg _)))

/-- True composite-totient scalar bound, attached to the actual family. -/
theorem proposition141_localized_block_le_mean {D d h:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ D₂:ℕ)
    (hd:0<d) (hh:0<h) {R:ℝ} (hR:0<R) (Q:Finset ℕ)
    (hQ1:∀r∈Q,1<r) (hQlo:∀r∈Q,R≤(r:ℝ)) :
    proposition141LocalizedConductorBlock χ β κ D₁ D₂ d h R Q ≤
      (D₂:ℝ)*((d:ℝ)*(h:ℝ)*(h.totient:ℝ))⁻¹*
        (proposition141LocalizedWeightedMean χ β κ D₁ d h R Q/R^(3/2:ℝ)) := by
  rw [proposition141_localized_mean_expanded]
  unfold proposition141LocalizedConductorBlock
  calc
    _≤∑r∈Q,((D₂:ℝ)*(((d:ℝ)*(h:ℝ)*(h.totient:ℝ))⁻¹*((r:ℝ)/r.totient)/R^(3/2:ℝ)))*
      ∑θ∈(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive),
        ‖proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r (proposition141LocalizedIndices D R h)‖ := by
      apply sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun _ _=>norm_nonneg _))
      exact mul_le_mul_of_nonneg_left
        (conductorTotientWeight_bound hd hh (by have := hQ1 r hr; omega) hR (hQlo r hr)) (Nat.cast_nonneg _)
    _=_ := by
      simp only [div_eq_mul_inv,mul_assoc]
      rw [←mul_sum,sum_mul]
      rw [←mul_sum]
      congr 1
      congr 1
      apply sum_congr rfl
      intro r hr
      ring

/-- Actual one-block bound with the original D₂ factor explicit. It comes
from the proved mean and not from an assumed (14.8)-type estimate. -/
theorem proposition141_uniform_localized_conductor_block :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D → NormalizedAssumptionA χ →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀B:ℝ,0≤B →
      ∀κ:ℕ→ℂ,Proposition141KappaBound B κ → ∀D₁ D₂ d h:ℕ,
      0<D₁ → 0<d → 0<h → ∀R:ℝ,(D:ℝ)^3≤R →
      ((d*h:ℕ):ℝ)*R≤2*(D:ℝ)*lemma61PaperP4 D →
      ∀Q:Finset ℕ,(∀r∈Q,1<r) → (∀r∈Q,R≤(r:ℝ)) → (∀r∈Q,(r:ℝ)≤2*R) →
      proposition141LocalizedConductorBlock χ β κ D₁ D₂ d h R Q ≤
        proposition141LargeMeanConstant*B*(lemma34Tau 5 D₁:ℝ)*lemma56PrimeMass D*lemma23PaperL D^3351*
          ((D₂:ℝ)/(D:ℝ)^(3/2:ℝ))*((lemma34Tau 5 d:ℝ)/(d:ℝ))*(h.totient:ℝ)⁻¹ := by
  obtain ⟨D₀,hD₀,hm⟩ := proposition141_uniform_localized_large_saving
  refine ⟨D₀,hD₀,?_⟩
  intro D χ hlarge hA β hβ B hB κ hκ D₁ D₂ d h hD₁ hd hh R hR hcut Q hQ1 hQlo hQhi
  have hDp : 0<(D:ℝ) := by exact_mod_cast (show 0<D by have := hD₀.trans hlarge; omega)
  have hRp : 0<R := (pow_pos hDp 3).trans_le hR
  have hmean := hm χ hlarge hA β hβ B hB κ hκ D₁ d h hD₁ hd hh R hR hcut Q hQ1 hQhi
  apply (proposition141_localized_block_le_mean χ β κ D₁ D₂ hd hh hRp Q hQ1 hQlo).trans
  have hb := mul_le_mul_of_nonneg_left hmean
    (show 0≤(D₂:ℝ)*((d:ℝ)*(h:ℝ)*(h.totient:ℝ))⁻¹ by positivity)
  apply hb.trans_eq
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  have hhR : 0<(h:ℝ) := by exact_mod_cast hh
  have hφh : 0<(h.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hh
  have hpow := (Real.rpow_pos_of_pos hDp (3/2:ℝ)).ne'
  field_simp

end ZhangLS.Spec
