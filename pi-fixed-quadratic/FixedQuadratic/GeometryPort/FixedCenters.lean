import FixedQuadratic.GeometryPort.Interpolation
import FixedQuadratic.Selection
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

namespace FixedQuadratic
open scoped BigOperators
open OAI.PiExponent

noncomputable def heightWeightsQ {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) : Fin m → ℚ := fun i =>
  (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℚ)

theorem heightWeightsQ_pos {m : ℕ} (F : IntermediateField ℚ ℝ)
    (β : Fin m → F) (hheight : ∀ i, 2 ≤ primitiveMinpolyHeight (β i : ℝ)) (i : Fin m) :
    0 < heightWeightsQ F β i := by
  have hh := MatrixArithmetic.ceil_log_weight_pos (hheight i)
  dsimp [heightWeightsQ]
  exact_mod_cast hh

noncomputable def geometricDegreeWeights {m : ℕ} (w0 : ℚ) (w : Fin m → ℚ) :
    Fin (m+1) → ℚ := Fin.cases w0 w
noncomputable def geometricJetWeights {m : ℕ} (v θ : ℚ) (w : Fin m → ℚ) :
    Fin (m+1) → ℚ := Fin.cases v (fun i => w i/θ)

theorem geometric_fibre_product_ratio {m : ℕ} (v θ : ℚ) (w : Fin m → ℚ)
    (hw : ∀ i, 0 < w i) :
    (∏ i : Fin m, (geometricDegreeWeights 1 w i.succ : ℝ))/
      (∏ i : Fin m, (geometricJetWeights v θ w i.succ : ℝ)) = (θ : ℝ)^m := by
  have hp : (∏ i, (w i : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => by exact_mod_cast (hw i).ne')
  simp only [geometricDegreeWeights, geometricJetWeights, Fin.cases_succ,
    Rat.cast_div, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hp]

theorem geometric_product_ratio {m : ℕ} (w0 v θ : ℚ) (w : Fin m → ℚ)
    (hw : ∀ i, 0 < w i) :
    (∏ i, (geometricDegreeWeights w0 w i : ℝ))/
      (∏ i, (geometricJetWeights v θ w i : ℝ)) =
      ((w0 : ℝ)/v)*(θ : ℝ)^m := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_div_mul_comm]
  have hf := geometric_fibre_product_ratio v θ w hw
  simpa only [geometricDegreeWeights, geometricJetWeights, Fin.cases_zero,
    Fin.cases_succ] using congrArg (fun z : ℝ => ((w0 : ℝ)/v)*z) hf

/-- Constructs actual fixed-field centers and actual primitive-height weights.
Only the explicit geometric volume, ratio and separated-weight conditions are
inputs. No geometric or surjectivity conclusion is an input. -/
noncomputable def realQuadraticGeometryData (ν Λ D : ℝ) {m : ℕ}
    (F : IntermediateField ℚ ℝ) (β : Fin m → F)
    (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (hheight : ∀ i, 2 ≤ primitiveMinpolyHeight (β i : ℝ)) (hm : 1 ≤ m)
    (k : ℕ) (w0 v θ sigma : ℚ) (hw0 : 0 < w0) (hv : 0 < v) (hθ : 0 < θ)
    (hsigma : 0 < (sigma : ℝ))
    (hvolume : (1+3*(sigma : ℝ))^(m+1)*((k : ℝ)*((w0 : ℝ)/v)*(θ : ℝ)^m) < 1)
    (hfibre : (1+3*(sigma : ℝ))^m*((k : ℝ)*(θ : ℝ)^m) < 1)
    (hratio : (1+(sigma : ℝ))*(θ : ℝ) < 1)
    (hsep : ∀ A B : Finset (Fin (m+1)), A.card = B.card → ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma*
        (∏ j ∈ B, (geometricJetWeights v θ (heightWeightsQ F β) j : ℝ)) <
        ∏ j ∈ A, (geometricDegreeWeights w0 (heightWeightsQ F β) j : ℝ)) :
    FixedFieldGeometryData ν Λ D where
  m := m
  K := k
  m_pos := hm
  sigma := sigma
  sigma_pos := hsigma
  curveDegreeWeights := geometricDegreeWeights w0 (heightWeightsQ F β)
  curveJetWeights := geometricJetWeights v θ (heightWeightsQ F β)
  curveDegreeWeights_pos := fun i => Fin.cases hw0 (heightWeightsQ_pos F β hheight) i
  curveJetWeights_pos := fun i => Fin.cases hv
    (fun j => div_pos (heightWeightsQ_pos F β hheight j) hθ) i
  curveCenters := fun j i => (j.val : ℂ)*(2*Complex.I*((β i : ℝ) : ℂ))
  curveCenters_injective := fun i => quadratic_centers_injective (β i : ℝ)
    (degree_two_ne_zero _ (hβ i)) k
  curve_volume := by
    have hp := geometric_product_ratio w0 v θ (heightWeightsQ F β) (heightWeightsQ_pos F β hheight)
    calc
      _ = (1+3*(sigma : ℝ))^(m+1)*((k : ℝ)*
          ((∏ i, (geometricDegreeWeights w0 (heightWeightsQ F β) i : ℝ))/
            (∏ i, (geometricJetWeights v θ (heightWeightsQ F β) i : ℝ)))) := by ring
      _ < 1 := by rw [hp]; simpa only [mul_assoc] using hvolume
  curve_fibre_volume := by
    have hp := geometric_fibre_product_ratio v θ (heightWeightsQ F β) (heightWeightsQ_pos F β hheight)
    calc
      _ = (1+3*(sigma : ℝ))^m*((k : ℝ)*
          ((∏ i : Fin m, (geometricDegreeWeights 1 (heightWeightsQ F β) i.succ : ℝ))/
            (∏ i : Fin m, (geometricJetWeights v θ (heightWeightsQ F β) i.succ : ℝ)))) := by
              simp only [geometricDegreeWeights, Fin.cases_succ]; ring
      _ < 1 := by rw [hp]; exact hfibre
  curve_separated_weight_products := hsep
  curve_coordinate_ratio := by
    intro i
    simp only [geometricDegreeWeights, geometricJetWeights, Fin.cases_succ, Rat.cast_div]
    have ht : (0 : ℝ) < θ := by exact_mod_cast hθ
    have hw : (0 : ℝ) < heightWeightsQ F β i := by exact_mod_cast heightWeightsQ_pos F β hheight i
    apply (lt_div_iff₀ ht).mpr
    nlinarith [mul_lt_mul_of_pos_right hratio hw]

/-- Actual fixed-field primitive-height centers have arbitrarily large nonzero
full-row minors under the explicit source geometric weight conditions.
Surjectivity is derived through the proved compactification/blowup chain. -/
theorem fixed_field_cofinal_nonzero_minor (ν Λ D : ℝ) {m : ℕ}
    (F : IntermediateField ℚ ℝ) (β : Fin m → F)
    (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (hheight : ∀ i, 2 ≤ primitiveMinpolyHeight (β i : ℝ)) (hm : 1 ≤ m)
    (k : ℕ) (w0 v θ sigma : ℚ) (hw0 : 0 < w0) (hv : 0 < v) (hθ : 0 < θ)
    (hsigma : 0 < (sigma : ℝ))
    (hvolume : (1+3*(sigma : ℝ))^(m+1)*((k : ℝ)*((w0 : ℝ)/v)*(θ : ℝ)^m) < 1)
    (hfibre : (1+3*(sigma : ℝ))^m*((k : ℝ)*(θ : ℝ)^m) < 1)
    (hratio : (1+(sigma : ℝ))*(θ : ℝ) < 1)
    (hsep : ∀ A B : Finset (Fin (m+1)), A.card = B.card → ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma*
        (∏ j ∈ B, (geometricJetWeights v θ (heightWeightsQ F β) j : ℝ)) <
        ∏ j ∈ A, (geometricDegreeWeights w0 (heightWeightsQ F β) j : ℝ))
    (T : Fin m → ℕ) (hTail : ∀ i, heightWeightsQ F β i/θ ≤ (T i : ℚ)*v)
    (L : ℝ) : ∃ H : ℝ, L ≤ H ∧ ∃ selection :
      InterpolationMatrix.Row k (v : ℝ) (θ : ℝ) (fun i => (heightWeightsQ F β i : ℝ)) H →
        InterpolationMatrix.Column (w0 : ℝ) (fun i => (heightWeightsQ F β i : ℝ)) H,
      Function.Injective selection ∧
      ((InterpolationMatrix.truncatedLogMatrix k w0 v θ (fun i => (heightWeightsQ F β i : ℝ)) H
        (fun i => 2*Complex.I*((β i : ℝ) : ℂ)) T).submatrix id selection).det ≠ 0 := by
  let d := realQuadraticGeometryData ν Λ D F β hβ hheight hm k w0 v θ sigma hw0 hv hθ
    hsigma hvolume hfibre hratio hsep
  apply FixedFieldInterpolation.cofinal_nonzero_full_row_minor d (w0 : ℝ) v θ
    (fun i => (heightWeightsQ F β i : ℝ)) (by exact_mod_cast hw0)
    (fun i => by exact_mod_cast heightWeightsQ_pos F β hheight i)
  · change ∀ i : Fin (m+1),
      (geometricDegreeWeights w0 (heightWeightsQ F β) i : ℝ) =
        InterpolationMatrix.columnWeights w0 (fun j => (heightWeightsQ F β j : ℝ)) i
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  · change ∀ i : Fin (m+1),
      (geometricJetWeights v θ (heightWeightsQ F β) i : ℝ) =
        InterpolationMatrix.rowWeights v θ (fun j => (heightWeightsQ F β j : ℝ)) i
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change ((heightWeightsQ F β j / θ : ℚ) : ℝ) =
        (heightWeightsQ F β j : ℝ) / (θ : ℝ)
      exact Rat.cast_div _ _
  · intro j i
    rfl
  · intro i
    exact hTail i

end FixedQuadratic
