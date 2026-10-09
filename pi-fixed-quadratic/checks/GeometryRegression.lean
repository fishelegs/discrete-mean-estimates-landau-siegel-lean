import FixedQuadratic.GeometryPort.Interpolation

namespace FixedQuadratic.GeometryRegression
open scoped BigOperators
open OAI.PiExponent

/-- A concrete consistent geometry packet: the geometric hypotheses are
checked by rational arithmetic, not assumed via an abstract data inhabitant. -/
noncomputable def concreteGeometry : FixedFieldGeometryData 3 1 1 where
  m := 1
  K := 1
  m_pos := by norm_num
  sigma := 1
  sigma_pos := by norm_num
  curveDegreeWeights := fun i => if i = 0 then 1 else 100000
  curveJetWeights := fun i => if i = 0 then 16 else 800000
  curveDegreeWeights_pos := by intro i; split_ifs <;> norm_num
  curveJetWeights_pos := by intro i; split_ifs <;> norm_num
  curveCenters := fun _ _ => 0
  curveCenters_injective := fun _ _ _ _ => Subsingleton.elim _ _
  curve_volume := by norm_num [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
  curve_fibre_volume := by norm_num [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
  curve_separated_weight_products := by
    intro A B hcard i hi hiA hiB hhigh
    fin_cases A <;> fin_cases B <;> fin_cases i <;>
      norm_num [PersistentWeightComparison.comparisonConstant, Fin.cases_zero, Fin.cases_succ] at *
  curve_coordinate_ratio := by intro i; fin_cases i; norm_num [Fin.cases_zero, Fin.cases_succ]

theorem concrete_jet_surjective : ∀ᶠ n : ℕ in Filter.atTop, Function.Surjective
    (BlowupJetSurjectivity.jetRestriction
      (FixedFieldBlowupGeometry.centerIdeal concreteGeometry)
      (FixedFieldBlowupGeometry.hyperplane concreteGeometry) n) :=
  FixedFieldJetSurjectivity.eventually_jetRestriction_surjective concreteGeometry

theorem concrete_nonzero_minor (L : ℝ) : ∃ H : ℝ, L ≤ H ∧
    ∃ selection : InterpolationMatrix.Row 1 16 (1/8) (fun _ : Fin 1 => 100000) H →
      InterpolationMatrix.Column 1 (fun _ : Fin 1 => 100000) H,
    Function.Injective selection ∧
    ((InterpolationMatrix.truncatedLogMatrix 1 1 16 (1/8) (fun _ : Fin 1 => 100000) H
      (fun _ => 1) (fun _ => 50000)).submatrix id selection).det ≠ 0 := by
  apply FixedFieldInterpolation.cofinal_nonzero_full_row_minor concreteGeometry
    1 16 (1/8) (fun _ => 100000) (by norm_num) (fun _ => by norm_num)
  · intro i; refine Fin.cases ?_ (fun j => ?_) i
    · change ((if (0 : Fin 2) = 0 then 1 else 100000 : ℚ) : ℝ) = 1
      norm_num
    · change ((if j.succ = 0 then 1 else 100000 : ℚ) : ℝ) = 100000
      simp
  · intro i; refine Fin.cases ?_ (fun j => ?_) i
    · change ((if (0 : Fin 2) = 0 then 16 else 800000 : ℚ) : ℝ) = 16
      norm_num
    · change ((if j.succ = 0 then 16 else 800000 : ℚ) : ℝ) = (100000 : ℝ) / (1/8)
      simp; norm_num
  · intro j i; fin_cases j; simp [concreteGeometry]
  · intro i; fin_cases i; change (800000 : ℚ) ≤ 50000 * 16; norm_num

end FixedQuadratic.GeometryRegression
