import FixedQuadratic.GeometryPort.FixedCenters
import OAI.NumberTheory.PiExponent.Approximation.WeightSeparation

namespace FixedQuadratic.ParameterPort
open scoped BigOperators
open OAI OAI.PiExponent

theorem separated_products_from_growth {m : ℕ} (w0 v θ sigma : ℚ)
    (w : Fin m → ℚ) (x : ℕ → ℝ)
    (hw0 : 0 < (w0 : ℝ)) (hv : 0 < (v : ℝ)) (hθ : 0 < (θ : ℝ))
    (hsigma : 0 < (sigma : ℝ)) (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hcast : ∀ i, (w i : ℝ) = x (i.val+1))
    (hgrowth : PiExponentApprox.SeparatedWeightGrowth m
      (PiExponentApprox.weightSeparationFactor m
        (PersistentWeightComparison.comparisonConstant m sigma) w0 v θ) x)
    (A B : Finset (Fin (m+1))) (hcard : A.card = B.card)
    (i : Fin (m+1)) (hi : i ≠ 0) (hiA : i ∈ A) (hiB : i ∉ B)
    (hhigh : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) :
    PersistentWeightComparison.comparisonConstant m sigma*
      (∏ j ∈ B, (geometricJetWeights v θ w j : ℝ)) <
      ∏ j ∈ A, (geometricDegreeWeights w0 w j : ℝ) := by
  classical
  have hdcast (j : Fin (m+1)) : (geometricDegreeWeights w0 w j : ℝ) =
      PiExponentApprox.geometricDegreeWeight w0 x j.val := by
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [geometricDegreeWeights,PiExponentApprox.geometricDegreeWeight]
    · simpa only [geometricDegreeWeights,Fin.cases_succ,Fin.val_succ,
        PiExponentApprox.geometricDegreeWeight,Nat.add_one_ne_zero,ite_false] using hcast l
  have hjcast (j : Fin (m+1)) : (geometricJetWeights v θ w j : ℝ) =
      PiExponentApprox.geometricJetWeight v θ x j.val := by
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [geometricJetWeights,PiExponentApprox.geometricJetWeight]
    · simp only [geometricJetWeights,Fin.cases_succ,Fin.val_succ,
        PiExponentApprox.geometricJetWeight,Nat.add_one_ne_zero,ite_false,Rat.cast_div,hcast]
  let e : Fin (m+1) ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hbound (S : Finset (Fin (m+1))) : S.map e ⊆ Finset.range (m+1) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB,hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k,hkB,rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k,hkA,rfl⟩)
  have hC : 0 < PersistentWeightComparison.comparisonConstant m sigma := by
    unfold PersistentWeightComparison.comparisonConstant
    positivity
  have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have h := PiExponentApprox.geometric_weight_products_separated m
    (PersistentWeightComparison.comparisonConstant m sigma) w0 v θ x
    hC hw0 hv hθ hx0 hx hgrowth (A.map e) (B.map e)
    (by simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i,hiA,rfl⟩)
    (by
      intro hmem
      obtain ⟨a,haB,hai⟩ := Finset.mem_map.mp hmem
      have hai' : a = i := Fin.ext hai
      exact hiB (hai' ▸ haB)) hbelow
  simpa only [Finset.prod_map,e,Function.Embedding.coeFn_mk,←hjcast,←hdcast] using h

end FixedQuadratic.ParameterPort
