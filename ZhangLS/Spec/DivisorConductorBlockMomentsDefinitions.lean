import ZhangLS.Spec.AllModuliLargeSieve
import ZhangLS.Spec.Proposition141DivisorBounds
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Proposition71WeightedCauchy
import Mathlib.Data.PNat.Basic

/-! Exact finite conductor blocks and positive long intervals.
The dyadic endpoints are real; the long endpoints are both inclusive.
Level one is retained, and residue zero is excluded from every long interval. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.DivisorConductorBlockMoments
open Complex Finset
open scoped Classical ComplexConjugate

noncomputable def blockModuli (R : ℝ) : Finset ℕ :=
  (Icc 1 ⌈2 * R⌉₊).filter (fun r => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R)

theorem mem_blockModuli {R : ℝ} {r : ℕ} :
    r ∈ blockModuli R ↔ 1 ≤ r ∧ R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R := by
  simp only [blockModuli, mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, by exact_mod_cast h.2.2.le.trans (Nat.le_ceil _)⟩, h.2⟩

noncomputable def longIndices (h : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc 1 ⌊8 * X⌋₊).filter
    (fun l => X / 2 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 8 * X ∧ l.Coprime h)

theorem mem_longIndices {h l : ℕ} {X : ℝ} (_hX : 0 ≤ X) :
    l ∈ longIndices h X ↔
      0 < l ∧ X / 2 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 8 * X ∧ l.Coprime h := by
  simp only [longIndices, mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨by omega, h.2⟩
  · intro h
    exact ⟨⟨by omega, Nat.le_floor h.2.2.1⟩, h.2⟩

theorem longIndices_positive {h l : ℕ} {X : ℝ} (hl : l ∈ longIndices h X) : 0 < l := by
  have := (mem_Icc.mp (mem_filter.mp hl).1).1
  omega

theorem longIndices_subset (h : ℕ) (X : ℝ) : longIndices h X ⊆ Icc 1 ⌊8 * X⌋₊ :=
  filter_subset _ _

def CoefficientBound (C_b : ℝ) (b : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, 0 < n → ‖b n‖ ≤ C_b * (lemma34Tau 5 n : ℝ)

noncomputable def longCoefficient (d : ℕ) (b : ℕ → ℂ) (t : ℝ) (l : ℕ) : ℂ :=
  b (d * l) * (l : ℂ) ^ (-(1 : ℂ) - I * (t : ℂ))

/-- The actual l^(-1-it) polynomial, with the complete coprimality mask. -/
noncomputable def longPolynomial (d h : ℕ) (X : ℝ) (b : ℕ → ℂ)
    (r : ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  ∑ l ∈ longIndices h X,
    b (d * l) * θ (l : ZMod r) * (l : ℂ) ^ (-(1 : ℂ) - I * (t : ℂ))

theorem longPolynomial_coefficient_sum (d h : ℕ) (X : ℝ) (b : ℕ → ℂ)
    (r : ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) :
    longPolynomial d h X b r θ t =
      ∑ l ∈ longIndices h X, longCoefficient d b t l * θ (l : ZMod r) := by
  apply sum_congr rfl
  intro l hl
  unfold longCoefficient
  ring

/-- An equivalent index set whose elements themselves carry l>0. -/
noncomputable def longPositiveIndices (h : ℕ) (X : ℝ) : Finset ℕ+ :=
  (longIndices h X).subtype (fun l : ℕ => 0 < l)

/-- The actual polynomial with d,h,l represented explicitly as positive integers. -/
noncomputable def positiveLongPolynomial (d h : ℕ+) (X : ℝ) (b : ℕ → ℂ)
    (r : ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  ∑ l ∈ longPositiveIndices (h : ℕ) X,
    b ((d : ℕ) * (l : ℕ)) * θ ((l : ℕ) : ZMod r) *
      ((l : ℕ) : ℂ) ^ (-(1 : ℂ) - I * (t : ℂ))

theorem positiveLongPolynomial_eq (d h : ℕ+) (X : ℝ) (b : ℕ → ℂ)
    (r : ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) :
    positiveLongPolynomial d h X b r θ t = longPolynomial (d : ℕ) (h : ℕ) X b r θ t := by
  unfold positiveLongPolynomial longPositiveIndices longPolynomial
  exact sum_subtype_of_mem (p := fun l : ℕ => 0 < l)
    (fun l : ℕ => b ((d : ℕ) * l) * θ (l : ZMod r) *
      (l : ℂ) ^ (-(1 : ℂ) - I * (t : ℂ))) (fun l hl => longIndices_positive hl)

noncomputable def blockMoment (R : ℝ)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℂ) : ℝ :=
  ∑ r ∈ blockModuli R, ((r : ℝ) / (r.totient : ℝ)) *
    ∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ r => θ.IsPrimitive), ‖F r θ‖ ^ 2

noncomputable def blockConstant : ℝ := 16 * (33 + Real.pi ^ 2)
noncomputable def logWeight (X : ℝ) : ℝ := (1 + Real.log (8 * X)) ^ 25
noncomputable def longEnvelope (C_b : ℝ) (d : ℕ) (X : ℝ) : ℝ :=
  C_b ^ 2 * (lemma34Tau 5 d : ℝ) ^ 2 * logWeight X

theorem blockConstant_pos : 0 < blockConstant := by unfold blockConstant; positivity
theorem logWeight_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ logWeight X := by
  have hlog : 0 ≤ Real.log (8 * X) := Real.log_nonneg (by linarith)
  unfold logWeight
  positivity
theorem longEnvelope_nonneg (C_b : ℝ) (d : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ longEnvelope C_b d X := by
  unfold longEnvelope
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (logWeight_nonneg hX)

/-- The exceptional conductor-one contribution is included explicitly. -/
theorem blockMoment_le_one_add_nontrivial (R : ℝ)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℂ) :
    blockMoment R F ≤ ‖F 1 1‖ ^ 2 +
      ∑ r ∈ primitiveDyadicModuli R, ((r : ℝ) / (r.totient : ℝ)) *
        ∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ r => θ.IsPrimitive), ‖F r θ‖ ^ 2 := by
  let f : ℕ → ℝ := fun r => ((r : ℝ) / (r.totient : ℝ)) *
    ∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ r => θ.IsPrimitive), ‖F r θ‖ ^ 2
  have hsub : blockModuli R ⊆ insert 1 (primitiveDyadicModuli R) := by
    intro r hr
    have h := mem_blockModuli.mp hr
    by_cases h1 : r = 1
    · simp [h1]
    · apply mem_insert_of_mem
      exact mem_primitiveDyadicModuli.mpr ⟨by omega, h.2⟩
  have h1 : (1 : ℕ) ∉ primitiveDyadicModuli R := by simp [mem_primitiveDyadicModuli]
  have hone : f 1 = ‖F 1 1‖ ^ 2 := by
    have hprim : (univ : Finset (DirichletCharacter ℂ 1)).filter (fun θ => θ.IsPrimitive) = {1} := by
      ext θ
      have ht : θ = 1 := Subsingleton.elim _ _
      simp only [mem_filter, mem_univ, true_and, mem_singleton, ht,
        DirichletCharacter.isPrimitive_one_level_one]
    dsimp only [f]
    rw [hprim]
    simp
  change (∑ r ∈ blockModuli R, f r) ≤ _
  calc
    _ ≤ ∑ r ∈ insert 1 (primitiveDyadicModuli R), f r :=
      sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => mul_nonneg (by positivity)
        (sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by rw [sum_insert h1, hone]

end ZhangLS.Spec.DivisorConductorBlockMoments
