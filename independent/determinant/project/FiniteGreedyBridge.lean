import OAI.NumberTheory.SiegelZeros.Selection.GreedyPivotsWeightLowSpan
import OAI.NumberTheory.SiegelZeros.Structure.InvariantJetLinearMap
import OAI.NumberTheory.SiegelZeros.Determinants.NormSqReal

/-!
# Finite same-witness determinant bridge

The selected row embedding is never replaced. Its range is identified with the finite
Greedy pivot set, the rectangle bounds are applied to that set, and the sums are
transported back along the original embedding. The final theorem applies both norm
bounds to the integral determinant returned by the finite source theorem.

This file is an adapter over the three imports above; its statements expose their
arithmetic, geometric, and size hypotheses.
-/

namespace OAI.SiegelZeros.WeightedTorusJets

open scoped BigOperators NumberField

/-- The range identity for the original row embedding gives the exact finite set. -/
theorem finiteGreedyPivots_univ_map_eq_of_range
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {m : ℕ} (s : Finset (Fin 3 → ℕ)) (R : (Fin 3 → ℕ) → V)
    (e : Fin s.card ≃ s) (α : Fin m ↪ (Fin 3 → ℕ))
    (hα : Set.range α = (finiteGreedyPivots K s R e 0 : Set (Fin 3 → ℕ))) :
    Finset.univ.map α = finiteGreedyPivots K s R e 0 := by
  classical
  apply Finset.coe_injective
  rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
  exact hα

/-- Rectangle spanning bounds the sums over the very same finite greedy rows.
The low-weight hypothesis is proved only for the pivot set, not assumed for the
larger original weight ball. -/
theorem same_finite_greedy_pivot_sum_bounds
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (R : (Fin 3 → ℕ) → V)
    (e : Fin (weightedJetIndices H (N ^ 4 - 1)).card ≃
      weightedJetIndices H (N ^ 4 - 1))
    (hsort : Monotone (fun i => (e i).1 0 + H * (e i).1 1 + H * (e i).1 2))
    (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ))
    (hα : Set.range α =
      (finiteGreedyPivots K (weightedJetIndices H (N ^ 4 - 1)) R e 0 :
        Set (Fin 3 → ℕ)))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ i, (α i 0 : ℝ) ∧
      (∑ i, ((α i 1 : ℝ) + α i 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  let P := finiteGreedyPivots K (weightedJetIndices H (N ^ 4 - 1)) R e 0
  have hmap : Finset.univ.map α = P :=
    finiteGreedyPivots_univ_map_eq_of_range _ R e α hα
  have hcard : P.card = N ^ 4 := by
    rw [← hmap]
    simp
  have hw := fixed_first_greedy_rectangle_weight_bound H N hH R e hsort hspan
  have hbounds := weighted_pivot_bounds P H N hH hHN hN hcard hw
  have hsum₁ := sum_embedding_eq_sum_finset_of_range α P hα
    (fun a => (a 0 : ℝ))
  have hsum₂ := sum_embedding_eq_sum_finset_of_range α P hα
    (fun a => (a 1 : ℝ) + a 2)
  constructor
  · rw [hsum₁]
    exact hbounds.1
  · rw [hsum₂]
    exact hbounds.2

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

/-- A primitive real character can have the lifted square-root-of-two field only
at level eight. This exclusion has no real-zero or small-L-value hypothesis. -/
theorem source_character_field_ne_sqrtTwo_of_ne_eight (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hq8 : q ≠ 8) :
    characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ) := by
  intro hfield
  let L := CyclotomicField (8 * q) ℚ
  let ζ : L := IsCyclotomicExtension.zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  have hroot : (ζ - ζ ^ 3) ^ 2 = (2 : L) :=
    sourceSqrtTwoField_root_sq q L
  have hfield' : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) =
        IntermediateField.adjoin ℚ {ζ - ζ ^ 3} := by
    simpa only [sourceSqrtTwoField, ζ, L] using hfield
  exact hq8 (primitive_level_eq_eight_of_lifted_sqrt_two_field
    (dvd_mul_left q 8) (dvd_mul_right 8 q) χ hprim
    (real_character_isQuadratic χ hreal) (ζ - ζ ^ 3) hroot hfield')

/-- The conductor range used in the explicit determinant estimate eliminates the
only square-root-of-two field exception. -/
theorem source_character_field_ne_sqrtTwo_of_ninety_seven_le (q : ℕ) [NeZero q]
    (hq : 97 ≤ q) (χ : DirichletCharacter ℂ q)
    (hreal : ∀ x : ZMod q, (χ x).im = 0) (hprim : χ.IsPrimitive) :
    characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ) := by
  exact source_character_field_ne_sqrtTwo_of_ne_eight q χ hreal hprim (by omega)

/-- The finite source theorem, rectangle theorem, and both norm estimates share one
arithmetic witness, one finite selected row embedding, and one integral determinant.
The finite sorted enumeration remains an explicit parameter, with existence supplied
by `exists_weight_sorted_enumeration`; no global enumeration is required. -/
theorem source_character_finite_greedy_determinant_same_witness_bounds (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N → 18818 ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
                let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ β) s.card : Set ℕ) ∧
                  (∀ i, α i = β (g i)) ∧
                  Set.range α = (finiteGreedyPivots B s R e 0 : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  ((N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) *
                      (N : ℝ) ^ (4 / 3 : ℝ) / (4 * 97 ^ 2) ≤
                      ∑ i, (α i 0 : ℝ)) ∧
                  ((∑ i, ((α i 1 : ℝ) + α i 2)) ≤
                    192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) *
                      (N : ℝ) ^ (4 / 3 : ℝ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    ∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_fixed_greedy_determinant_divisibility_of_field_ne
      q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN hN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e he
  let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hninj : Function.Injective (fun j i => (n j i : ℕ)) := by
    intro x y h
    apply n.injective
    funext i
    apply Fin.ext
    exact congrFun h i
  have hrectangle := actual_biquadratic_rectangle_span a' b' v hv σ τ
    hσa hσb hτa hτb H N hH hHN
    (fun j i => (n j i : ℕ)) hninj (fun j i => (n j i).isLt)
  have hpivots := same_finite_greedy_pivot_sum_bounds H N hH hHN hN
    _ e he α hrange hrectangle
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hpivots.1, hpivots.2,
    Δ, hΔ, hneΔ, ?_, hdiv, ?_⟩
  · have ha' : a' ^ 2 = (d : B) := by
      apply Subtype.ext
      exact ha
    have hb' : b' ^ 2 = (2 : B) := by
      apply Subtype.ext
      exact hb
    have hdreal : |(d : ℝ)| ≤ q := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using
        (show (d.natAbs : ℝ) ≤ q from Nat.cast_le.mpr hbound)
    exact archimedean_bound_of_integral_jet_determinant hdegree σ.toRingHom τ.toRingHom
      ha' hb' hdreal (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (hH.trans_le hHN)
      (fun j i => (n j i : ℕ)) (fun j i => (n j i).isLt) α Δ hneΔ hΔ
  · intro U hU
    simpa only [Nat.cast_pow] using finite_place_bounds_of_source_determinant hdegree
      Δ hneΔ α q H (fun p => χ p) hdiv U hU

/-- The same finite determinant bridge for conductor at least 97, with the field
exception discharged. All finite parameter, coordinate, and sorting inputs are
retained explicitly in the conclusion. -/
theorem source_character_finite_greedy_determinant_same_witness_bounds_of_ninety_seven_le (q : ℕ) [NeZero q]
    (hq : 97 ≤ q)
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N → 18818 ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
                let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ β) s.card : Set ℕ) ∧
                  (∀ i, α i = β (g i)) ∧
                  Set.range α = (finiteGreedyPivots B s R e 0 : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  ((N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) *
                      (N : ℝ) ^ (4 / 3 : ℝ) / (4 * 97 ^ 2) ≤
                      ∑ i, (α i 0 : ℝ)) ∧
                  ((∑ i, ((α i 1 : ℝ) + α i 2)) ≤
                    192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) *
                      (N : ℝ) ^ (4 / 3 : ℝ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    ∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) := by
  exact source_character_finite_greedy_determinant_same_witness_bounds q χ hreal hprim hne
    (source_character_field_ne_sqrtTwo_of_ninety_seven_le q hq χ hreal hprim)

#check source_character_field_ne_sqrtTwo_of_ne_eight
#print axioms source_character_field_ne_sqrtTwo_of_ne_eight
#check source_character_field_ne_sqrtTwo_of_ninety_seven_le
#print axioms source_character_field_ne_sqrtTwo_of_ninety_seven_le
#check source_character_finite_greedy_determinant_same_witness_bounds_of_ninety_seven_le
#print axioms source_character_finite_greedy_determinant_same_witness_bounds_of_ninety_seven_le
#check same_finite_greedy_pivot_sum_bounds
#print axioms same_finite_greedy_pivot_sum_bounds
#check source_character_finite_greedy_determinant_same_witness_bounds
#print axioms source_character_finite_greedy_determinant_same_witness_bounds

end OAI.SiegelZeros.WeightedTorusJets
