import ZhangLS.Spec.AllModuliLargeSieve
namespace ZhangLS.Spec
open scoped Classical

-- The true primitive Gauss normalization is available at composite levels.
example (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = 4 := by
  simpa using primitive_gauss_norm_square χ hχ (by norm_num : (4:ℕ) ≠ 1)
example (χ : DirichletCharacter ℂ 9) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = 9 := by
  simpa using primitive_gauss_norm_square χ hχ (by norm_num : (9:ℕ) ≠ 1)

-- Nonzero nonunits must vanish, not be treated as prime-level nonzero residues.
example (χ : DirichletCharacter ℂ 8) : χ (2 : ZMod 8) = 0 := by
  apply MulChar.map_nonunit
  rw [show (2:ZMod 8) = ((2:ℕ):ZMod 8) from rfl, ZMod.isUnit_iff_coprime]
  decide
example (χ : DirichletCharacter ℂ 9) : χ (3 : ZMod 9) = 0 := by
  apply MulChar.map_nonunit
  rw [show (3:ZMod 9) = ((3:ℕ):ZMod 9) from rfl, ZMod.isUnit_iff_coprime]
  decide

-- Orthogonality at distinct units of a composite modulus is genuinely diagonal.
example : (∑ χ : DirichletCharacter ℂ 8, χ (3:ZMod 8) * star (χ (5:ZMod 8))) = 0 := by
  have hu : IsUnit (3:ZMod 8) := by
    rw [show (3:ZMod 8) = ((3:ℕ):ZMod 8) from rfl, ZMod.isUnit_iff_coprime]
    decide
  simpa using all_moduli_character_hermitian_orthogonality (b := (5:ZMod 8)) hu
example : (∑ χ : DirichletCharacter ℂ 8, χ (3:ZMod 8) * star (χ (3:ZMod 8))) = 4 := by
  have hu : IsUnit (3:ZMod 8) := by
    rw [show (3:ZMod 8) = ((3:ℕ):ZMod 8) from rfl, ZMod.isUnit_iff_coprime]
    decide
  simpa using all_moduli_character_hermitian_orthogonality (b := (3:ZMod 8)) hu

-- Distinct reduced fractions of composite denominators satisfy the same separation.
example : 1 / ((4:ℝ)*9) ≤ |(1:ℝ)/4 - (2:ℝ)/9| := by
  simpa using reduced_fraction_separation (p := 4) (q := 9) (a := 1) (b := 2) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)

-- Actual dyadic boundaries and composite membership.
example : (4:ℕ) ∈ primitiveDyadicModuli 3 := by rw [mem_primitiveDyadicModuli]; norm_num
example : (6:ℕ) ∈ primitiveDyadicModuli 4 := by rw [mem_primitiveDyadicModuli]; norm_num
example : (4:ℕ) ∈ primitiveDyadicModuli 4 := by rw [mem_primitiveDyadicModuli]; norm_num
example : (8:ℕ) ∉ primitiveDyadicModuli 4 := by rw [mem_primitiveDyadicModuli]; norm_num
example : (1:ℕ) ∉ primitiveDyadicModuli 1 := by rw [mem_primitiveDyadicModuli]; norm_num
example : primitiveDyadicModuli 1 = ∅ := by
  ext q
  simp only [mem_primitiveDyadicModuli, Finset.notMem_empty, iff_false]
  rintro ⟨hq, hlo, hhi⟩
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  norm_num at hhi
  linarith
example {R : ℝ} (hR : R ≤ 0) : primitiveDyadicModuli R = ∅ := by
  ext q
  simp only [mem_primitiveDyadicModuli, Finset.notMem_empty, iff_false]
  rintro ⟨hq, hlo, hhi⟩
  have hqR : (0:ℝ) ≤ q := Nat.cast_nonneg q
  linarith

-- The final large sieve has no positive-length assumption and remains correct for empty support.
example {R : ℝ} (hR : 1 ≤ R) (a : ℕ → ℂ) (M : ℕ) :
    (∑ q ∈ primitiveDyadicModuli R,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
        ‖∑ n ∈ (∅ : Finset ℕ), a n * χ (n : ZMod q)‖ ^ 2) ≤
      (32 + Real.pi ^ 2) * (R ^ 2 + (0 : ℝ)) * ∑ n ∈ (∅ : Finset ℕ), ‖a n‖ ^ 2 := by
  simpa only [Nat.cast_zero] using primitive_dyadic_large_sieve hR ∅ a M 0 (by simp)
example (S : Finset ℕ) (M : ℕ) (hS : ∀ n ∈ S, M < n ∧ n ≤ M+0) : S = ∅ := by
  ext n
  simp only [Finset.notMem_empty, iff_false]
  intro hn
  have := hS n hn
  omega

-- A coefficient at a nonunit is allowed; the theorem does not assume coprimality of support.
example (a : ℕ → ℂ) :
    (∑ q ∈ ({4,8} : Finset ℕ), ∑ χ ∈ Finset.univ.filter
      (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
        ‖∑ n ∈ ({6,7,8} : Finset ℕ), a n * χ (n : ZMod q)‖ ^ 2) ≤
      (32 + Real.pi ^ 2) * (4 ^ 2 + (3 : ℝ)) * ∑ n ∈ ({6,7,8} : Finset ℕ), ‖a n‖ ^ 2 := by
  exact primitive_large_sieve_finset _
    (by intro q hq; simp at hq; rcases hq with rfl | rfl <;> norm_num)
    _ a (by norm_num : (1:ℝ) ≤ 4)
    (by intro q hq; simp at hq; rcases hq with rfl | rfl <;> norm_num) 5 3
    (by intro n hn; simp at hn; rcases hn with rfl | rfl | rfl <;> norm_num)
end ZhangLS.Spec

#print axioms ZhangLS.Spec.primitive_gauss_norm_square
#print axioms ZhangLS.Spec.all_moduli_character_hermitian_orthogonality
#print axioms ZhangLS.Spec.all_moduli_unit_character_mean_square_exact
#print axioms ZhangLS.Spec.all_moduli_unit_character_transform_parseval
#print axioms ZhangLS.Spec.all_moduli_gauss_finite_transform_norm_square
#print axioms ZhangLS.Spec.all_moduli_primitive_mean_le_additive
#print axioms ZhangLS.Spec.all_moduli_primitive_mean_mul_le_additive
#print axioms ZhangLS.Spec.all_moduli_primitive_mean_weighted_le_additive
#print axioms ZhangLS.Spec.reduced_fraction_cross_ne
#print axioms ZhangLS.Spec.reduced_fraction_separation
#print axioms ZhangLS.Spec.trig_sum_shift_norm
#print axioms ZhangLS.Spec.shifted_additive_large_sieve
#print axioms ZhangLS.Spec.all_moduli_sample_bounds
#print axioms ZhangLS.Spec.all_moduli_samples_separated
#print axioms ZhangLS.Spec.all_moduli_primitive_large_sieve
#print axioms ZhangLS.Spec.primitive_large_sieve_finset
#print axioms ZhangLS.Spec.mem_primitiveDyadicModuli
#print axioms ZhangLS.Spec.primitive_dyadic_large_sieve
#print axioms ZhangLS.Spec.all_moduli_primitive_large_sieve_weighted
#print axioms ZhangLS.Spec.primitive_large_sieve_finset_weighted
#print axioms ZhangLS.Spec.primitiveDyadicModuli_eq_empty_of_le_one
