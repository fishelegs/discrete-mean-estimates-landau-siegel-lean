import ZhangLS.Spec.Lemma33GaussTransform
set_option autoImplicit false
namespace ZhangLS.Spec
open ComplexConjugate
open scoped Classical
set_option maxHeartbeats 2000000

/-- Primitive Gauss sums have squared norm equal to the level for every nontrivial level,
including composite levels. -/
theorem primitive_gauss_norm_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : N ≠ 1) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (N : ℝ) := by
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  let τInv : ℂ := gaussSum χ⁻¹ ZMod.stdAddChar
  have hproduct : τ * τInv = (N : ℂ) * χ (-1) := by
    simpa [τ, τInv] using lemma23_gaussSum_mul_inverse χ hχ hN
  have hminusSq : χ (-1) ^ 2 = 1 := by
    rw [← map_pow]
    simp
  have hminusProd : χ (-1) * χ (-1) = 1 := by
    simpa [pow_two] using hminusSq
  have hminusNe : χ (-1) ≠ 0 := by
    intro h
    rw [h] at hminusProd
    norm_num at hminusProd
  have hminusInv : (χ (-1))⁻¹ = χ (-1) := by
    calc
      (χ (-1))⁻¹ = (χ (-1))⁻¹ * 1 := by simp
      _ = (χ (-1))⁻¹ * (χ (-1) * χ (-1)) := by rw [hminusProd]
      _ = ((χ (-1))⁻¹ * χ (-1)) * χ (-1) := by ring
      _ = χ (-1) := by rw [inv_mul_cancel₀ hminusNe]; simp
  have hχInvMinus : χ⁻¹ (-1) = χ (-1) := by
    calc
      χ⁻¹ (-1) = (χ (-1))⁻¹ := MulChar.inv_apply_eq_inv' χ (-1)
      _ = χ (-1) := hminusInv
  have hshift0 : χ⁻¹ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ =
      gaussSum χ⁻¹ ZMod.stdAddChar := by
    rw [(ZMod.stdAddChar).inv_mulShift, ← Units.coe_neg_one]
    exact gaussSum_mulShift χ⁻¹ ZMod.stdAddChar (-1)
  have hshift0' : χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ = τInv := by
    simpa [τInv, hχInvMinus] using hshift0
  have hshift : χ (-1) * τInv =
      gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := by
    calc
      χ (-1) * τInv = χ (-1) *
          (χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹) := by rw [← hshift0']
      _ = gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := by
        calc
          _ = (χ (-1) * χ (-1)) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := by ring
          _ = gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := by rw [hminusProd]; simp
  have hconjTau : conj τ = χ (-1) * τInv := by
    calc
      conj τ = star τ := by rw [Complex.star_def]
      _ = gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := star_gaussSum_eq χ ZMod.stdAddChar
      _ = χ (-1) * τInv := hshift.symm
  have hnormSqComplex : (Complex.normSq τ : ℂ) = (N : ℂ) := by
    calc
      (Complex.normSq τ : ℂ) = conj τ * τ := Complex.normSq_eq_conj_mul_self
      _ = τ * conj τ := by ring
      _ = (N : ℂ) := by
        rw [hconjTau]
        calc
          τ * (χ (-1) * τInv) = χ (-1) * (τ * τInv) := by ring
          _ = χ (-1) * ((N : ℂ) * χ (-1)) := by rw [hproduct]
          _ = (N : ℂ) := by
            calc
              _ = (N : ℂ) * (χ (-1) * χ (-1)) := by ring
              _ = (N : ℂ) := by rw [hminusProd]; simp
  have hnormSq : Complex.normSq τ = N := by exact_mod_cast hnormSqComplex
  have hτsq : ‖τ‖ ^ 2 = (N : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq τ]
    exact hnormSq
  exact hτsq

theorem all_moduli_character_hermitian_orthogonality
    {q : ℕ} [NeZero q] {a b : ZMod q}
    (ha : IsUnit a) :
    (∑ ψ : DirichletCharacter ℂ q, ψ a * star (ψ b)) =
      if a = b then (q.totient : ℂ) else 0 := by
  calc
    (∑ ψ : DirichletCharacter ℂ q, ψ a * star (ψ b)) =
        ∑ ψ : DirichletCharacter ℂ q, ψ a * ψ⁻¹ b := by
          apply Finset.sum_congr rfl
          intro ψ hψ
          rw [MulChar.star_apply']
    _ = ∑ ψ : DirichletCharacter ℂ q, ψ⁻¹ a * ψ b := by
      exact Fintype.sum_bijective (fun ψ : DirichletCharacter ℂ q => ψ⁻¹)
        inv_involutive.bijective
        (fun ψ => ψ a * ψ⁻¹ b) (fun ψ => ψ⁻¹ a * ψ b)
        (fun ψ => by simp)
    _ = if a = b then (q.totient : ℂ) else 0 := by
      have hInv : Ring.inverse a = a⁻¹ := by
        rcases ha with ⟨u, rfl⟩
        rw [Ring.inverse_unit, ZMod.inv_coe_unit]
      simpa only [MulChar.inv_apply, hInv] using
        (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q) ha b)

lemma all_moduli_unit_character_mean_square_exact {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : ∀ a ∈ S, IsUnit a) (a : ZMod p → ℂ) :
    (∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ S, a n * ψ n‖ ^ 2) =
      (p.totient : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let K : Finset (ZMod p) := S
  let c : DirichletCharacter ℂ p → ZMod p → ℂ := fun ψ n => a n * ψ n
  have hterm (ψ : DirichletCharacter ℂ p) :
      Complex.ofReal (‖∑ n ∈ K, c ψ n‖ ^ 2) =
        ∑ m ∈ K, ∑ n ∈ K, star (c ψ m) * c ψ n := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [c] using lemma23_complex_normSq_finset_sum K (fun n => c ψ n)
  have horth (m n : ZMod p) (hm : m ∈ K) (hn : n ∈ K) :
      (∑ ψ : DirichletCharacter ℂ p, star (ψ m) * ψ n) =
        if m = n then (p.totient : ℂ) else 0 := by
    have h := all_moduli_character_hermitian_orthogonality (b := m) (hS n hn)
    simpa only [mul_comm,eq_comm] using h
  have hmain :
      Complex.ofReal
          (∑ ψ : DirichletCharacter ℂ p,
            ‖∑ n ∈ K, c ψ n‖ ^ 2) =
        (p.totient : ℂ) *
          ∑ n ∈ K, Complex.normSq (a n) := by
    calc
      Complex.ofReal
          (∑ ψ : DirichletCharacter ℂ p,
            ‖∑ n ∈ K, c ψ n‖ ^ 2) =
        ∑ ψ : DirichletCharacter ℂ p,
          ∑ m ∈ K, ∑ n ∈ K, star (c ψ m) * c ψ n := by
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro ψ hψ
            exact hterm ψ
      _ = ∑ m ∈ K, ∑ ψ : DirichletCharacter ℂ p,
            ∑ n ∈ K, star (c ψ m) * c ψ n := by
            rw [Finset.sum_comm]
      _ = ∑ m ∈ K, ∑ n ∈ K,
            ∑ ψ : DirichletCharacter ℂ p, star (c ψ m) * c ψ n := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.sum_comm]
      _ = ∑ m ∈ K, ∑ n ∈ K,
            (star (a m) * a n) *
              ∑ ψ : DirichletCharacter ℂ p,
                star (ψ m) * ψ n := by
            apply Finset.sum_congr rfl
            intro m hm
            apply Finset.sum_congr rfl
            intro n hn
            calc
              (∑ ψ : DirichletCharacter ℂ p,
                  star (c ψ m) * c ψ n) =
                ∑ ψ : DirichletCharacter ℂ p,
                  (star (a m) * a n) *
                    (star (ψ m) * ψ n) := by
                    apply Finset.sum_congr rfl
                    intro ψ hψ
                    simp only [c, star_mul]
                    ring
              _ = (star (a m) * a n) *
                    ∑ ψ : DirichletCharacter ℂ p,
                      star (ψ m) * ψ n := by
                    rw [← Finset.mul_sum]
      _ = ∑ m ∈ K, ∑ n ∈ K,
            (star (a m) * a n) *
              (if m = n then (p.totient : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro m hm
            apply Finset.sum_congr rfl
            intro n hn
            rw [horth m n hm hn]
      _ = ∑ m ∈ K, (star (a m) * a m) * (p.totient : ℂ) := by
            apply Finset.sum_congr rfl
            intro m hm
            simp [mul_ite, Finset.sum_ite_eq, hm]
      _ = (p.totient : ℂ) * ∑ n ∈ K, Complex.normSq (a n) := by
            rw [← Finset.sum_mul]
            rw [mul_comm]
            congr 1
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro n hn
            rw [Complex.star_def]
            exact Complex.normSq_eq_conj_mul_self.symm
  apply Complex.ofReal_injective
  simpa [K, Complex.normSq_eq_norm_sq] using hmain



/-- Restrict the Fourier-side sum to units: every Dirichlet character vanishes off them. -/
theorem all_moduli_unit_character_transform_parseval {p : ℕ} [NeZero p]
    (β : ZMod p → ℂ) :
    (∑ χ : DirichletCharacter ℂ p, ‖∑ u : ZMod p, β u * χ⁻¹ u‖ ^ 2) =
      (p.totient : ℝ) * ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod p)), ‖β u‖ ^ 2 := by
  classical
  let U : Finset (ZMod p) := Finset.univ.filter IsUnit
  have hrow (χ : DirichletCharacter ℂ p) :
      (∑ u : ZMod p, β u * χ⁻¹ u) = ∑ u ∈ U, β u * χ⁻¹ u := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _) 
    intro u hu hnot
    have hn : ¬ IsUnit u := by simpa [U] using hnot
    rw [MulChar.map_nonunit _ hn, mul_zero]
  simp_rw [hrow]
  calc
    _ = ∑ χ : DirichletCharacter ℂ p, ‖∑ u ∈ U, β u * χ u‖ ^ 2 := by
      exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ p => χ⁻¹)
        inv_involutive.bijective _ _ (fun χ => by simp)
    _ = _ := all_moduli_unit_character_mean_square_exact U
      (fun u hu => (Finset.mem_filter.mp hu).2) β

/-- The primitive multiplicative transform at any nontrivial nonzero modulus. -/
theorem all_moduli_gauss_finite_transform_norm_square {p : ℕ} [NeZero p]
    (hp : p ≠ 1) (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 =
      (p : ℝ) * ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2 := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def χ).mp hχ
  rw [lemma33_gauss_finite_transform χ hχ S a,norm_mul,mul_pow,
    primitive_gauss_norm_square χ⁻¹ hi hp]

/-- The complete primitive-character family is bounded by the additive samples at reduced
residues, uniformly for every nontrivial modulus, with no primality hypothesis. -/
theorem all_moduli_primitive_mean_le_additive {p : ℕ} [NeZero p]
    (hp : p ≠ 1) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) ≤
        ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod p)),
          ‖lemma33AdditivePolynomial S a u‖ ^ 2 := by
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (mul_le_mul_iff_right₀ hpR).mp
  calc
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        (p : ℝ) * ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      exact (all_moduli_gauss_finite_transform_norm_square hp χ
        (Finset.mem_filter.mp hχ).2 S a).symm
    _ ≤ ∑ χ : DirichletCharacter ℂ p,
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = (p.totient : ℝ) * ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod p)),
        ‖lemma33AdditivePolynomial S a u‖ ^ 2 :=
      all_moduli_unit_character_transform_parseval (lemma33AdditivePolynomial S a)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le p)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Exact modulus/totient normalization before discarding the standard sieve weight. -/
theorem all_moduli_primitive_mean_mul_le_additive {p : ℕ} [NeZero p]
    (hp : p ≠ 1) (S : Finset ℕ) (a : ℕ → ℂ) :
    (p : ℝ) * (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) ≤
        (p.totient : ℝ) * ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod p)),
          ‖lemma33AdditivePolynomial S a u‖ ^ 2 := by
  classical
  calc
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        (p : ℝ) * ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      exact (all_moduli_gauss_finite_transform_norm_square hp χ
        (Finset.mem_filter.mp hχ).2 S a).symm
    _ ≤ ∑ χ : DirichletCharacter ℂ p,
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = (p.totient : ℝ) * ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod p)),
        ‖lemma33AdditivePolynomial S a u‖ ^ 2 :=
      all_moduli_unit_character_transform_parseval (lemma33AdditivePolynomial S a)

/-- The standard `q/φ(q)`-weighted primitive mean is bounded by the reduced additive samples. -/
theorem all_moduli_primitive_mean_weighted_le_additive {p : ℕ} [NeZero p]
    (hp : p ≠ 1) (S : Finset ℕ) (a : ℕ → ℂ) :
    ((p : ℝ) / p.totient) *
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) ≤
      ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod p)),
        ‖lemma33AdditivePolynomial S a u‖ ^ 2 := by
  have hφ : 0 < (p.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  apply (mul_le_mul_iff_right₀ hφ).mp
  convert all_moduli_primitive_mean_mul_le_additive hp S a using 1 <;> field_simp

end ZhangLS.Spec
