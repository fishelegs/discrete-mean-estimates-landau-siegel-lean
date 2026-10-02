import ZhangLS.Spec.Lemma23PrimitiveGaussSum
import ZhangLS.Spec.Lemma23CharacterOrthogonality
import ZhangLS.Spec.Lemma23GoodSet
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

lemma lemma33_primitive_nonprincipal {p : ℕ} [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro he
  have hc : χ.conductor = p := hχ
  rw [he,DirichletCharacter.conductor_one] at hc
  exact hp.ne_one hc.symm

lemma lemma33_prime_gauss_norm_square {p : ℕ} [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hg := gaussSum_mul_gaussSum_eq_card
    (lemma33_primitive_nonprincipal hp χ hχ) (ZMod.isPrimitive_stdAddChar p)
  rw [← star_gaussSum_eq χ ZMod.stdAddChar] at hg
  apply Complex.ofReal_injective
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self,mul_comm]
  simpa only [Complex.star_def,ZMod.card,Complex.ofReal_natCast] using hg

lemma lemma33_unit_character_mean_square_exact {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : ∀ a ∈ S, IsUnit a) (a : ZMod p → ℂ) :
    (∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ S, a n * ψ n‖ ^ 2) =
      (p.totient : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let K : Finset (ZMod p) := S
  let c : DirichletCharacter ℂ p → ZMod p → ℂ := fun ψ n => a n * ψ n
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hterm (ψ : DirichletCharacter ℂ p) :
      Complex.ofReal (‖∑ n ∈ K, c ψ n‖ ^ 2) =
        ∑ m ∈ K, ∑ n ∈ K, star (c ψ m) * c ψ n := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [c] using lemma23_complex_normSq_finset_sum K (fun n => c ψ n)
  have horth (m n : ZMod p) (hm : m ∈ K) (hn : n ∈ K) :
      (∑ ψ : DirichletCharacter ℂ p, star (ψ m) * ψ n) =
        if m = n then (p.totient : ℂ) else 0 := by
    have h := lemma23_dirichletCharacter_hermitian_orthogonality (b := m) (hS n hn)
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


noncomputable def lemma33AdditivePolynomial {p : ℕ} [NeZero p] (S : Finset ℕ)
    (a : ℕ → ℂ) (u : ZMod p) : ℂ :=
  ∑ n ∈ S, a n * ZMod.stdAddChar (u * (n : ZMod p))

lemma lemma33_gauss_finite_transform {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u) =
      gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ S, a n * χ (n : ZMod p)) := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def χ).mp hχ
  have hh (n : ℕ) : (∑ u : ZMod p, χ⁻¹ u * ZMod.stdAddChar (u * (n : ZMod p))) =
      χ (n : ZMod p) * gaussSum χ⁻¹ ZMod.stdAddChar := by
    simpa only [gaussSum,AddChar.mulShift_apply,inv_inv,mul_comm] using
      gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hi (n : ZMod p)
  calc
    _ = ∑ n ∈ S, a n * ∑ u : ZMod p, χ⁻¹ u * ZMod.stdAddChar (u * (n : ZMod p)) := by
      simp only [lemma33AdditivePolynomial,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = _ := by
      simp_rw [hh]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

lemma lemma33_gauss_finite_transform_norm_square {p : ℕ} [NeZero p]
    (hp : p.Prime) (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 =
      (p : ℝ) * ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2 := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def χ).mp hχ
  rw [lemma33_gauss_finite_transform χ hχ S a,norm_mul,mul_pow,
    lemma33_prime_gauss_norm_square hp χ⁻¹ hi]

lemma lemma33_unit_character_transform_parseval {p : ℕ} [NeZero p]
    (hp : p.Prime) (β : ZMod p → ℂ) :
    (∑ χ : DirichletCharacter ℂ p, ‖∑ u : ZMod p, β u * χ⁻¹ u‖ ^ 2) =
      (p.totient : ℝ) * ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)), ‖β u‖ ^ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let U : Finset (ZMod p) := Finset.univ.erase 0
  have hrow (χ : DirichletCharacter ℂ p) :
      (∑ u : ZMod p, β u * χ⁻¹ u) = ∑ u ∈ U, β u * χ⁻¹ u := by
    have h := Finset.sum_erase_add Finset.univ (fun u => β u * χ⁻¹ u) (Finset.mem_univ (0 : ZMod p))
    simpa only [U,MulChar.map_zero,mul_zero,add_zero] using h.symm
  simp_rw [hrow]
  calc
    _ = ∑ χ : DirichletCharacter ℂ p, ‖∑ u ∈ U, β u * χ u‖ ^ 2 := by
      exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ p => χ⁻¹)
        inv_involutive.bijective _ _ (fun χ => by simp)
    _ = _ := lemma33_unit_character_mean_square_exact hp U
      (fun u hu => isUnit_iff_ne_zero.mpr (Finset.mem_erase.mp hu).1) β

lemma lemma33_prime_primitive_mean_le_additive {p : ℕ} [NeZero p]
    (hp : p.Prime) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2) ≤
        ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)), ‖lemma33AdditivePolynomial S a u‖ ^ 2 := by
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  apply (mul_le_mul_iff_right₀ hpR).mp
  calc
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        (p : ℝ) * ‖∑ n ∈ S, a n * χ (n : ZMod p)‖ ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive),
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      exact (lemma33_gauss_finite_transform_norm_square hp χ (Finset.mem_filter.mp hχ).2 S a).symm
    _ ≤ ∑ χ : DirichletCharacter ℂ p,
        ‖∑ u : ZMod p, lemma33AdditivePolynomial S a u * χ⁻¹ u‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = (p.totient : ℝ) * ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
        ‖lemma33AdditivePolynomial S a u‖ ^ 2 :=
      lemma33_unit_character_transform_parseval hp (lemma33AdditivePolynomial S a)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le p)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end ZhangLS.Spec
