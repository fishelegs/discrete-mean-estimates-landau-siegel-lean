import FixedQuadratic.Complexification
import FixedQuadratic.PrimitiveHeight

open Polynomial
namespace FixedQuadratic

/-- Every nonrational element is moved by the unique nontrivial conjugation
of the fixed real quadratic field. -/
theorem real_quadratic_conjugation_moves (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) (β : F)
    (hβ : (minpoly ℚ (β : ℝ)).natDegree = 2) : σ β ≠ β := by
  classical
  letI := real_quadratic_isGalois F hF
  have hc : Fintype.card (F ≃ₐ[ℚ] F) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hF]
  have hu : (Finset.univ : Finset (F ≃ₐ[ℚ] F)) = {1, σ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hc, Finset.card_pair hσ.symm]
  intro hfix
  have hf : ∀ f : F ≃ₐ[ℚ] F, f β = β := by
    intro f
    have hm : f ∈ ({1, σ} : Finset (F ≃ₐ[ℚ] F)) := hu ▸ Finset.mem_univ f
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · rfl
    · exact hfix
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed β).mpr hf
  have hqr : (algebraMap ℚ ℝ) q = (β : ℝ) := by
    have hh := congrArg (fun x : F => (x : ℝ)) hq
    exact hh
  have hd := (minpoly.natDegree_eq_one_iff (A := ℚ) (x := (β : ℝ))).mpr ⟨q, hqr⟩
  omega

/-- The simultaneous field involution gives exactly the other root of each
actual primitive minpoly, independently of all coordinate dependencies. -/
theorem real_quadratic_conjugate_eq (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) (β : F)
    (hβ : (minpoly ℚ (β : ℝ)).natDegree = 2) :
    (σ β : ℝ) = primitiveConjugate (β : ℝ) := by
  have he : minpoly ℚ (σ β : ℝ) = minpoly ℚ (β : ℝ) := by
    exact (minpoly.algHom_eq F.val F.val.injective (σ β)).trans
      ((minpoly.algEquiv_eq σ β).trans (minpoly.algHom_eq F.val F.val.injective β).symm)
  have hd : minpoly ℚ (σ β : ℝ) ∣
      (primitiveMinpoly (β : ℝ)).map (algebraMap ℤ ℚ) := by
    rw [he]
    exact (primitiveMinpoly_map_associated (β : ℝ) hβ).dvd
  have hr := (minpoly.dvd_iff (A := ℚ) (x := (σ β : ℝ))).mp hd
  rw [aeval_map_algebraMap] at hr
  have hr' : eval (σ β : ℝ) ((primitiveMinpoly (β : ℝ)).map (algebraMap ℤ ℝ)) = 0 := by
    rw [eval_map]
    exact hr
  have hp := congrArg (Polynomial.eval (σ β : ℝ))
    (primitiveMinpoly_real_factorization (β : ℝ) hβ)
  rw [hr'] at hp
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hp
  have ha : ((primitiveMinpoly (β : ℝ)).coeff 2 : ℝ) ≠ 0 := by
    exact_mod_cast (primitiveMinpoly_coeff_two_pos (β : ℝ) hβ).ne'
  have hn : (σ β : ℝ)-(β : ℝ) ≠ 0 := by
    intro hh
    apply real_quadratic_conjugation_moves F hF σ hσ β hβ
    apply Subtype.ext
    exact sub_eq_zero.mp hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hp.symm).resolve_left ha)).resolve_left hn)

/-- Actual primitive root-pair data in F(i), for the single simultaneous
conjugation constructed from the fixed real field. -/
theorem complexification_primitive_factorization (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) (β : F)
    (hβ : (minpoly ℚ (β : ℝ)).natDegree = 2) :
    C ((primitiveMinpoly (β : ℝ)).coeff 2 : Complexification F)*X^2+
    C ((primitiveMinpoly (β : ℝ)).coeff 1 : Complexification F)*X+
    C ((primitiveMinpoly (β : ℝ)).coeff 0 : Complexification F) =
      C ((primitiveMinpoly (β : ℝ)).coeff 2 : Complexification F)*
        ((X-C (algebraMap F (Complexification F) β))*
          (X-C (complexificationConjugation F σ (algebraMap F (Complexification F) β)))) := by
  obtain ⟨hb, hc⟩ := primitiveMinpoly_root_relations (β : ℝ) hβ
  rw [← real_quadratic_conjugate_eq F hF σ hσ β hβ] at hb hc
  have hbF : ((primitiveMinpoly (β : ℝ)).coeff 1 : F) =
      -((primitiveMinpoly (β : ℝ)).coeff 2 : F)*(β+σ β) := by
    apply Subtype.ext
    exact_mod_cast hb
  have hcF : ((primitiveMinpoly (β : ℝ)).coeff 0 : F) =
      ((primitiveMinpoly (β : ℝ)).coeff 2 : F)*β*(σ β) := by
    apply Subtype.ext
    exact_mod_cast hc
  have hbK := congrArg (algebraMap F (Complexification F)) hbF
  have hcK := congrArg (algebraMap F (Complexification F)) hcF
  simp only [map_intCast, map_neg, map_mul, map_add] at hbK hcK
  have ht : complexificationConjugation F σ (algebraMap F (Complexification F) β) =
      algebraMap F (Complexification F) (σ β) := by
    ext <;> simp [complexificationConjugation]
  rw [ht, hbK, hcK]
  simp only [map_neg, map_mul, map_add]
  ring

theorem complexification_real_eval (F : IntermediateField ℚ ℝ) (β : F) :
    complexificationToComplex F (algebraMap F (Complexification F) β) = (β : ℝ) := by
  rw [complexificationToComplex_apply]
  simp

theorem complexification_primitive_mahler (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) (β : F)
    (hβ : (minpoly ℚ (β : ℝ)).natDegree = 2) :
    ‖complexificationToComplex F ((primitiveMinpoly (β : ℝ)).coeff 2 : Complexification F)‖*
      max 1 ‖complexificationToComplex F (algebraMap F (Complexification F) β)‖*
      max 1 ‖complexificationToComplex F
        (complexificationConjugation F σ (algebraMap F (Complexification F) β))‖ =
      quadraticMahler ((primitiveMinpoly (β : ℝ)).coeff 2 : ℝ) (β : ℝ)
        (primitiveConjugate (β : ℝ)) := by
  have ht : complexificationConjugation F σ (algebraMap F (Complexification F) β) =
      algebraMap F (Complexification F) (σ β) := by
    ext <;> simp [complexificationConjugation]
  rw [ht, complexification_real_eval, complexification_real_eval,
    real_quadratic_conjugate_eq F hF σ hσ β hβ, map_intCast]
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast]
  unfold quadraticMahler
  have ha : 0 ≤ ((primitiveMinpoly (β : ℝ)).coeff 2 : ℝ) := by
    exact_mod_cast (primitiveMinpoly_coeff_two_pos (β : ℝ) hβ).le
  rw [abs_of_nonneg ha]

end FixedQuadratic
