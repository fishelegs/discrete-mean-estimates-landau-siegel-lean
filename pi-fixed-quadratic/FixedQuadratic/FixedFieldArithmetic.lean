import FixedQuadratic.FieldMinpoly
import FixedQuadratic.ArithmeticErrors

open scoped BigOperators
namespace FixedQuadratic

/-- Actual same-field norm integrality, instantiated in the constructed F(i).
No fraction-field, relative-degree, involution or root-pair hypotheses remain. -/
theorem fixed_real_field_norm_integral (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) {m : ℕ}
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (P : MvPolynomial (Fin m) GaussianInt) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i) :
    (∏ i, ((primitiveMinpoly (β i : ℝ)).coeff 2 : Complexification F)^e i)*
      MvPolynomial.eval₂ (algebraMap GaussianInt (Complexification F))
        (fun i => algebraMap F (Complexification F) (β i)) P*
      MvPolynomial.eval₂ (algebraMap GaussianInt (Complexification F))
        (fun i => complexificationConjugation F σ (algebraMap F (Complexification F) (β i))) P ∈
      (algebraMap GaussianInt (Complexification F)).range := by
  letI := complexification_isGalois F hF
  exact quadratic_cleared_product_gaussian (complexification_relative_degree F hF)
    (complexificationConjugation F σ) (complexificationConjugation_ne_one F σ hσ) P
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 2)
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 1)
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 0)
    (fun i => algebraMap F (Complexification F) (β i)) e he
    (fun i => primitiveMinpoly_three_gcd (β i : ℝ) (hβ i))
    (fun i => complexification_primitive_factorization F hF σ hσ (β i) (hβ i))

/-- The norm/Mahler lower bound for arbitrary dependent coordinates in one
actual fixed real quadratic field, with the actual primitive minpolys. -/
theorem fixed_real_field_multi_mahler_lower (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) {m : ℕ}
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (P : MvPolynomial (Fin m) GaussianInt) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hne : MvPolynomial.eval₂ GaussianInt.toComplex (fun i => ((β i : ℝ) : ℂ)) P ≠ 0) :
    (∏ i, (max 1 |(β i : ℝ)|)^e i)/
      (multiCoefficientL1 (MvPolynomial.map GaussianInt.toComplex P)*
        ∏ i, (quadraticMahler ((primitiveMinpoly (β i : ℝ)).coeff 2 : ℝ)
          (β i : ℝ) (primitiveConjugate (β i : ℝ)))^e i) ≤
      ‖MvPolynomial.eval₂ GaussianInt.toComplex (fun i => ((β i : ℝ) : ℂ)) P‖ := by
  obtain ⟨σ, hσ⟩ := exists_real_quadratic_conjugation F hF
  letI := complexification_isGalois F hF
  have hEval : complexificationToComplex F
      (MvPolynomial.eval₂ (algebraMap GaussianInt (Complexification F))
        (fun i => algebraMap F (Complexification F) (β i)) P) =
      MvPolynomial.eval₂ GaussianInt.toComplex (fun i => ((β i : ℝ) : ℂ)) P := by
    rw [MvPolynomial.eval₂_comp_left, complexificationToComplex_compatible]
    congr 1
    funext i
    exact complexification_real_eval F (β i)
  have hx : MvPolynomial.eval₂ (algebraMap GaussianInt (Complexification F))
      (fun i => algebraMap F (Complexification F) (β i)) P ≠ 0 := by
    intro hz
    apply hne
    rw [← hEval, hz, map_zero]
  have hh := quadratic_multi_l1_mahler_lower (complexification_relative_degree F hF)
    (complexificationConjugation F σ) (complexificationConjugation_ne_one F σ hσ) P
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 2)
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 1)
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 0)
    (fun i => algebraMap F (Complexification F) (β i)) e he
    (fun i => primitiveMinpoly_three_gcd (β i : ℝ) (hβ i))
    (fun i => complexification_primitive_factorization F hF σ hσ (β i) (hβ i))
    (fun i => (primitiveMinpoly_coeff_two_pos (β i : ℝ) (hβ i)).ne') hx
    (complexificationToComplex F) (complexificationToComplex_compatible F)
  rw [hEval] at hh
  have hM : ∀ i, ‖complexificationToComplex F
      ((primitiveMinpoly (β i : ℝ)).coeff 2 : Complexification F)‖*
      max 1 ‖complexificationToComplex F (algebraMap F (Complexification F) (β i))‖*
      max 1 ‖complexificationToComplex F (complexificationConjugation F σ
        (algebraMap F (Complexification F) (β i)))‖ =
      quadraticMahler ((primitiveMinpoly (β i : ℝ)).coeff 2 : ℝ)
        (β i : ℝ) (primitiveConjugate (β i : ℝ)) :=
    fun i => complexification_primitive_mahler F hF σ hσ (β i) (hβ i)
  simp_rw [hM, complexification_real_eval, Complex.norm_real, Real.norm_eq_abs] at hh
  exact hh

/-- Primitive maximum-coefficient height replaces the actual Mahler measure,
with one l1 coefficient cost. No Weil-height convention is substituted. -/
theorem fixed_real_field_multi_height_lower (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) {m : ℕ}
    (β : Fin m → F) (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (P : MvPolynomial (Fin m) GaussianInt) (e : Fin m → ℕ)
    (he : ∀ i, P.degreeOf i ≤ e i)
    (hne : MvPolynomial.eval₂ GaussianInt.toComplex (fun i => ((β i : ℝ) : ℂ)) P ≠ 0) :
    (∏ i, (max 1 |(β i : ℝ)|)^e i) ≤
      multiCoefficientL1 (MvPolynomial.map GaussianInt.toComplex P)*
      (∏ i, (Real.sqrt 3*(primitiveMinpolyHeight (β i : ℝ) : ℝ))^e i)*
      ‖MvPolynomial.eval₂ GaussianInt.toComplex (fun i => ((β i : ℝ) : ℂ)) P‖ := by
  let B := multiCoefficientL1 (MvPolynomial.map GaussianInt.toComplex P)
  let M := fun i => quadraticMahler ((primitiveMinpoly (β i : ℝ)).coeff 2 : ℝ)
    (β i : ℝ) (primitiveConjugate (β i : ℝ))
  have hB : 0 < B := multiCoefficientL1_pos_of_eval_ne_zero _ _ (by
    rw [MvPolynomial.eval_map]
    exact hne)
  have hM : ∀ i, 0 < M i := by
    intro i
    have ha : 0 < ((primitiveMinpoly (β i : ℝ)).coeff 2 : ℝ) := by
      exact_mod_cast primitiveMinpoly_coeff_two_pos (β i : ℝ) (hβ i)
    exact mul_pos (mul_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hh := fixed_real_field_multi_mahler_lower F hF β hβ P e he hne
  have hden : 0 < B*∏ i, (M i)^e i :=
    mul_pos hB (Finset.prod_pos (fun i _ => pow_pos (hM i) _))
  have hl := (div_le_iff₀ hden).mp hh
  have hprod : (∏ i, (M i)^e i) ≤
      ∏ i, (Real.sqrt 3*(primitiveMinpolyHeight (β i : ℝ) : ℝ))^e i := by
    apply Finset.prod_le_prod₀ (fun i _ => (pow_pos (hM i) _).le)
    intro i hi
    exact pow_le_pow_left₀ (hM i).le (primitiveMinpoly_mahler_le (β i : ℝ) (hβ i)) _
  have hp := mul_le_mul_of_nonneg_left hprod hB.le
  have hn := norm_nonneg (MvPolynomial.eval₂ GaussianInt.toComplex (fun i => ((β i : ℝ) : ℂ)) P)
  calc
    _ ≤ (B*∏ i, (M i)^e i)*‖MvPolynomial.eval₂ GaussianInt.toComplex
          (fun i => ((β i : ℝ) : ℂ)) P‖ := by simpa only [mul_comm] using hl
    _ ≤ _ := mul_le_mul_of_nonneg_right hp hn

/-- The actual height-linked minor bound in an actual fixed real quadratic
field. All arithmetic structure obligations are now discharged. Only the
explicit legal-packet budgets and actual nonzero minor remain as inputs. -/
theorem fixed_real_field_minor_normalized_lower (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (β : Fin m → F)
    (hβ : ∀ i, (minpoly ℚ (β i : ℝ)).natDegree = 2)
    (T : Fin m → ℕ) (k : ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ)
    (hj : ∀ r, j r ≤ k)
    (hne : MvPolynomial.eval (fun i => ((β i : ℝ) : ℂ)) (formalMinor T j s h b a) ≠ 0)
    (scale v w0 wmin D rebate : ℝ)
    (hscale : 0 ≤ scale) (hv : 0 < v) (hw0 : 0 < w0) (hwmin : 0 < wmin) (hD : 0 < D)
    (hw : ∀ i, wmin ≤ (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℝ))
    (hT : ∀ i, (T i : ℝ) ≤ scale*
      (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℝ)/v+1)
    (hjoint : ∑ i, (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℝ)*
      (minorDegrees a b i : ℝ) ≤ D*(1-rebate)) (hrebate : 0 ≤ rebate)
    (hs : (∑ r, s r : ℕ) ≤ D/v) (hh : (∑ c, h c : ℕ) ≤ D/w0)
    (hα : (∑ c, ∑ i, a c i : ℕ) ≤ D/wmin) :
    -(1-rebate)-arithmeticError scale v w0 wmin k-
      Real.log ((Fintype.card ι).factorial : ℝ)/D ≤
      Real.log ‖MvPolynomial.eval (fun i => ((β i : ℝ) : ℂ)) (formalMinor T j s h b a)‖/D := by
  obtain ⟨σ, hσ⟩ := exists_real_quadratic_conjugation F hF
  letI := complexification_isGalois F hF
  have hne' : MvPolynomial.eval (fun i => complexificationToComplex F
      (algebraMap F (Complexification F) (β i))) (formalMinor T j s h b a) ≠ 0 := by
    simpa only [complexification_real_eval] using hne
  have hM : ∀ i, Real.log (‖complexificationToComplex F
      ((primitiveMinpoly (β i : ℝ)).coeff 2 : Complexification F)‖*
      max 1 ‖complexificationToComplex F (algebraMap F (Complexification F) (β i))‖*
      max 1 ‖complexificationToComplex F (complexificationConjugation F σ
        (algebraMap F (Complexification F) (β i)))‖) ≤
      (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℝ)+Real.log (Real.sqrt 3) := by
    intro i
    rw [complexification_primitive_mahler F hF σ hσ (β i) (hβ i)]
    exact primitiveMinpoly_mahler_log_le (β i : ℝ) (hβ i)
  have hl := formal_minor_fixed_field_normalized_lower
    (complexification_relative_degree F hF) (complexificationConjugation F σ)
    (complexificationConjugation_ne_one F σ hσ) T k j s h b a hj
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 2)
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 1)
    (fun i => (primitiveMinpoly (β i : ℝ)).coeff 0)
    (fun i => algebraMap F (Complexification F) (β i))
    (fun i => primitiveMinpoly_three_gcd (β i : ℝ) (hβ i))
    (fun i => complexification_primitive_factorization F hF σ hσ (β i) (hβ i))
    (fun i => (primitiveMinpoly_coeff_two_pos (β i : ℝ) (hβ i)).ne')
    (complexificationToComplex F) (complexificationToComplex_compatible F) hne'
    (fun i => (Nat.ceil (Real.log (primitiveMinpolyHeight (β i : ℝ) : ℝ)) : ℝ))
    scale v w0 wmin D rebate hscale hv hw0 hwmin hD hw hT hjoint hrebate hs hh hα hM
  simpa only [complexification_real_eval] using hl

end FixedQuadratic
