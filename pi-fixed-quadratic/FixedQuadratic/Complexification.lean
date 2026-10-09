import FixedQuadratic.GaussianField
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

namespace FixedQuadratic
open scoped QuadraticAlgebra

/-- The concrete F(i) model used for one fixed real field F. -/
abbrev Complexification (F : IntermediateField ℚ ℝ) := QuadraticAlgebra F (-1) 0

instance complexificationCondition (F : IntermediateField ℚ ℝ) :
    Fact (∀ r : F, r^2 ≠ -1+0*r) := ⟨by
  intro r hr
  have hh := congrArg (fun v : F => (v : ℝ)) hr
  norm_num at hh
  nlinarith [sq_nonneg (r : ℝ)]⟩

noncomputable def gaussianFieldToComplexification (F : IntermediateField ℚ ℝ) :
    GaussianField →ₐ[ℚ] Complexification F :=
  QuadraticAlgebra.lift ⟨QuadraticAlgebra.omega, by
    simp [QuadraticAlgebra.omega_mul_omega_eq_add, Algebra.smul_def]⟩

noncomputable instance complexificationGaussianAlgebra (F : IntermediateField ℚ ℝ) :
    Algebra GaussianField (Complexification F) := (gaussianFieldToComplexification F).toRingHom.toAlgebra

noncomputable instance complexificationGaussianIntAlgebra (F : IntermediateField ℚ ℝ) :
    Algebra GaussianInt (Complexification F) :=
      ((gaussianFieldToComplexification F).toRingHom.comp gaussianToField).toAlgebra

instance complexificationGaussianTower (F : IntermediateField ℚ ℝ) :
    IsScalarTower GaussianInt GaussianField (Complexification F) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance complexificationRatGaussianTower (F : IntermediateField ℚ ℝ) :
    IsScalarTower ℚ GaussianField (Complexification F) :=
  IsScalarTower.of_algebraMap_eq (fun q => ((gaussianFieldToComplexification F).commutes q).symm)

instance complexificationRatRealTower (F : IntermediateField ℚ ℝ) :
    IsScalarTower ℚ F (Complexification F) where
  smul_assoc q x z := by ext <;> simp [smul_assoc]

noncomputable instance complexificationFinite (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] : FiniteDimensional ℚ (Complexification F) :=
  Module.Finite.trans F (Complexification F)

noncomputable instance complexificationGaussianFinite (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] : FiniteDimensional GaussianField (Complexification F) :=
  Module.Finite.of_restrictScalars_finite ℚ GaussianField (Complexification F)

noncomputable instance complexificationNumberField (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] : NumberField (Complexification F) where

/-- The relative degree is proved from the actual two successive quadratic
bases and the compatible Gaussian tower; it is not an extra tower hypothesis. -/
theorem complexification_relative_degree (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) :
    Module.finrank GaussianField (Complexification F) = 2 := by
  have htotal := Module.finrank_mul_finrank ℚ F (Complexification F)
  rw [hF, QuadraticAlgebra.finrank_eq_two] at htotal
  have hgaussian := Module.finrank_mul_finrank ℚ GaussianField (Complexification F)
  rw [gaussianField_finrank] at hgaussian
  omega

theorem complexification_isGalois (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) :
    IsGalois GaussianField (Complexification F) := by
  letI : Algebra.IsQuadraticExtension GaussianField (Complexification F) :=
    ⟨complexification_relative_degree F hF⟩
  infer_instance

theorem real_quadratic_isGalois (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) : IsGalois ℚ F := by
  letI : Algebra.IsQuadraticExtension ℚ F := ⟨hF⟩
  infer_instance

theorem exists_real_quadratic_conjugation (F : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ F] (hF : Module.finrank ℚ F = 2) :
    ∃ σ : F ≃ₐ[ℚ] F, σ ≠ 1 := by
  letI := real_quadratic_isGalois F hF
  have hc := IsGalois.card_aut_eq_finrank ℚ F
  rw [hF] at hc
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : F ≃ₐ[ℚ] F)).mp hc
  exact ⟨σ, hσ⟩

/-- Apply the same real-field conjugation to both coefficients, fixing i. -/
noncomputable def complexificationConjugation (F : IntermediateField ℚ ℝ)
    (σ : F ≃ₐ[ℚ] F) : Complexification F ≃ₐ[GaussianField] Complexification F where
  toFun z := ⟨σ z.re, σ z.im⟩
  invFun z := ⟨σ.symm z.re, σ.symm z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_add' z w := by ext <;> simp
  commutes' g := by
    change (⟨σ ((gaussianFieldToComplexification F g).re),
      σ ((gaussianFieldToComplexification F g).im)⟩ : Complexification F) =
        gaussianFieldToComplexification F g
    have hre : (gaussianFieldToComplexification F g).re = algebraMap ℚ F g.re := by
      simp [gaussianFieldToComplexification, QuadraticAlgebra.lift, Algebra.smul_def]
    have him : (gaussianFieldToComplexification F g).im = algebraMap ℚ F g.im := by
      simp [gaussianFieldToComplexification, QuadraticAlgebra.lift, Algebra.smul_def]
    ext <;> simp [hre, him]

theorem complexificationConjugation_ne_one (F : IntermediateField ℚ ℝ)
    (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) : complexificationConjugation F σ ≠ 1 := by
  intro he
  apply hσ
  apply AlgEquiv.ext
  intro x
  have hh := AlgEquiv.congr_fun he (algebraMap F (Complexification F) x)
  have hr := congrArg QuadraticAlgebra.re hh
  exact hr


noncomputable def complexificationToComplex (F : IntermediateField ℚ ℝ) :
    Complexification F →+* ℂ where
  toFun z := ((z.re : ℝ) : ℂ)+((z.im : ℝ) : ℂ)*Complex.I
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    simp only [neg_mul, zero_mul, add_zero, mul_add, add_mul]
    ring_nf
    simp
    ring

theorem complexificationToComplex_apply (F : IntermediateField ℚ ℝ) (z : Complexification F) :
    complexificationToComplex F z = ((z.re : ℝ) : ℂ)+((z.im : ℝ) : ℂ)*Complex.I := rfl

theorem gaussianFieldToComplexification_re (F : IntermediateField ℚ ℝ) (g : GaussianField) :
    (gaussianFieldToComplexification F g).re = algebraMap ℚ F g.re := by
  simp [gaussianFieldToComplexification, QuadraticAlgebra.lift, Algebra.smul_def]

theorem gaussianFieldToComplexification_im (F : IntermediateField ℚ ℝ) (g : GaussianField) :
    (gaussianFieldToComplexification F g).im = algebraMap ℚ F g.im := by
  simp [gaussianFieldToComplexification, QuadraticAlgebra.lift, Algebra.smul_def]

theorem complexificationToComplex_compatible (F : IntermediateField ℚ ℝ) :
    (complexificationToComplex F).comp (algebraMap GaussianInt (Complexification F)) =
      GaussianInt.toComplex := by
  apply RingHom.ext
  intro z
  rw [RingHom.comp_apply]
  change complexificationToComplex F ((gaussianFieldToComplexification F) (gaussianToField z)) = _
  rw [complexificationToComplex_apply, gaussianFieldToComplexification_re,
    gaussianFieldToComplexification_im]
  change (((algebraMap ℚ F) (z.re : ℚ) : ℝ) : ℂ)+
    (((algebraMap ℚ F) (z.im : ℚ) : ℝ) : ℂ)*Complex.I = GaussianInt.toComplex z
  have hr : (algebraMap ℚ F (z.re : ℚ) : ℝ) = (z.re : ℝ) := by
    rw [IntermediateField.coe_algebraMap_apply]
    norm_cast
  have hi : (algebraMap ℚ F (z.im : ℚ) : ℝ) = (z.im : ℝ) := by
    rw [IntermediateField.coe_algebraMap_apply]
    norm_cast
  rw [hr, hi]
  exact (GaussianInt.toComplex_def z).symm

end FixedQuadratic
