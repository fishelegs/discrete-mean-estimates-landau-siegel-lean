import FixedQuadratic.QuadraticNorm
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic

namespace FixedQuadratic

open scoped QuadraticAlgebra

/-- An explicit model of Q(i), with basis (1,i). -/
abbrev GaussianField := QuadraticAlgebra ℚ (-1) 0

instance gaussianFieldCondition : Fact (∀ r : ℚ, r^2 ≠ -1+0*r) := ⟨by
  intro r hr
  nlinarith [sq_nonneg r]⟩

noncomputable def gaussianToField : GaussianInt →+* GaussianField where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

noncomputable instance gaussianFieldAlgebra : Algebra GaussianInt GaussianField :=
  gaussianToField.toAlgebra

theorem gaussianToField_injective : Function.Injective gaussianToField := by
  intro x y h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  change (x.re : ℚ) = (y.re : ℚ) at hr
  change (x.im : ℚ) = (y.im : ℚ) at hi
  apply Zsqrtd.ext
  · exact_mod_cast hr
  · exact_mod_cast hi

instance gaussianFieldFaithful : FaithfulSMul GaussianInt GaussianField :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr gaussianToField_injective

theorem gaussianField_fraction_surj (z : GaussianField) :
    ∃ x y : GaussianInt, z = algebraMap GaussianInt GaussianField x /
      algebraMap GaussianInt GaussianField y := by
  let x : GaussianInt := ⟨z.re.num*(z.im.den : ℤ), z.im.num*(z.re.den : ℤ)⟩
  let y : GaussianInt := ⟨(z.re.den : ℤ)*z.im.den, 0⟩
  have hy : algebraMap GaussianInt GaussianField y ≠ 0 := by
    intro hh
    have hr := congrArg QuadraticAlgebra.re hh
    change (((z.re.den : ℤ)*(z.im.den : ℤ) : ℤ) : ℚ) = 0 at hr
    push_cast at hr
    have h1 : (z.re.den : ℚ) ≠ 0 := by exact_mod_cast z.re.den_ne_zero
    have h2 : (z.im.den : ℚ) ≠ 0 := by exact_mod_cast z.im.den_ne_zero
    exact (mul_ne_zero h1 h2) hr
  refine ⟨x, y, (eq_div_iff hy).mpr ?_⟩
  change z * gaussianToField y = gaussianToField x
  ext <;> simp [gaussianToField, x, y]
  · have hr : z.re*(z.re.den : ℚ) = z.re.num :=
      (eq_div_iff (by exact_mod_cast z.re.den_ne_zero)).mp z.re.num_div_den.symm
    nlinarith only [congrArg (fun v : ℚ => v*(z.im.den : ℚ)) hr]
  · have hi : z.im*(z.im.den : ℚ) = z.im.num :=
      (eq_div_iff (by exact_mod_cast z.im.den_ne_zero)).mp z.im.num_div_den.symm
    nlinarith only [congrArg (fun v : ℚ => v*(z.re.den : ℚ)) hi]

noncomputable instance gaussianFieldFractionRing : IsFractionRing GaussianInt GaussianField :=
  IsFractionRing.of_field GaussianInt GaussianField gaussianField_fraction_surj

theorem gaussianField_finrank : Module.finrank ℚ GaussianField = 2 :=
  QuadraticAlgebra.finrank_eq_two (-1 : ℚ) 0

noncomputable def gaussianFieldToComplex : GaussianField →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp [Algebra.smul_def]⟩

theorem gaussianFieldToComplex_compatible :
    gaussianFieldToComplex.toRingHom.comp (algebraMap GaussianInt GaussianField) =
      GaussianInt.toComplex := by
  apply RingHom.ext
  intro z
  change gaussianFieldToComplex (gaussianToField z) = GaussianInt.toComplex z
  simp [gaussianFieldToComplex, QuadraticAlgebra.lift, gaussianToField,
    GaussianInt.toComplex_def, Algebra.smul_def]

end FixedQuadratic
