import ZhangLS.Spec.Lemma23DirichletFunctionalEquation

/-!
# A Gauss-sum identity for the root number in Lemma 2.3

The discrete Fourier transform formula for primitive Dirichlet characters
gives the product of the Gauss sums of a character and its inverse, without
assuming the modulus is prime.
-/

namespace ZhangLS.Spec

open ComplexConjugate
open scoped ZMod

theorem lemma23_gaussSum_mul_inverse
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar =
      (N : ℂ) * χ (-1) := by
  have hχInv : DirichletCharacter.IsPrimitive χ⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact (DirichletCharacter.isPrimitive_def χ).mp hχ
  have hχNe : χ ≠ 1 := by
    intro h
    have hprimitive := (DirichletCharacter.isPrimitive_def χ).mp hχ
    rw [h, DirichletCharacter.conductor_one] at hprimitive
    exact hN hprimitive.symm
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  let τInv : ℂ := gaussSum χ⁻¹ ZMod.stdAddChar
  have hFourier : ZMod.dft χ = fun k : ZMod N ↦ χ⁻¹ (-k) * τ := by
    funext k
    simpa [τ] using hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hFourierInv : ZMod.dft
      ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) =
      fun k : ZMod N ↦ χ (-k) * τInv := by
    funext k
    simpa [τInv] using hχInv.fourierTransform_eq_inv_mul_gaussSum k
  have hleft : ZMod.dft (ZMod.dft χ) (1 : ZMod N) = τ * τInv := by
    rw [hFourier, ZMod.dft_mul_const, ZMod.dft_comp_neg]
    rw [hFourierInv]
    simp [τ, τInv] <;> ring
  have hright : ZMod.dft (ZMod.dft χ) (1 : ZMod N) =
      (N : ℂ) * χ (-1) := by
    have h := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (1 : ZMod N)
    simpa using h
  calc
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = τ * τInv := by
      rfl
    _ = ZMod.dft (ZMod.dft χ) (1 : ZMod N) := hleft.symm
    _ = (N : ℂ) * χ (-1) := hright

/-- The global root number defined by mathlib has unit modulus for every
primitive Dirichlet character of nontrivial level.  The proof derives the
Gauss-sum magnitude from the primitive Fourier-transform identity on `ZMod N`.
-/
theorem lemma23_rootNumber_norm_eq_one
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1) :
    ‖DirichletCharacter.rootNumber χ‖ = 1 := by
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
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hden : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt (N : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    norm_num [Real.sqrt_eq_rpow]
  have hdenSq : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ ^ 2 = (N : ℝ) := by
    rw [hden, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hτnorm : ‖τ‖ = ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ := by
    nlinarith [hτsq, hdenSq, norm_nonneg τ,
      norm_nonneg ((N : ℂ) ^ (1 / 2 : ℂ))]
  have hsqrtNe : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.mpr hNpos)).ne'
  rw [DirichletCharacter.rootNumber]
  simp only [norm_div, norm_pow]
  rw [Complex.norm_I]
  simp only [one_pow, div_one]
  rw [hτnorm, hden]
  exact div_self hsqrtNe

end ZhangLS.Spec
