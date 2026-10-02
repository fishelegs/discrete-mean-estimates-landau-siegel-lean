import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Complex.Basic

/-!
# Trusted specification: real primitive Dirichlet characters

We use mathlib's complex-valued `DirichletCharacter`, because mathlib's analytic
continuation and L-function API is built for complex characters.

A *real* character is recorded by the mathematically direct condition that every
value has zero imaginary part.  The quadratic identity is retained as a derived/useful
algebraic condition in the structure for now; a later bridge theorem should show the
redundancy under the standard Dirichlet-character hypotheses.
-/

namespace ZhangLS.Spec

open ComplexConjugate

/-- A positive-modulus primitive real Dirichlet character.

`real_valued` is deliberately explicit.  It prevents a later analytic theorem from
silently treating a complex-valued character as real merely because of its name.
-/
structure RealPrimitiveCharacter (D : ℕ) where
  chi : DirichletCharacter ℂ D
  primitive : chi.IsPrimitive
  real_valued : ∀ a : ZMod D, (chi a).im = 0
  quadratic : chi ^ 2 = 1
  modulus_pos : 0 < D

namespace RealPrimitiveCharacter

variable {D : ℕ}

/-- Evaluate the character on a natural number. -/
noncomputable def evalNat (χ : RealPrimitiveCharacter D) (n : ℕ) : ℂ :=
  χ.chi (n : ZMod D)

@[simp] theorem evalNat_one (χ : RealPrimitiveCharacter D) : χ.evalNat 1 = 1 := by
  simp [evalNat]

/-- Every value of a real character is fixed by complex conjugation. -/
theorem conj_eval (χ : RealPrimitiveCharacter D) (a : ZMod D) :
    conj (χ.chi a) = χ.chi a := by
  apply Complex.ext
  · simp
  · simpa [χ.real_valued a]

/-- Natural-number evaluations are real. -/
theorem evalNat_im (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (χ.evalNat n).im = 0 := by
  exact χ.real_valued (n : ZMod D)

/-- The modulus is nonzero. -/
theorem modulus_ne_zero (χ : RealPrimitiveCharacter D) : D ≠ 0 :=
  Nat.ne_of_gt χ.modulus_pos

/-- A real primitive character of modulus `D > 1` is nontrivial.

The proof uses primitivity: a trivial character has conductor `1`, whereas a
primitive character has conductor equal to its modulus.
-/
theorem nontrivial_of_one_lt_modulus (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) : χ.chi ≠ 1 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  intro hχ
  have hcond : χ.chi.conductor = D :=
    (DirichletCharacter.isPrimitive_def χ.chi).mp χ.primitive
  rw [hχ, DirichletCharacter.conductor_one] at hcond
  omega

end RealPrimitiveCharacter

end ZhangLS.Spec
