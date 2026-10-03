import ZhangLS.Spec.QuotientConductorArithmetic

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Literal positive k and primitive divisor family at level D₂*k. -/
def quotientConductorSource (D₂ : ℕ) : Type :=
  Σ k : ℕ+, primitiveConductorFamilyIndex (D₂*(k:ℕ))

/-- Positive r,h with D₂|r*h, carrying the same primitive character at r. -/
def quotientConductorTarget (D₂ : ℕ) : Type :=
  Σ r : ℕ+, Σ _h : {h : ℕ+ // D₂ ∣ (r:ℕ)*(h:ℕ)},
    {θ : DirichletCharacter ℂ (r:ℕ) // θ.IsPrimitive}

noncomputable def quotientConductorForward (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorSource D₂) : quotientConductorTarget D₂ :=
  let hi := quotientConductor_forward hD i.1.property (Nat.mem_divisors.mp i.2.1.property).1
  ⟨⟨i.2.1.val,hi.1⟩, ⟨⟨D₂*(i.1:ℕ)/i.2.1.val,hi.2.1⟩,hi.2.2.1⟩,i.2.2⟩

noncomputable def quotientConductorBackward (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorTarget D₂) : quotientConductorSource D₂ :=
  let hi := quotientConductor_backward hD i.1.property i.2.1.val.property i.2.1.property
  ⟨⟨(i.1:ℕ)*(i.2.1.val:ℕ)/D₂,hi.1⟩,
    ⟨⟨(i.1:ℕ),Nat.mem_divisors.mpr ⟨hi.2.1,(Nat.mul_pos hD hi.1).ne'⟩⟩,i.2.2⟩⟩

theorem quotientConductor_family_heq {N M r : ℕ} (he : N=M)
    (hN : r ∈ N.divisors) (hM : r ∈ M.divisors)
    (θ : {θ : DirichletCharacter ℂ r // θ.IsPrimitive}) :
    HEq (⟨⟨r,hN⟩,θ⟩ : primitiveConductorFamilyIndex N)
      (⟨⟨r,hM⟩,θ⟩ : primitiveConductorFamilyIndex M) := by
  subst M
  rfl

theorem quotientConductor_backward_forward (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorSource D₂) :
    quotientConductorBackward D₂ hD (quotientConductorForward D₂ hD i) = i := by
  rcases i with ⟨⟨k,hk⟩,⟨⟨r,hr⟩,θ⟩⟩
  have hk' := (quotientConductor_forward hD hk (Nat.mem_divisors.mp hr).1).2.2.2
  dsimp [quotientConductorBackward,quotientConductorForward]
  congr 1
  · exact PNat.eq hk'
  · apply quotientConductor_family_heq
    exact congrArg (D₂ * ·) hk'

theorem quotientConductor_forward_backward (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorTarget D₂) :
    quotientConductorForward D₂ hD (quotientConductorBackward D₂ hD i) = i := by
  rcases i with ⟨⟨r,hr⟩,⟨⟨⟨h,hh⟩,hdiv⟩,θ⟩⟩
  have hh' := (quotientConductor_backward hD hr hh hdiv).2.2
  dsimp [quotientConductorBackward,quotientConductorForward]
  congr 1
  · simp_all

noncomputable def quotientConductorEquiv (D₂ : ℕ) (hD : 0 < D₂) :
    quotientConductorSource D₂ ≃ quotientConductorTarget D₂ where
  toFun := quotientConductorForward D₂ hD
  invFun := quotientConductorBackward D₂ hD
  left_inv := quotientConductor_backward_forward D₂ hD
  right_inv := quotientConductor_forward_backward D₂ hD

/-- The original coefficient and every k-based predicate transport exactly. -/
theorem quotientConductor_backward_k (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorTarget D₂) :
    ((quotientConductorBackward D₂ hD i).1:ℕ) = (i.1:ℕ)*(i.2.1.val:ℕ)/D₂ := rfl

/-- Reindexing leaves the actual primitive character untouched. -/
theorem quotientConductor_backward_character (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorTarget D₂) :
    (quotientConductorBackward D₂ hD i).2.2.val = i.2.2.val := rfl

/-- The principal-conductor boundary is preserved, including D₂=k=r=h=1. -/
theorem quotientConductor_backward_principal (D₂ : ℕ) (hD : 0 < D₂)
    (i : quotientConductorTarget D₂) :
    (quotientConductorBackward D₂ hD i).2.1.val = 1 ↔ (i.1:ℕ) = 1 := Iff.rfl

end ZhangLS.Spec
