import ZhangLS.Spec.Proposition141OffDiagonalCoefficientSum
import ZhangLS.Spec.Proposition141PrimitiveSmallSum

/-! # The primitive off-diagonal κ* sum with its literal nonunit filter

The actual primitive conductor is r>1; D∤r excludes induction of χ.
The common-modulus support bound permits precisely the unit-domain bridge
used by the proved nonprincipal Lemma5.6 chain.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

theorem proposition141_uniform_primitive_off_diagonal_sum_bound :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧
      ∀{D r h:ℕ} [NeZero r] (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r),
      D₀≤D → NormalizedAssumptionA χ → ((D*r:ℕ):ℝ)≤lemma23PaperP D →
      ¬D∣r → θ.IsPrimitive → 1<r → r<D^3 → 0<h →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀B:ℝ,0≤B →
      ∀κ:ℕ→ℂ,Proposition141KappaBound B κ → ∀D₁ d X:ℕ,
      0<D₁ → 0<d → 1≤X → ∀S:Finset ℕ,S⊆Icc 1 X →
      ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S‖ ≤
        C*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*lemma23PaperL D^7200*
          ((h:ℝ)*(r:ℝ))*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*
            (1+Real.log (X:ℝ))^5 := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_off_diagonal_finite_sum_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D r h _ χ θ hlarge hA hNP hDn hprim hr hrD hh β hβ B hB κ hκ D₁ d X hD₁ hd hX S hS
  have hθ : θ≠1 := by
    intro he
    have hc := congrArg DirichletCharacter.conductor he
    rw [show θ.conductor=r from hprim,DirichletCharacter.conductor_one] at hc
    omega
  have hcond : θ.conductor<D^3 := by rw [show θ.conductor=r from hprim]; exact hrD
  exact hbound χ θ hlarge hA hNP hDn hθ hcond β hβ B hB κ hκ D₁ d X hD₁ hd hX
    (h:ℝ) (r:ℝ) (by exact_mod_cast hh) (by exact_mod_cast (show 0<r by omega))
    (S.filter (fun l=>l.Coprime h)) ((filter_subset _ _).trans hS)

end ZhangLS.Spec
