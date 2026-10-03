import ZhangLS.Spec.Proposition141ResidualBound

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

-- The majorant is the literal original finite normalized residual.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ) :
    proposition141FiniteResidualMajorant χ β κ a =
      (Real.sqrt (D:ℝ))⁻¹ *
        ∑D₁∈D.divisors,∑d∈proposition141Indices D,∑k∈proposition141Indices D,
          if hN:0<(D/D₁)*k then
            letI : NeZero ((D/D₁)*k) := ⟨hN.ne'⟩
            if k.Coprime D₁ then
              (‖a (d*k)‖/((d:ℝ)*(k:ℝ)*(((D/D₁)*k).totient:ℝ)))*
                ‖proposition141ResidualCharacterSource (N:=(D/D₁)*k) χ β κ D₁ d‖
            else 0
          else 0 := rfl

-- Both main characters are actually excluded before taking the norm.
example {D N : ℕ} [NeZero N] (χ : RealPrimitiveCharacter D) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d : ℕ) :
    proposition141ResidualCharacterSource (N:=N) χ β κ D₁ d =
      ∑θ∈(univ:Finset (DirichletCharacter ℂ N)).filter
        (fun θ=>θ≠1 ∧ ∀hDN:D∣N,θ≠χ.chi.changeLevel hDN),
        gaussSum θ⁻¹ ZMod.stdAddChar*
          (∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*χ.chi (p:ZMod D)*
            proposition141LevelPrimeRow (D:=D) θ κ D₁ d p) := rfl

-- Literal short coefficient, reciprocal weight, induced exclusion, and full σ.
example {D D₁ D₂ d k : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ)
    (κ a : ℕ→ℂ) (hk : 0<k) :
    proposition141QuotientNatRow χ β κ a D₁ D₂ d k =
      ∑i:primitiveConductorFamilyIndex (D₂*k),
        if k.Coprime D₁ ∧ 1 < i.1.val ∧
          (∀hDN:D∣D₂*k,i.2.val.changeLevel (Nat.mem_divisors.mp i.1.property).1 ≠ χ.chi.changeLevel hDN) then
          ‖a (d*k)‖*(Real.sqrt (i.1.val:ℝ)/((d:ℝ)*(k:ℝ)*((D₂*k).totient:ℝ)))*
            ‖∑'l:ℕ,proposition141SigmaTerm χ i.2.val β κ D₁ d (D₂*k / i.1.val) l‖
        else 0 := by
  unfold proposition141QuotientNatRow
  rw [dif_pos hk]
  rfl

-- The primitive principal branch r=1 contributes exactly zero.
example {D D₁ D₂ d : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ)
    (κ a : ℕ→ℂ) (i : quotientConductorSource D₂) (hr : i.2.1.val=1) :
    quotientConductorSourceTerm χ β κ a D₁ D₂ d i=0 := by
  simp [quotientConductorSourceTerm,hr]

-- No strict cutoff or target convergence premise replaces original support.
example {D D₁ D₂ : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ)
    (κ : ℕ→ℂ) {Ba : ℝ} {a : ℕ→ℂ}
    (ha : Proposition141AdmissibleSequence D Ba a) :
    (∑'d:ℕ+,∑'k:ℕ+,∑i:primitiveConductorFamilyIndex (D₂*(k:ℕ)),
      quotientConductorSourceTerm χ β κ a D₁ D₂ (d:ℕ) ⟨k,i⟩)=
      ∑d∈proposition141Indices D,∑k∈proposition141Indices D,
        proposition141QuotientNatRow χ β κ a D₁ D₂ d k :=
  proposition141_quotient_dk_tsum_eq_finite χ β κ ha

-- Exact quotient weight retains every factor after the arithmetic transport.
example {D₂ d k r h : ℕ} (hD₂ : 0<D₂) (hr : 0<r) (he : r*h=D₂*k) :
    Real.sqrt (r:ℝ)/((d:ℝ)*(k:ℝ)*((D₂*k).totient:ℝ))=
      (D₂:ℝ)/((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ)) :=
  quotientConductor_weight hD₂ hr he

-- The final bridge assumes the original κ/a bounds, not a desired source estimate.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    (hmod : 2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    {Bκ Ba : ℝ} (hBκ : 0≤Bκ) {κ a : ℕ→ℂ}
    (hκ : Proposition141KappaBound Bκ κ) (ha : Proposition141AdmissibleSequence D Ba a) :
    proposition141FiniteResidualMajorant χ β κ a ≤ quotientSourceNormalizedSource χ β κ a :=
  proposition141_finite_residual_majorant_le_quotient χ β hD hL hmod hBκ hκ ha

end ZhangLS.Spec

#print axioms ZhangLS.Spec.proposition141FiniteResidualMajorant
#print axioms ZhangLS.Spec.proposition141QuotientNatRow
#print axioms ZhangLS.Spec.proposition141_quotient_nat_row_zero
#print axioms ZhangLS.Spec.proposition141_tsum_pnat_eq_finite
#print axioms ZhangLS.Spec.proposition141_quotient_k_tsum_eq_finite
#print axioms ZhangLS.Spec.proposition141_quotient_dk_tsum_eq_finite
#print axioms ZhangLS.Spec.proposition141_quotient_normalized_eq_finite
#print axioms ZhangLS.Spec.proposition141_weighted_residual_row_le_quotient
#print axioms ZhangLS.Spec.proposition141_finite_residual_majorant_le_quotient
