import ZhangLS.Spec.QuotientConductorSource
set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ZhangLS.Spec
open scoped Classical

-- Noncoprime r,h are genuinely allowed: r=4,h=6,D₂=6,k=4.
example : 0 < 4*6/6 ∧ 4 ∣ 6*(4*6/6) ∧ 6*(4*6/6)/4 = 6 :=
  quotientConductor_backward (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (d : ℕ) :
    Real.sqrt (4:ℝ)/((d:ℝ)*(4:ℝ)*(Nat.totient 24:ℝ)) =
      (6:ℝ)/((d:ℝ)*(6:ℝ)*(Nat.totient 24:ℝ)*Real.sqrt (4:ℝ)) := by
  simpa using quotientConductor_weight (D₂:=6) (d:=d) (k:=4) (r:=4) (h:=6)
    (by norm_num) (by norm_num) (by norm_num)

-- All weights use total real division, so d=0 and k=h=0 need no exclusions.
example {D₂ k r h : ℕ} (hD : 0<D₂) (hr : 0<r) (he : r*h=D₂*k) :
    Real.sqrt (r:ℝ)/(((0:ℕ):ℝ)*(k:ℝ)*((D₂*k).totient:ℝ)) =
      (D₂:ℝ)/(((0:ℕ):ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ)) :=
  quotientConductor_weight (d:=0) hD hr he

example {D₂ r : ℕ} (hD : 0<D₂) (hr : 0<r) :
    Real.sqrt (r:ℝ)/(((3:ℕ):ℝ)*((0:ℕ):ℝ)*((D₂*0).totient:ℝ)) =
      (D₂:ℝ)/(((3:ℕ):ℝ)*((0:ℕ):ℝ)*((0*r).totient:ℝ)*Real.sqrt (r:ℝ)) :=
  quotientConductor_weight (d:=3) (k:=0) (h:=0) hD hr (by simp)

-- r=1 weight is retained by arithmetic and excluded only by the original mask.
example (d : ℕ) :
    Real.sqrt (1:ℝ)/((d:ℝ)*(1:ℝ)*(Nat.totient 1:ℝ)) =
      (1:ℝ)/((d:ℝ)*(1:ℝ)*(Nat.totient 1:ℝ)*Real.sqrt (1:ℝ)) := by
  simpa using quotientConductor_weight (D₂:=1) (d:=d) (k:=1) (r:=1) (h:=1)
    (by norm_num) (by norm_num) rfl

example {D D₁ D₂ d : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ)
    (i : quotientConductorTarget D₂) (hr : (i.1:ℕ)=1) :
    quotientConductorTargetTerm χ β κ a D₁ D₂ d i=0 := by
  simp [quotientConductorTargetTerm,hr]

example {D D₁ D₂ : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ→ℂ)
    (i : quotientConductorSource D₂) :
    quotientConductorSourceTerm χ β κ a D₁ D₂ 0 i=0 := by
  simp [quotientConductorSourceTerm]

-- Equality at 2P₄ is included in both boxes.
example {D D₂ : ℕ} (i : quotientConductorSource D₂)
    (hboundary : ((i.1:ℕ):ℝ)=2*lemma61PaperP4 D) :
    i ∈ quotientConductorSourceBox D D₂ := by
  apply (quotientConductor_mem_sourceBox i).mpr
  rw [proposition141_mem_indices]
  exact ⟨i.1.property,hboundary.le⟩

example {D D₂ : ℕ} (hD : 0<D₂) (i : quotientConductorTarget D₂)
    (hboundary : (((i.1:ℕ)*(i.2.1.val:ℕ)/D₂:ℕ):ℝ)=2*lemma61PaperP4 D) :
    i ∈ quotientConductorTargetBox D D₂ hD := by
  apply (quotientConductor_mem_targetBox hD i).mpr
  rw [proposition141_mem_indices]
  exact ⟨(quotientConductor_backward hD i.1.property i.2.1.val.property i.2.1.property).1,
    hboundary.le⟩

-- The literal chi-induced exclusion survives dependent level transport.
example {D N M r : ℕ} (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r)
    (he : N=M) (hrN : r∣N) (hrM : r∣M) :
    (∀ hDN : D∣N, θ.changeLevel hrN ≠ χ.chi.changeLevel hDN) ↔
      (∀ hDM : D∣M, θ.changeLevel hrM ≠ χ.chi.changeLevel hDM) :=
  quotientConductor_induced_exclusion χ θ he hrN hrM

end ZhangLS.Spec
