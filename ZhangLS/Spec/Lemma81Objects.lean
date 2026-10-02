import ZhangLS.Spec.Lemma81FiniteZerosReflection
import ZhangLS.Spec.Lemma81KernelReplacement

/-! # Faithful original Lemma 8.1 target

The actual Θ₁ is its §7 contour definition, without assuming Proposition 7.1.
The zero window is exactly (2.14), subject to the paper's undefined Z̃ notation
being read as Z. The outer conjugation and unconditional prime-mass error are
retained. This module defines the target and proves object/branch bridges;
it does not prove Lemma81Target.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
open scoped Classical

/-- The foundational predicate agrees definitionally with the earlier actual
Lemma 2.3 zero window. -/
theorem lemma81_zero_window_iff_original (D : ℕ) (ρ : ℂ) :
    Lemma81InZeroWindow D ρ ↔ Lemma23InZeroWindow D ρ := Iff.rfl

/-- The finite enumeration is exactly the original actual L-zero set. -/
theorem lemma81_mem_original_zero_finset {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) (ρ : ℂ) :
    ρ ∈ lemma81ZeroFinset D ψ ↔ Lemma23InZeroWindow D ρ ∧ ψ.LFunction ρ = 0 :=
  lemma81_mem_zero_finset ψ hψ ρ

noncomputable def lemma81ThetaOne {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑ ψ ∈ lemma81GoodFamily χ, lemma81NormalizedSegmentIntegral D 1
    (fun s => lemma81ActualC D c ψ.2 s * lemma81Polynomial D a₁ ψ.2 s *
      lemma81Polynomial D a₂ ψ.2⁻¹ (1 - s) * lemma81Omega D s)

noncomputable def lemma81DiscreteMean {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑ ψ ∈ lemma81GoodFamily χ, ∑ ρ ∈ lemma81ZeroFinset D ψ.2,
    lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ * lemma81Polynomial D a₁ ψ.2 ρ *
      lemma81Polynomial D a₂ ψ.2⁻¹ (1 - ρ) * lemma81Omega D ρ

/-- The branch condition in the target is satisfiable on the actual family. -/
theorem lemma81_actual_family_branches_exist {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ∃ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      ∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ) := by
  classical
  have he : ∀ ψ : lemma33CharacterIndex D, ∃ Y : ℂ → ℂ,
      ψ ∈ lemma81GoodFamily χ → Lemma23ActualBranch ψ.2 Y := by
    intro ψ
    by_cases hψ : ψ ∈ lemma81GoodFamily χ
    · have hg := (lemma81_mem_good_family χ ψ).mp hψ
      obtain ⟨Y,hY⟩ := lemma23_exists_continuous_actual_square_root ψ.2 hg.1.2.1 hg.1.1.ne_one
      exact ⟨Y,fun _ => hY⟩
    · exact ⟨fun _ => 0,fun hm => (hψ hm).elim⟩
  choose Y hY using he
  exact ⟨Y,hY⟩

/-- Original asymptotic target under the documented Z̃=Z notation reading.
Fixed coefficient bounds come before ε and its D-threshold; the error is
normalized by the actual prime mass. Every actual branch is allowed.
No Assumption (A), residue theorem, mean bound, or prime-mass estimate is an
extra hypothesis. The unconditional prime-mass normalization is still an
obligation for a future proof, as are the remaining contour/residue estimates. -/
def Lemma81Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c ∧
    ∀ B₁ B₂ : ℝ, 0 < B₁ → 0 < B₂ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
    ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ →
    Lemma81AdmissibleSequence D B₂ a₂ →
    ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
    (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
    ‖lemma81DiscreteMean χ c Y a₁ a₂ - lemma81ThetaOne χ c a₁ a₂ -
      conj (lemma81ThetaOne χ c (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁))‖ ≤
      ε * lemma33ActualPrimeMass D

end ZhangLS.Spec
