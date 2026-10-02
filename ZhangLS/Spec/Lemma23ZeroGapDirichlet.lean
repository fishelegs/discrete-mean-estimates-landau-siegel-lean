import ZhangLS.Spec.Lemma23DirichletBranch
import ZhangLS.Spec.Lemma23ZeroGapArithmetic

/-!
# Lemma 2.3 with the zero-gap hypotheses of Proposition 2.2

This adapter feeds product zero-freeness between consecutive ordinates into
the actual Dirichlet `L`-function coefficient theorem.  It leaves only the
analytic task of obtaining those consecutive zeros and their gap bounds from
Proposition 2.2.
-/

namespace ZhangLS.Spec

/-- If the product of the target Dirichlet `L`-function and a partner factor
has no zeros in the first and third consecutive gaps, then the coefficient
in Lemma 2.3 is nonnegative at the paper's three offsets.  The arithmetic
ordering and transfer of product nonvanishing to the target factor are
formalized here; Proposition 2.2 must still supply the gap and zero-free data.
-/
theorem lemma23_actual_dirichlet_coefficient_nonneg_of_product_gaps
    {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : DirichletCharacter.IsPrimitive ψ) (hN : N ≠ 1)
    (ρ : ℂ) (hρre : ρ.re = 1 / 2) (hρim : 0 < ρ.im)
    {α δ g₁ g₂ g₃ : ℝ} (G : ℝ → ℂ)
    (hα : 0 < α) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 5)
    (hg₁lo : α * (1 - δ) < g₁) (hg₁hi : g₁ < α * (1 + δ))
    (hg₂lo : α * (1 - δ) < g₂) (hg₂hi : g₂ < α * (1 + δ))
    (hg₃lo : α * (1 - δ) < g₃)
    (hgap₁ : ∀ x, 0 < x → x < g₁ →
      DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) * G x ≠ 0)
    (hgap₃ : ∀ x, g₁ + g₂ < x → x < g₁ + g₂ + g₃ →
      DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) * G x ≠ 0)
    (hLzero : DirichletCharacter.LFunction ψ ρ = 0)
    (hLderivNe : deriv (DirichletCharacter.LFunction ψ) ρ ≠ 0) :
    ∃ Y : ℂ → ℂ,
      ((lemma23ComplexCoefficient
        (lemma23DirichletNormalizedM ψ Y
          (criticalLinePoint ρ (α * (1 - 5 * δ))))
        (lemma23DirichletNormalizedM ψ Y
          (criticalLinePoint ρ (2 * α * (1 + δ))))
        (lemma23DirichletNormalizedM ψ Y
          (criticalLinePoint ρ (3 * α * (1 - δ))))
        (Y ρ * deriv (DirichletCharacter.LFunction ψ) ρ)).im = 0) ∧
      0 ≤ (lemma23ComplexCoefficient
        (lemma23DirichletNormalizedM ψ Y
          (criticalLinePoint ρ (α * (1 - 5 * δ))))
        (lemma23DirichletNormalizedM ψ Y
          (criticalLinePoint ρ (2 * α * (1 + δ))))
        (lemma23DirichletNormalizedM ψ Y
          (criticalLinePoint ρ (3 * α * (1 - δ))))
        (Y ρ * deriv (DirichletCharacter.LFunction ψ) ρ)).re := by
  let F : ℝ → ℂ := fun x => DirichletCharacter.LFunction ψ (criticalLinePoint ρ x)
  let b₁ : ℝ := α * (1 - 5 * δ)
  let b₂ : ℝ := 2 * α * (1 + δ)
  let b₃ : ℝ := 3 * α * (1 - δ)
  have hinterleave := lemma23_paper_offset_gap_interleaving hα hδ hδlt
    hg₁lo hg₁hi hg₂lo hg₂hi hg₃lo
  have horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃ := by
    rcases hinterleave with ⟨hb₁pos, hb₁b₂, _, _, hb₂b₃, _⟩
    exact ⟨by simpa [b₁] using hb₁pos,
      by simpa [b₁, b₂] using hb₁b₂.le,
      by simpa [b₂, b₃] using hb₂b₃.le⟩
  have hnonzero := lemma23_offset_factor_nonzero_of_product_gap_exclusion
    F G hα hδ hδlt hg₁lo hg₁hi hg₂lo hg₂hi hg₃lo hgap₁ hgap₃
  have hLnozero₁ : ∀ ⦃x : ℝ⦄, 0 < x → x ≤ b₁ →
      DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) ≠ 0 := by
    intro x hx hxb₁
    have hFx := hnonzero.1 hx (by simpa [b₁] using hxb₁)
    simpa [F] using hFx
  have hLnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      DirichletCharacter.LFunction ψ (criticalLinePoint ρ x) ≠ 0 := by
    intro x hx
    have hFx := hnonzero.2 x (by simpa [b₂, b₃] using hx)
    simpa [F] using hFx
  have hresult := lemma23_actual_dirichlet_coefficient_nonneg ψ hψ hN ρ
    hρre hρim horder hLzero hLderivNe hLnozero₁ hLnozero₂
  simpa [b₁, b₂, b₃] using hresult

end ZhangLS.Spec
