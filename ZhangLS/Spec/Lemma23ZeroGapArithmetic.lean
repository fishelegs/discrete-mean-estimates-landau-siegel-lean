import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic interleaving of the offsets in Lemma 2.3

The three shifts in the paper lie in three successive gaps between zeros of
`L(s, ψ)L(s, χψ)`.  This file isolates the real-variable calculation: if each
of three consecutive gaps is within a relative error `δ` of `α`, then the
paper's `β₁, β₂, β₃` lie before the first gap, after the second gap, and before
the third gap, respectively.  The analytic theorem supplying the consecutive
zeros and their gap bounds remains separate.
-/

namespace ZhangLS.Spec

/-- The locations of the three offsets interleave with three consecutive
gaps whose lengths are each `α(1 ± δ)`. -/
theorem lemma23_paper_offset_gap_interleaving
    {α δ g₁ g₂ g₃ : ℝ}
    (hα : 0 < α) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 5)
    (hg₁lo : α * (1 - δ) < g₁) (hg₁hi : g₁ < α * (1 + δ))
    (hg₂lo : α * (1 - δ) < g₂) (hg₂hi : g₂ < α * (1 + δ))
    (hg₃lo : α * (1 - δ) < g₃) :
    0 < α * (1 - 5 * δ) ∧
      α * (1 - 5 * δ) < 2 * α * (1 + δ) ∧
      α * (1 - 5 * δ) < g₁ ∧
      g₁ + g₂ < 2 * α * (1 + δ) ∧
      2 * α * (1 + δ) < 3 * α * (1 - δ) ∧
      3 * α * (1 - δ) < g₁ + g₂ + g₃ := by
  have hcoef₁ : 0 < 1 - 5 * δ := by linarith
  have hcoef₂ : 2 * (1 + δ) < 3 * (1 - δ) := by linarith
  have hg₂pos : 0 < g₂ := lt_trans (mul_pos hα (by linarith [hδlt])) hg₂lo
  have hb₁g₁ : α * (1 - 5 * δ) < g₁ := by
    calc
      α * (1 - 5 * δ) ≤ α * (1 - δ) := by
        apply mul_le_mul_of_nonneg_left _ hα.le
        linarith [hδ]
      _ < g₁ := hg₁lo
  refine ⟨mul_pos hα hcoef₁, ?_, hb₁g₁, ?_, ?_, ?_⟩
  · calc
      α * (1 - 5 * δ) < g₁ := hb₁g₁
      _ < g₁ + g₂ := by linarith
      _ < 2 * α * (1 + δ) := by
        calc
          g₁ + g₂ < α * (1 + δ) + α * (1 + δ) := add_lt_add hg₁hi hg₂hi
          _ = 2 * α * (1 + δ) := by ring
  · calc
      g₁ + g₂ < α * (1 + δ) + α * (1 + δ) := add_lt_add hg₁hi hg₂hi
      _ = 2 * α * (1 + δ) := by ring
  · calc
      2 * α * (1 + δ) = α * (2 * (1 + δ)) := by ring
      _ < α * (3 * (1 - δ)) := mul_lt_mul_of_pos_left hcoef₂ hα
      _ = 3 * α * (1 - δ) := by ring
  · calc
      3 * α * (1 - δ) = α * (1 - δ) + α * (1 - δ) + α * (1 - δ) := by ring
      _ < g₁ + g₂ + g₃ := by linarith [hg₁lo, hg₂lo, hg₃lo]

/-- If the product whose zeros are controlled by Proposition 2.2 is nonzero
between its first and third consecutive zeros, then the first factor is
nonzero on the two offset intervals used by Lemma 2.3. -/
theorem lemma23_offset_factor_nonzero_of_product_gap_exclusion
    {α δ g₁ g₂ g₃ : ℝ} (F G : ℝ → ℂ)
    (hα : 0 < α) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 5)
    (hg₁lo : α * (1 - δ) < g₁) (hg₁hi : g₁ < α * (1 + δ))
    (hg₂lo : α * (1 - δ) < g₂) (hg₂hi : g₂ < α * (1 + δ))
    (hg₃lo : α * (1 - δ) < g₃)
    (hgap₁ : ∀ x, 0 < x → x < g₁ → F x * G x ≠ 0)
    (hgap₃ : ∀ x, g₁ + g₂ < x → x < g₁ + g₂ + g₃ → F x * G x ≠ 0) :
    (∀ ⦃x : ℝ⦄, 0 < x → x ≤ α * (1 - 5 * δ) → F x ≠ 0) ∧
      (∀ x ∈ Set.Icc (2 * α * (1 + δ)) (3 * α * (1 - δ)), F x ≠ 0) := by
  obtain ⟨_, _, hb₁g₁, hg₁₂b₂, hb₂b₃, hb₃g₁₂₃⟩ :=
    lemma23_paper_offset_gap_interleaving hα hδ hδlt
      hg₁lo hg₁hi hg₂lo hg₂hi hg₃lo
  constructor
  · intro x hx hxle hFxzero
    have hFxGx := hgap₁ x hx (lt_of_le_of_lt hxle hb₁g₁)
    exact hFxGx (by simp [hFxzero])
  · intro x hx hFxzero
    have hxlower : g₁ + g₂ < x := lt_of_lt_of_le hg₁₂b₂ hx.1
    have hxupper : x < g₁ + g₂ + g₃ := lt_of_le_of_lt hx.2 hb₃g₁₂₃
    have hFxGx := hgap₃ x hxlower hxupper
    exact hFxGx (by simp [hFxzero])

end ZhangLS.Spec
