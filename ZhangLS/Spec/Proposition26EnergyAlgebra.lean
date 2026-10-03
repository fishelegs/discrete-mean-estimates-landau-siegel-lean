import ZhangLS.Spec.Proposition26OriginalObjects

/-! Exact quadratic homogeneity needed to apply the uniform mean theorem to
L^24 times the actual smoothing error, before rescaling. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Exact rescaling, valid without sign or asymptotic assumptions. -/
theorem proposition26_energy_homogeneity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ)
    (F : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (z : ℂ) :
    proposition26Energy χ c Y (fun ψ s => z*F ψ s) =
      ‖z‖^2*proposition26Energy χ c Y F := by
  unfold proposition26Energy
  simp only [norm_mul,mul_pow,Finset.mul_sum]
  apply sum_congr rfl
  intro ψ hψ
  apply sum_congr rfl
  intro ρ hρ
  ring

/-- Exact polynomial rescaling: the coefficient normalization used before
P7.1 induces the same normalization at the genuine zeros. -/
theorem proposition26_polynomial_scalar {p : ℕ} (D : ℕ) (a : ℕ→ℂ)
    (ψ : DirichletCharacter ℂ p) (s z : ℂ) :
    lemma81Polynomial D (fun n => z*a n) ψ s = z*lemma81Polynomial D a ψ s := by
  unfold lemma81Polynomial
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

/-- A three-piece norm decomposition loses only the explicit factor three. -/
lemma proposition26_three_square_bound (a b c : ℂ) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have ht : ‖a+b+c‖≤‖a‖+‖b‖+‖c‖ :=
    (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

end ZhangLS.Spec
