import ZhangLS.Spec.Lemma45ZeroFree

/-! Paper-statement and trusted-axiom regression for Lemma 4.5. -/

namespace ZhangLS.Spec

open Complex

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ}
    (hσ : 1 / 2 + lemma44PaperAlpha D ^ 2 < s.re) (hσ1 : s.re < 1)
    (ht : |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2) :
    lemma45ActualA χ ψ s ≠ 0 :=
  lemma45_actual_A_ne_zero χ ψ hD hψ ⟨hσ, hσ1, ht⟩

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma45InRegion D s) :
    (lemma23PaperL D ^ 9)⁻¹ / 4 ≤ ‖lemma45ActualA χ ψ s‖ :=
  lemma45_actual_A_lower_bound χ ψ hD hψ hs

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma45InRegion D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s ≠ 0 :=
  lemma45_actual_product_ne_zero χ ψ hD hψ hs

#print axioms lemma45_short_sum_inv_eq_conj
#print axioms lemma45_omega1_F_inv_bound
#print axioms lemma45_equation410
#print axioms lemma45_divisor_series_mass_le
#print axioms lemma45_inverse_square_mass_le
#print axioms lemma45_error_constant_le
#print axioms lemma45_horizontal_F_quotient_bound
#print axioms lemma45_B_uniform_gap
#print axioms lemma45_actual_A_lower_bound
#print axioms lemma45_actual_A_ne_zero
#print axioms lemma45_actual_product_ne_zero

end ZhangLS.Spec
