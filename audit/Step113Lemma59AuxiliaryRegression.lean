import ZhangLS.Spec.Lemma59UniformPolynomialInputs
import ZhangLS.Spec.Lemma59FiniteZeroProducts

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi1 χ ψ →
    ∀ {s : ℂ}, |s.re - 1 / 2| ≤ lemma44PaperAlpha D →
      |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10 →
      (lemma23PaperL D ^ 88)⁻¹ ≤
        ‖∑ n ∈ Finset.Icc 1 (D ^ 4), lemma23NuArithmeticFunction χ n * ψ (n : ZMod p) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ ∧
      ‖∑ n ∈ Finset.Icc 1 (D ^ 4), lemma23NuArithmeticFunction χ n * ψ (n : ZMod p) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ ≤ lemma23PaperL D ^ 88 ∧
      (∑ n ∈ Finset.Icc 1 (D ^ 4), lemma23NuArithmeticFunction χ n * ψ (n : ZMod p) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) ≠ 0 ∧
      ‖logDeriv (fun z : ℂ => ∑ n ∈ Finset.Icc 1 (D ^ 4),
          lemma23NuArithmeticFunction χ n * ψ (n : ZMod p) *
          Complex.exp (-z * (Real.log (n : ℝ) : ℂ))) s‖ ≤ 140800 * lemma23PaperL D := by
  obtain ⟨D₀, h⟩ := lemma59_uniform_extended_F_inputs
  refine ⟨D₀, ?_⟩
  intro D p _ χ ψ hD hψ s hre him
  simpa only [lemma23ActualSectionFourF, lemma23SectionFourF,
    lemma23FiniteDirichletPolynomial] using h χ ψ hD hψ ⟨hre, him⟩

example {D : ℕ} (hL : 100 ≤ lemma23PaperL D) :
    Lemma59InExtendedOmega2 D
      ⟨1 / 2 + lemma44PaperAlpha D, (lemma23PaperCenter D).im + lemma23PaperL D ^ 405 + 10⟩ ∧
    Lemma51InExtendedRegion D
      ⟨1 / 2 + lemma44PaperAlpha D, (lemma23PaperCenter D).im + lemma23PaperL D ^ 405 + 10⟩ := by
  apply lemma59_original_region_in_extended hL
  constructor
  · simp only [add_sub_cancel_left, abs_of_pos (lemma59_alpha_bounds hL).1]
    exact le_rfl
  · change |(lemma23PaperCenter D).im + lemma23PaperL D ^ 405 + 10 - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10
    have hp : 0 ≤ lemma23PaperL D ^ 405 + 10 := by positivity
    have he : (lemma23PaperCenter D).im + lemma23PaperL D ^ 405 + 10 -
        (lemma23PaperCenter D).im = lemma23PaperL D ^ 405 + 10 := by ring
    rw [he, abs_of_nonneg hp]

example {D : ℕ} (hL : 100 ≤ lemma23PaperL D) :
    Lemma59InExtendedOmega2 D
      ⟨1 / 2 - lemma44PaperAlpha D, (lemma23PaperCenter D).im - (lemma23PaperL D ^ 405 + 10)⟩ ∧
    Lemma51InExtendedRegion D
      ⟨1 / 2 - lemma44PaperAlpha D, (lemma23PaperCenter D).im - (lemma23PaperL D ^ 405 + 10)⟩ := by
  apply lemma59_original_region_in_extended hL
  constructor
  · simp only [sub_sub_cancel_left, abs_neg,
      abs_of_pos (lemma59_alpha_bounds hL).1]
    exact le_rfl
  · simp only [sub_sub_cancel_left, abs_neg]
    rw [abs_of_nonneg (by positivity : 0 ≤ lemma23PaperL D ^ 405 + 10)]

example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (hL : 100 ≤ lemma23PaperL D) {s : ℂ} {η : ℝ} (hη : 0 < η)
    (hs : ∀ ρ : ℂ, DirichletCharacter.LFunction ψ ρ = 0 →
      η * lemma44PaperAlpha D ≤ ‖s - ρ‖) : DirichletCharacter.LFunction ψ s ≠ 0 := by
  exact lemma59_zero_separated_LFunction_ne_zero ψ hL hη hs


example {D : ℕ} {c : ℝ} (hL : 100 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : 5 * c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2) :
    0 < lemma44PaperAlpha D * (1 - 5 * c * lemma44PaperAlpha D * lemma23PaperL D) ∧
      lemma44PaperAlpha D * (1 - 5 * c * lemma44PaperAlpha D * lemma23PaperL D) ≤ lemma44PaperAlpha D := by
  simpa only [lemma23PaperOffsetOne] using lemma59_paper_offset_one_bounds hL hc hsmall

example {D : ℕ} {c : ℝ} {s : ℂ} (hL : 100 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : 5 * c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    (hs : |s.re - 1 / 2| ≤ lemma44PaperAlpha D ∧
      |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10) :
    Lemma59InExtendedOmega2 D
      (s + I * ((lemma44PaperAlpha D * (1 - 5 * c * lemma44PaperAlpha D * lemma23PaperL D) : ℝ) : ℂ)) := by
  have hb := lemma59_paper_offset_one_bounds hL hc hsmall
  have hh := lemma59_original_shift_in_extended hL hs
    (u := lemma23PaperOffsetOne D c) (by rw [abs_of_pos hb.1]; exact hb.2)
  simpa only [lemma23PaperOffsetOne] using hh

example {N : ℕ} {z : ℂ} {ρ : ℕ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ k ∈ Finset.range N, ((k : ℝ) + 1) * δ ≤ ‖z - ρ k‖) :
    ‖(∏ k ∈ Finset.range N, (z + I * (δ : ℂ) - ρ k)) /
      (∏ k ∈ Finset.range N, (z - ρ k))‖ ≤ (N : ℝ) + 1 := by
  rw [← Finset.prod_div_distrib]
  exact lemma59_ranked_zero_product_bound hδ hgap

example (S : Finset ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (habove : ∀ ρ ∈ S, z.im + δ ≤ ρ.im) :
    ‖(∏ ρ ∈ S, (z + I * (δ : ℂ) - ρ)) / (∏ ρ ∈ S, (z - ρ))‖ ≤ 1 := by
  rw [← Finset.prod_div_distrib]
  exact lemma59_above_zero_product_le_one S hδ habove


#print axioms lemma59_alpha_bounds
#print axioms lemma59_original_region_in_extended
#print axioms lemma59_zero_separated_LFunction_ne_zero
#print axioms lemma59_paper_offset_one_bounds
#print axioms lemma59_original_shift_in_extended
#print axioms lemma59_extended_center_displacement_le_three
#print axioms lemma59_extended_center_displacement_le
#print axioms lemma59_extended_power_kernel_le
#print axioms lemma59_extended_FG_bound
#print axioms lemma59_extended_product_bound
#print axioms lemma59_extended_L227_error_lt_half
#print axioms lemma59_extended_F_two_sided
#print axioms lemma59_extended_F_ne_zero
#print axioms lemma59_extended_disk_subset_omega1
#print axioms lemma59_extended_F_logDeriv_bound
#print axioms lemma59_uniform_extended_F_inputs
#print axioms lemma59_linear_telescoping_product
#print axioms lemma59_shift_factor_bound
#print axioms lemma59_ranked_zero_product_bound
#print axioms lemma59_near_zero_factor_bound
#print axioms lemma59_above_zero_norm_decreases
#print axioms lemma59_above_zero_factor_le_one
#print axioms lemma59_above_zero_product_le_one
#print axioms lemma59_descending_gap_rank
#print axioms lemma59_descending_zeros_ranked_distance
#print axioms lemma59_descending_zero_product_bound
#print axioms lemma59_exceptional_zero_product_bound

end ZhangLS.Spec
