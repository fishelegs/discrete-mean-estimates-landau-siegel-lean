import ZhangLS.Spec.Lemma81SixOneLengths

/-! # Fourth moments of the actual K, N and short error polynomials

The original Gaussian coefficients and strict T³ cutoff are retained.
Every coefficient bound and every length condition is proved.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_finite_character_polynomial_conjugate {p : ℕ} (X : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    conj (lemma81FiniteCharacterPolynomial X a ψ s) =
      lemma81FiniteCharacterPolynomial X (lemma81ConjugateSequence a) ψ⁻¹ (conj s) := by
  unfold lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hchar : conj (ψ (n : ZMod p)) = ψ⁻¹ (n : ZMod p) := MulChar.star_apply' ψ _
  simp only [map_mul,hchar,← Complex.exp_conj,map_neg,Complex.conj_ofReal,lemma81ConjugateSequence]

lemma lemma81_actual_inverse_polynomial_fourth_moment {D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hL : 3 ≤ lemma23PaperL D) (X : ℕ) (hX : X ≤ ⌊lemma23PaperP D⌋₊) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B) {s : ℂ}
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81FiniteCharacterPolynomial X a ψ.2⁻¹ s‖^4) ≤
      lemma81FourthMomentConstant * B^4 * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  have he : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81FiniteCharacterPolynomial X a ψ.2⁻¹ s‖^4) =
      ∑ ψ ∈ lemma33ActualFamily D, ‖lemma81FiniteCharacterPolynomial X (lemma81ConjugateSequence a) ψ.2 (conj s)‖^4 := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    have hh := lemma81_finite_character_polynomial_conjugate X (lemma81ConjugateSequence a) ψ.2 (conj s)
    rw [lemma81_conjugate_sequence_involutive,conj_conj] at hh
    rw [← hh,Complex.norm_conj]
  rw [he]
  exact lemma81_actual_polynomial_fourth_moment hB hL X hX _
    (fun n hn => by simpa only [lemma81ConjugateSequence,Complex.norm_conj] using ha n hn)
    (by simpa only [conj_re] using hs)

lemma lemma81_weighted_polynomial_eq_actual_prefix {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) :
    lemma61WeightedPolynomial D ψ x s =
      lemma81FiniteCharacterPolynomial ⌈2*x⌉₊ (fun n => (lemma61GaussianStar D (x/n) : ℂ)) ψ s := by
  unfold lemma61WeightedPolynomial lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma lemma81_weighted_polynomial_fourth_moment {D : ℕ} (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : ⌈2*x⌉₊ ≤ ⌊lemma23PaperP D⌋₊) {s : ℂ}
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61WeightedPolynomial D ψ.2 x s‖^4) ≤
      lemma81FourthMomentConstant * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  simp_rw [lemma81_weighted_polynomial_eq_actual_prefix]
  simpa only [one_pow,mul_one] using lemma81_actual_polynomial_fourth_moment
    (by norm_num : (0 : ℝ) ≤ 1) hL _ hx _
    (fun n hn => lemma61_gaussian_star_norm_le_one hD _) hs

lemma lemma81_inverse_weighted_polynomial_fourth_moment {D : ℕ} (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : ⌈2*x⌉₊ ≤ ⌊lemma23PaperP D⌋₊) {s : ℂ}
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61WeightedPolynomial D ψ.2⁻¹ x s‖^4) ≤
      lemma81FourthMomentConstant * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  simp_rw [lemma81_weighted_polynomial_eq_actual_prefix]
  simpa only [one_pow,mul_one] using lemma81_actual_inverse_polynomial_fourth_moment
    (by norm_num : (0 : ℝ) ≤ 1) hL _ hx _
    (fun n hn => lemma61_gaussian_star_norm_le_one hD _) hs

noncomputable def lemma81ShortCutoffCoefficient (D n : ℕ) : ℂ :=
  if (n : ℝ) < lemma56PaperT D^3 then 1 else 0

lemma lemma81_short_cutoff_coefficient_norm (D n : ℕ) : ‖lemma81ShortCutoffCoefficient D n‖ ≤ 1 := by
  unfold lemma81ShortCutoffCoefficient
  split_ifs <;> norm_num

lemma lemma81_short_polynomial_eq_actual_prefix {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma61ShortPolynomial D ψ s =
      lemma81FiniteCharacterPolynomial ⌈lemma56PaperT D^3⌉₊ (lemma81ShortCutoffCoefficient D) ψ s := by
  unfold lemma61ShortPolynomial lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
    lemma81ShortCutoffCoefficient
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

lemma lemma81_short_polynomial_fourth_moment {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) (hcut : ⌈lemma56PaperT D^3⌉₊ ≤ ⌊lemma23PaperP D⌋₊) {s : ℂ}
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ShortPolynomial D ψ.2 s‖^4) ≤
      lemma81FourthMomentConstant * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  simp_rw [lemma81_short_polynomial_eq_actual_prefix]
  simpa only [one_pow,mul_one] using lemma81_actual_polynomial_fourth_moment
    (by norm_num : (0 : ℝ) ≤ 1) hL _ hcut _
    (fun n hn => lemma81_short_cutoff_coefficient_norm D n) hs

/-- Genuine uniform fourth moments for every polynomial in the original 6.1. -/
theorem lemma81_uniform_six_one_polynomial_moments :
    ∃ N : ℕ, lemma61ModulusThreshold ≤ N ∧ ∀ D : ℕ, N ≤ D → ∀ s : ℂ,
      |s.re-1/2| ≤ lemma44PaperAlpha D →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ActualK D ψ.2 s‖^4) ≤
        lemma81FourthMomentConstant*lemma23PaperP D^2*lemma23PaperL D^36 ∧
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ActualN D ψ.2⁻¹ (1-s)‖^4) ≤
        lemma81FourthMomentConstant*lemma23PaperP D^2*lemma23PaperL D^36 ∧
      ∀ v : ℝ, (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ShortPolynomial D ψ.2 (s+I*(v : ℂ))‖^4) ≤
        lemma81FourthMomentConstant*lemma23PaperP D^2*lemma23PaperL D^36 := by
  obtain ⟨N,hN,hlen⟩ := lemma81_uniform_six_one_lengths
  refine ⟨N,hN,?_⟩
  intro D hD s hs
  have hp := lemma61_parameters_at_threshold (hN.trans hD)
  have hL : 3 ≤ lemma23PaperL D := by linarith only [hp.2]
  have hlength := hlen D hD
  refine ⟨lemma81_weighted_polynomial_fourth_moment hp.1 hL _ hlength.1 hs,?_,?_⟩
  · apply lemma81_inverse_weighted_polynomial_fourth_moment hp.1 hL _ hlength.2.1
    have he : (1-s).re-1/2 = -(s.re-1/2) := by simp; ring
    rw [he,abs_neg]
    exact hs
  · intro v
    exact lemma81_short_polynomial_fourth_moment hL hlength.2.2 (by simpa using hs)

end ZhangLS.Spec
