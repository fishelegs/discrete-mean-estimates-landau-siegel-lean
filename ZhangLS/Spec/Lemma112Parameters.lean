import ZhangLS.Spec.Lemma111
import ZhangLS.Spec.Lemma61

/-!
# Original Lemma 11.2: genuine objects and product-conductor inputs

The statement on printed p65 writes `O(E₂)` but labels the immediately
following definition `E`. This file consistently calls that displayed
quantity `lemma112ActualE2`. No extra exponential floor is inserted.

The character family is the ambient Ψ, not Ψ₁; there is no assumption (A).
The actual twist has modulus/conductor D*p, and the second cutoff is D*t₀
rather than t₀. The smoothed J functions are the original infinite sums.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology ComplexConjugate

noncomputable def lemma112PaperP1 (D : ℕ) : ℝ :=
  lemma23PaperP D ^ (63 / 125 : ℝ)

noncomputable def lemma112Coefficient {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (n : ℕ) : ℂ :=
  χ.evalNat n * ψ (n : ZMod p)

noncomputable def lemma112JtildeOne {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
    (lemma111SmoothedOne D n : ℂ)

noncomputable def lemma112JtildeTwo {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
    (lemma111SmoothedTwo D n : ℂ)

/-- The strict `n<P₁` cutoff from the display defining E₂. -/
noncomputable def lemma112ShortPolynomial {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
      (fun n : ℕ => (n : ℝ) < lemma112PaperP1 D),
    lemma112Coefficient χ ψ n * exp (-s * (Real.log (n : ℝ) : ℂ))

noncomputable def lemma112ActualE2 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℝ :=
  lemma23PaperL D ^ (-68 : ℤ) *
    (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
      ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)))

def Lemma112InRegion (D : ℕ) (s : ℂ) : Prop :=
  s.re = 1 / 2 ∧ |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405

def Lemma112Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
    ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi (D := D) ψ →
      ∀ {s : ℂ}, Lemma112InRegion D s →
        letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
        ‖lemma112JtildeOne χ ψ s - lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
          lemma112JtildeTwo χ ψ⁻¹ (1 - s)‖ ≤ C * lemma112ActualE2 χ ψ s

lemma lemma112_coefficient_eq_twist {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) :
    lemma112Coefficient χ ψ = fun n : ℕ => lemma44CharacterTwist χ ψ (n : ZMod (D * p)) := by
  funext n
  exact (lemma44CharacterTwist_eval_nat χ ψ n).symm

lemma lemma112_coefficient_norm_le_one {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (n : ℕ) :
    ‖lemma112Coefficient χ ψ n‖ ≤ 1 := by
  unfold lemma112Coefficient RealPrimitiveCharacter.evalNat
  rw [norm_mul]
  exact mul_le_one₀ (χ.chi.norm_le_one _) (norm_nonneg _) (ψ.norm_le_one _)

lemma lemma112_coefficient_one {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) :
    lemma112Coefficient χ ψ 1 = 1 := by simp [lemma112Coefficient]

lemma lemma112_short_polynomial_differentiable {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) :
    Differentiable ℂ (lemma112ShortPolynomial χ ψ) := by
  unfold lemma112ShortPolynomial
  fun_prop

lemma lemma112_error_integrand_continuous {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    Continuous (fun v : ℝ => ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
      Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
  have h := (lemma112_short_polynomial_differentiable χ ψ).continuous
  fun_prop

lemma lemma112_error_integrand_interval_integrable {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
      Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) volume a b :=
  (lemma112_error_integrand_continuous χ ψ s).intervalIntegrable a b

lemma lemma112_E2_nonneg {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    0 ≤ lemma112ActualE2 χ ψ s := by
  unfold lemma112ActualE2
  apply mul_nonneg (zpow_nonneg (Real.log_natCast_nonneg D) _)
  have hp : 0 ≤ lemma23PaperL D ^ 20 := pow_nonneg (Real.log_natCast_nonneg D) 20
  exact intervalIntegral.integral_nonneg
    (by linarith only [hp]) (fun _ _ => by positivity)

lemma lemma112_short_polynomial_conjugation {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma112ShortPolynomial χ ψ⁻¹ (conj s) = conj (lemma112ShortPolynomial χ ψ s) := by
  unfold lemma112ShortPolynomial lemma112Coefficient RealPrimitiveCharacter.evalNat
  simp only [map_sum, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n hn
  rw [χ.conj_eval, ← MulChar.star_apply' ψ (n : ZMod p)]
  rfl

lemma lemma112_short_polynomial_critical_reflection {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s.re = 1 / 2) (v : ℝ) :
    ‖lemma112ShortPolynomial χ ψ⁻¹ (1 - s - I * (v : ℂ))‖ =
      ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ := by
  have he : 1 - s - I * (v : ℂ) = conj (s + I * (v : ℂ)) := by
    apply Complex.ext <;> simp [hs] <;> ring
  rw [he, lemma112_short_polynomial_conjugation, Complex.norm_conj]

lemma lemma112_region_subset_lemma51 {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) :
    Lemma51InRegion D s := by
  refine ⟨?_, by linarith [hs.2]⟩
  rw [hs.1, sub_self, abs_zero]
  exact (lemma44_alpha_pos_le_one hL).1.le

lemma lemma112_region_subset_lemma61 {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) :
    Lemma61InRegion D s := by
  refine ⟨?_, by linarith [hs.2]⟩
  rw [hs.1, sub_self, abs_zero]
  exact mul_pos (by norm_num) (lemma44_alpha_pos_le_one hL).1

/-- All hypotheses needed by the conductor-Dp functional equation come from Ψ. -/
lemma lemma112_twist_family_data {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    (lemma44CharacterTwist χ ψ).IsPrimitive ∧
      (lemma44CharacterTwist χ ψ).conductor = D * p ∧
      D * p ≠ 1 ∧ lemma44CharacterTwist χ ψ ≠ 1 := by
  have ht := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  refine ⟨ht, ht, ?_, (lemma44_family_characters_nontrivial χ ψ hL hψ).2⟩
  intro h
  exact hψ.1.ne_one (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))

lemma lemma112_actual_twist_functional_equation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (him : 0 < s.im) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s =
      lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ⁻¹) (1 - s) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hd := lemma112_twist_family_data χ ψ hL hψ
  have h := lemma23_dirichletLFunction_functional_equation
    (lemma44CharacterTwist χ ψ) hd.1 hd.2.2.1
    (lemma23_gammaFactor_ne_zero_of_im_ne_zero _ him.ne')
    (lemma23_gammaFactor_ne_zero_of_im_ne_zero _ (by simpa using neg_ne_zero.mpr him.ne'))
  simpa only [lemma44CharacterTwist_inv] using h

end ZhangLS.Spec
