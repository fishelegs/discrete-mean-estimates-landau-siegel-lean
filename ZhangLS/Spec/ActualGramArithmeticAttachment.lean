import ZhangLS.Spec.ActualGramPiCollapse
import ZhangLS.Spec.Proposition71Objects
import ZhangLS.Spec.Lemma84WeightedMass

/-! Literal finite arithmetic attachments for arbitrary fixed profile values.
The coefficients retain the real primitive character, the true xi, the true
lambda and the original strict polynomial index set. No limiting Gram is
assumed or identified with a finite arithmetic or zero sum. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex ComplexConjugate
open scoped Classical

lemma actualGram_character_mul {D : ℕ} (χ : RealPrimitiveCharacter D) (m n : ℕ) :
    χ.evalNat (m*n) = χ.evalNat m * χ.evalNat n := by
  simp [RealPrimitiveCharacter.evalNat, Nat.cast_mul, map_mul]

lemma actualGram_character_square {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    χ.evalNat n ^ 2 = (‖χ.evalNat n‖ : ℂ) := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (n : ZMod D) with h | h | h
  · have he : χ.evalNat n = 0 := h
    simp [he]
  · have he : χ.evalNat n = 1 := h
    simp [he]
  · have he : χ.evalNat n = -1 := h
    simp [he]

noncomputable def actualGramProfileSequence {D : ℕ} (χ : RealPrimitiveCharacter D)
    (f : ℕ → ℂ) (n : ℕ) : ℂ := χ.evalNat n * f n

lemma actualGram_profile_conjugate {D : ℕ} (χ : RealPrimitiveCharacter D)
    (f : ℕ → ℂ) :
    lemma81ConjugateSequence (actualGramProfileSequence χ f) =
      actualGramProfileSequence χ (fun n => conj (f n)) := by
  funext n
  simp [lemma81ConjugateSequence, actualGramProfileSequence, map_mul,
    RealPrimitiveCharacter.evalNat, χ.conj_eval]

noncomputable def actualGramFirst {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (f : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ m ∈ lemma81PolynomialIndices D,
    χ.evalNat m / (m : ℂ) ^ (1 - lemma83PaperBeta D c j) * f (q*m)

noncomputable def actualGramSecond {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (g : ℕ → ℂ) (d r : ℕ) : ℂ :=
  ∑ n ∈ lemma81PolynomialIndices D,
    χ.evalNat n * lemma83Xi (lemma83PaperBeta D c) j n d r / (n : ℂ) * g (d*r*n)

/-- The actual P7 sum in its exact chi/Pi-compatible Section 8 form.
For the Hermitian Gram choose g=conj(f₂); the conjugation is not dropped. -/
theorem actualGram_P7_profile_factorization {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (f g : ℕ → ℂ) :
    proposition71ArithmeticSum D c j
      (actualGramProfileSequence χ f) (actualGramProfileSequence χ g) =
    ∑ d ∈ lemma81PolynomialIndices D, ∑ r ∈ lemma81PolynomialIndices D,
      lemma84Section8Weight χ c j d r * actualGramFirst χ c j f (d*r) *
        actualGramSecond χ c j g d r := by
  unfold proposition71ArithmeticSum
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro r hr
  have hfirst : (∑ m ∈ lemma81PolynomialIndices D,
      actualGramProfileSequence χ f (d*r*m) / (m : ℂ) ^ (1 - lemma83PaperBeta D c j)) =
      χ.evalNat (d*r) * actualGramFirst χ c j f (d*r) := by
    rw [actualGramFirst, mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [actualGramProfileSequence, actualGram_character_mul]
    ring
  have hsecond : (∑ n ∈ lemma81PolynomialIndices D,
      actualGramProfileSequence χ g (d*r*n) *
        lemma83Xi (lemma83PaperBeta D c) j n d r / (n : ℂ)) =
      χ.evalNat (d*r) * actualGramSecond χ c j g d r := by
    rw [actualGramSecond, mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [actualGramProfileSequence, actualGram_character_mul]
    ring
  rw [hfirst, hsecond]
  calc
    _ = ((↑|ArithmeticFunction.moebius r| : ℂ) *
        lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j) /
          ((d : ℂ) * (r : ℂ) * (Nat.totient r : ℂ))) * χ.evalNat (d*r)^2 *
            actualGramFirst χ c j f (d*r) * actualGramSecond χ c j g d r := by ring
    _ = _ := by
      rw [actualGram_character_square, lemma84Section8Weight]
      push_cast
      simp only [← Int.cast_abs, Complex.ofReal_intCast]
      ring

/-- Exact antidiagonal collapse of the actual Section 8 weight after the
Pi-bearing main term has been inserted. -/
theorem actualGram_weight_pi_collapse {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (n : ℕ) (hn : n ≠ 0) :
    (∑ dr ∈ n.divisorsAntidiagonal,
      lemma84Section8Weight χ c j dr.1 dr.2 * lemma83Pi χ dr.1 dr.2) =
      (‖χ.evalNat n‖ : ℂ) *
        lemma83Lambda (lemma83PaperBeta D c) n (1 - lemma83PaperBeta D c j) /
          (Nat.totient n : ℂ) := by
  have he : (∑ dr ∈ n.divisorsAntidiagonal,
      lemma84Section8Weight χ c j dr.1 dr.2 * lemma83Pi χ dr.1 dr.2) =
      ((‖χ.evalNat n‖ : ℂ) *
        lemma83Lambda (lemma83PaperBeta D c) n (1 - lemma83PaperBeta D c j) / (n : ℂ)) *
        ∑ dr ∈ n.divisorsAntidiagonal,
          (↑|ArithmeticFunction.moebius dr.2| : ℂ) * lemma83Pi χ dr.1 dr.2 /
            (Nat.totient dr.2 : ℂ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro dr hdr
    have hn' := (Nat.mem_divisorsAntidiagonal.mp hdr).1
    rw [lemma84Section8Weight, hn']
    push_cast
    have hc : (dr.1 : ℂ) * (dr.2 : ℂ) = (n : ℂ) := by exact_mod_cast hn'
    rw [hc]
    simp only [← Int.cast_abs, Complex.ofReal_intCast]
    ring
  rw [he, actualGram_pi_divisor_collapse χ n hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- The finite profile main term has the exact ramified totient coefficient.
K can be the differential/Volterra product evaluated at log(n)/B. -/
theorem actualGram_finite_main_attachment {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (K : ℕ → ℂ) :
    (∑ n ∈ S, ∑ dr ∈ n.divisorsAntidiagonal,
      lemma84Section8Weight χ c j dr.1 dr.2 * lemma83Pi χ dr.1 dr.2 * K n) =
    ∑ n ∈ S, (‖χ.evalNat n‖ : ℂ) *
      lemma83Lambda (lemma83PaperBeta D c) n (1 - lemma83PaperBeta D c j) /
        (Nat.totient n : ℂ) * K n := by
  apply sum_congr rfl
  intro n hn
  rw [← sum_mul, actualGram_weight_pi_collapse χ c j n (hS n hn)]

end ZhangLS.Spec
