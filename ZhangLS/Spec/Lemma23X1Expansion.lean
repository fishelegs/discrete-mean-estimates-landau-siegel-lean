import ZhangLS.Spec.Lemma23CoefficientBounds
import ZhangLS.Spec.Lemma23Nu20Bounds
import ZhangLS.Spec.Lemma23CharacterOrthogonality

/-!
# The actual `X₁` bridge in Lemma 4.1

This module instantiates the abstract Abel estimate with the coefficients from the paper.  It
defines `X₁` as the partial sums of the actual twentieth-power coefficients, proves that the
finite polynomial power is exactly the centered Abel sum, and packages the resulting conditional
`(log D)^79` bound.  The paper's estimates for `X₁` and the pointwise kernel bounds remain inputs.
-/

namespace ZhangLS.Spec

open MeasureTheory

/-- The centered coefficient of the actual twentieth power, including the zero value at index
zero required by finite Abel summation. -/
noncomputable def lemma23ActualNu20CenteredCoefficient {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    lemma23Nu20Coefficient χ n * ψ (n : ZMod N) *
      Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))

/-- Zhang's actual `X₁(x, ψ)`, expressed as a finite sum using the real cutoff `n ≤ x`. -/
noncomputable def lemma23ActualX1 {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    lemma23Nu20Coefficient χ n * ψ (n : ZMod N) *
      Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))

/-- The centered coefficient sequence for the actual twentieth power of `G`. -/
noncomputable def lemma23ActualUpsilon20CenteredCoefficient {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) *
      Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))

/-- Zhang's actual `X₂(x, ψ)`, the partial sums of the centered coefficients of `G^20`. -/
noncomputable def lemma23ActualX2 {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) *
      Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))

private theorem lemma23_sum_Icc_zero_eq_one_of_zero
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (N : ℕ) (h0 : f 0 = 0) :
    (∑ n ∈ Finset.Icc 0 N, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
  have hset : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : 0 ∉ Finset.Icc 1 N := by simp
  rw [hset, Finset.sum_insert hnot]
  simp [h0]

/-- The actual coefficient at zero vanishes. -/
@[simp] theorem lemma23ActualNu20CenteredCoefficient_zero {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s₀ : ℂ) :
    lemma23ActualNu20CenteredCoefficient χ ψ s₀ 0 = 0 := by
  simp [lemma23ActualNu20CenteredCoefficient]

@[simp] theorem lemma23ActualUpsilon20CenteredCoefficient_zero {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s₀ : ℂ) :
    lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀ 0 = 0 := by
  simp [lemma23ActualUpsilon20CenteredCoefficient]

/-- The partial sum of the centered coefficient sequence is exactly Zhang's `X₁`. -/
theorem lemma23ActualX1_eq_centered_partial_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ : ℂ) (x : ℝ) :
    lemma23ActualX1 χ ψ s₀ x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        lemma23ActualNu20CenteredCoefficient χ ψ s₀ n := by
  symm
  rw [lemma23_sum_Icc_zero_eq_one_of_zero
    (lemma23ActualNu20CenteredCoefficient χ ψ s₀) ⌊x⌋₊ (by simp)]
  unfold lemma23ActualX1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  simp [lemma23ActualNu20CenteredCoefficient, hn0]

/-- Exact character-family mean square for the actual `X₁` endpoint whenever its polynomial
length is below the prime modulus.  The coefficient sequence is the genuine `ν₂₀` from
Section 3, not an abstract sequence. -/
theorem lemma23ActualX1_character_mean_square_exact {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (s₀ : ℂ) (x : ℝ) (hp : p.Prime)
    (hshort : ⌊x⌋₊ < p) :
    (∑ ψ : DirichletCharacter ℂ p, ‖lemma23ActualX1 χ ψ s₀ x‖ ^ 2) =
      (p.totient : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ‖lemma23Nu20Coefficient χ n *
            Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by
  calc
    (∑ ψ : DirichletCharacter ℂ p, ‖lemma23ActualX1 χ ψ s₀ x‖ ^ 2) =
        ∑ ψ : DirichletCharacter ℂ p,
          ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              (lemma23Nu20Coefficient χ n *
                Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))) * ψ (n : ZMod p)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro ψ hψ
          apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
          unfold lemma23ActualX1
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (p.totient : ℝ) *
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ‖lemma23Nu20Coefficient χ n *
              Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 :=
        lemma23_prime_character_mean_square_exact hp hshort _

/-- The actual `X₁` mean square is bounded by a finite weighted `τ₄₀²` sum.  This is the
coefficient-majorant reduction needed before the remaining generalized-divisor mean estimate. -/
theorem lemma23ActualX1_character_mean_square_le_tau40 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (s₀ : ℂ) (x : ℝ) (hp : p.Prime)
    (hshort : ⌊x⌋₊ < p) :
    (∑ ψ : DirichletCharacter ℂ p, ‖lemma23ActualX1 χ ψ s₀ x‖ ^ 2) ≤
      (p.totient : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          lemma23Tau40 n ^ 2 *
            ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by
  rw [lemma23ActualX1_character_mean_square_exact χ s₀ x hp hshort]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    have hcoef := lemma23Nu20Coefficient_norm_le_tau40 χ n
    have hweight : 0 ≤ ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ := norm_nonneg _
    have htau : 0 ≤ lemma23Tau40 n := by
      unfold lemma23Tau40
      apply Finset.sum_nonneg
      intro q hq
      apply Finset.prod_nonneg
      intro i hi
      positivity
    have hprod :
        ‖lemma23Nu20Coefficient χ n‖ *
            ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ≤
          lemma23Tau40 n *
            ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ :=
      mul_le_mul_of_nonneg_right hcoef hweight
    calc
      (‖lemma23Nu20Coefficient χ n‖ *
          ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖) ^ 2 ≤
        (lemma23Tau40 n *
          ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖) ^ 2 :=
            (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hweight)
              (mul_nonneg htau hweight)).mpr hprod
      _ = lemma23Tau40 n ^ 2 *
          ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by rw [mul_pow]
  · positivity

/-- Exact character-family mean square for the actual `X₂` endpoint below a prime modulus. -/
theorem lemma23ActualX2_character_mean_square_exact {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (s₀ : ℂ) (x : ℝ) (hp : p.Prime)
    (hshort : ⌊x⌋₊ < p) :
    (∑ ψ : DirichletCharacter ℂ p, ‖lemma23ActualX2 χ ψ s₀ x‖ ^ 2) =
      (p.totient : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ‖lemma23Upsilon20Coefficient χ n *
            Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by
  calc
    (∑ ψ : DirichletCharacter ℂ p, ‖lemma23ActualX2 χ ψ s₀ x‖ ^ 2) =
        ∑ ψ : DirichletCharacter ℂ p,
          ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              (lemma23Upsilon20Coefficient χ n *
                Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))) * ψ (n : ZMod p)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro ψ hψ
          apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
          unfold lemma23ActualX2
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (p.totient : ℝ) *
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ‖lemma23Upsilon20Coefficient χ n *
              Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 :=
        lemma23_prime_character_mean_square_exact hp hshort _

/-- The actual `X₂` mean square is bounded by the matching finite weighted `τ₄₀²` sum. -/
theorem lemma23ActualX2_character_mean_square_le_tau40 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (s₀ : ℂ) (x : ℝ) (hp : p.Prime)
    (hshort : ⌊x⌋₊ < p) :
    (∑ ψ : DirichletCharacter ℂ p, ‖lemma23ActualX2 χ ψ s₀ x‖ ^ 2) ≤
      (p.totient : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          lemma23Tau40 n ^ 2 *
            ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by
  rw [lemma23ActualX2_character_mean_square_exact χ s₀ x hp hshort]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    have hcoef := lemma23Upsilon20Coefficient_norm_le_tau40 χ n
    have hweight : 0 ≤ ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ := norm_nonneg _
    have htau : 0 ≤ lemma23Tau40 n := by
      unfold lemma23Tau40
      apply Finset.sum_nonneg
      intro q hq
      apply Finset.prod_nonneg
      intro i hi
      positivity
    have hprod :
        ‖lemma23Upsilon20Coefficient χ n‖ *
            ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ≤
          lemma23Tau40 n *
            ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ :=
      mul_le_mul_of_nonneg_right hcoef hweight
    calc
      (‖lemma23Upsilon20Coefficient χ n‖ *
          ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖) ^ 2 ≤
        (lemma23Tau40 n *
          ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖) ^ 2 :=
            (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hweight)
              (mul_nonneg htau hweight)).mpr hprod
      _ = lemma23Tau40 n ^ 2 *
          ‖Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by rw [mul_pow]
  · positivity

/-- The partial sum of the centered `υ₂₀` coefficients is exactly Zhang's `X₂`. -/
theorem lemma23ActualX2_eq_centered_partial_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ : ℂ) (x : ℝ) :
    lemma23ActualX2 χ ψ s₀ x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀ n := by
  symm
  rw [lemma23_sum_Icc_zero_eq_one_of_zero
    (lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀) ⌊x⌋₊ (by simp)]
  unfold lemma23ActualX2
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  simp [lemma23ActualUpsilon20CenteredCoefficient, hn0]

/-- The twentieth power of the actual Section 4 polynomial is the finite Abel sum whose partial
sums are `X₁`.  Here the power weight is `x^(s₀-s)` in the paper's notation. -/
theorem lemma23ActualSectionFourF20_eq_centered_abel_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ s : ℂ) :
    (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s) ^ 20 =
      ∑ n ∈ Finset.Icc 0 (D ^ 80),
        lemma23AbelPowerWeight (s₀ - s) n *
          lemma23ActualNu20CenteredCoefficient χ ψ s₀ n := by
  classical
  rw [lemma23ActualSectionFourF20_expansion]
  calc
    (∑ n ∈ Finset.Icc 1 (D ^ 80),
        lemma23Nu20Coefficient χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) =
      ∑ n ∈ Finset.Icc 1 (D ^ 80),
        lemma23AbelPowerWeight (s₀ - s) n *
          lemma23ActualNu20CenteredCoefficient χ ψ s₀ n := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn0 : n ≠ 0 := by
              exact Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
            symm
            rw [lemma23AbelPowerWeight, lemma23ActualNu20CenteredCoefficient,
              if_neg hn0]
            calc
              Complex.exp ((s₀ - s) * (Real.log (n : ℝ) : ℂ)) *
                  (lemma23Nu20Coefficient χ n * ψ (n : ZMod N) *
                    Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))) =
                (lemma23Nu20Coefficient χ n * ψ (n : ZMod N)) *
                  (Complex.exp ((s₀ - s) * (Real.log (n : ℝ) : ℂ)) *
                    Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))) := by ring
              _ = (lemma23Nu20Coefficient χ n * ψ (n : ZMod N)) *
                  Complex.exp ((s₀ - s) * (Real.log (n : ℝ) : ℂ) +
                    (-s₀ * (Real.log (n : ℝ) : ℂ))) := by
                      rw [← Complex.exp_add]
              _ = lemma23Nu20Coefficient χ n * ψ (n : ZMod N) *
                  Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
                      congr 2
                      ring
    _ = ∑ n ∈ Finset.Icc 0 (D ^ 80),
          lemma23AbelPowerWeight (s₀ - s) n *
            lemma23ActualNu20CenteredCoefficient χ ψ s₀ n := by
            symm
            exact lemma23_sum_Icc_zero_eq_one_of_zero
              (fun n => lemma23AbelPowerWeight (s₀ - s) n *
                lemma23ActualNu20CenteredCoefficient χ ψ s₀ n)
              (D ^ 80) (by simp)

/-- The actual twentieth power of `G` is the finite Abel sum whose partial sums are `X₂`. -/
theorem lemma23ActualSectionFourG20_eq_centered_abel_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ s : ℂ) :
    (lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s) ^ 20 =
      ∑ n ∈ Finset.Icc 0 (D ^ 80),
        lemma23AbelPowerWeight (s₀ - s) n *
          lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀ n := by
  classical
  rw [lemma23ActualSectionFourG20_expansion]
  calc
    (∑ n ∈ Finset.Icc 1 (D ^ 80),
        lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) =
      ∑ n ∈ Finset.Icc 1 (D ^ 80),
        lemma23AbelPowerWeight (s₀ - s) n *
          lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀ n := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn0 : n ≠ 0 := by
              exact Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
            symm
            rw [lemma23AbelPowerWeight, lemma23ActualUpsilon20CenteredCoefficient,
              if_neg hn0]
            calc
              Complex.exp ((s₀ - s) * (Real.log (n : ℝ) : ℂ)) *
                  (lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) *
                    Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))) =
                (lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N)) *
                  (Complex.exp ((s₀ - s) * (Real.log (n : ℝ) : ℂ)) *
                    Complex.exp (-s₀ * (Real.log (n : ℝ) : ℂ))) := by ring
              _ = (lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N)) *
                  Complex.exp ((s₀ - s) * (Real.log (n : ℝ) : ℂ) +
                    (-s₀ * (Real.log (n : ℝ) : ℂ))) := by
                      rw [← Complex.exp_add]
              _ = lemma23Upsilon20Coefficient χ n * ψ (n : ZMod N) *
                  Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
                      congr 2
                      ring
    _ = ∑ n ∈ Finset.Icc 0 (D ^ 80),
          lemma23AbelPowerWeight (s₀ - s) n *
            lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀ n := by
            symm
            exact lemma23_sum_Icc_zero_eq_one_of_zero
              (fun n => lemma23AbelPowerWeight (s₀ - s) n *
                lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀ n)
              (D ^ 80) (by simp)

/-- If the actual `X₁` endpoint and weighted-integral bounds from (3.4) hold, and the
paper's pointwise power-kernel bounds hold on the required interval, then the actual `F` bound
in Lemma 4.1 follows.  This removes the former abstract expansion/partial-sum assumptions; only
the analytic estimates defining the good set `Ψ₁` remain hypotheses. -/
theorem lemma23ActualSectionFourF_norm_le_of_X1_data {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ s : ℂ) (L : ℝ)
    (hL : 3 ≤ L)
    (hEndpointX1 : ‖lemma23ActualX1 χ ψ s₀ ((D : ℝ) ^ 80)‖ ≤ L ^ 1171)
    (hX1Integral : ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
      ‖lemma23ActualX1 χ ψ s₀ t‖ / t ≤ L ^ 1171)
    (hZ : ‖s₀ - s‖ ≤ L ^ 406)
    (hEndpointKernel :
      ‖lemma23AbelPowerWeight (s₀ - s) ((D ^ 80 : ℕ) : ℝ)‖ ≤ L)
    (hKernel : ∀ t ∈ Set.Ioc (1 : ℝ) ((D ^ 80 : ℕ) : ℝ),
      ‖lemma23AbelPowerWeight (s₀ - s) t‖ ≤ L) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ ≤ L ^ 79 := by
  let c : ℕ → ℂ := lemma23ActualNu20CenteredCoefficient χ ψ s₀
  have hc0 : c 0 = 0 := by simp [c]
  have hExpansion :
      (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s) ^ 20 =
        ∑ k ∈ Finset.Icc 0 (D ^ 80),
          lemma23AbelPowerWeight (s₀ - s) k * c k := by
    rw [lemma23ActualSectionFourF20_eq_centered_abel_sum]
  have hCoefficientEndpoint :
      ‖∑ k ∈ Finset.Icc 0 (D ^ 80), c k‖ ≤ L ^ 1171 := by
    have hfloor : ⌊(D : ℝ) ^ 80⌋₊ = D ^ 80 := by
      rw [← Nat.cast_pow, Nat.floor_natCast]
    have hEq : (∑ k ∈ Finset.Icc 0 (D ^ 80), c k) =
        lemma23ActualX1 χ ψ s₀ ((D : ℝ) ^ 80) := by
      have hpart := (lemma23ActualX1_eq_centered_partial_sum χ ψ s₀
        ((D : ℝ) ^ 80)).symm
      rw [hfloor] at hpart
      simpa [c] using hpart
    rw [hEq]
    exact hEndpointX1
  have hPartialIntegral :
      ∫ t in Set.Ioc (1 : ℝ) ((D ^ 80 : ℕ) : ℝ),
        ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t ≤ L ^ 1171 := by
    rw [Nat.cast_pow]
    have hfun :
        (fun t : ℝ => ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t) =
        (fun t => ‖lemma23ActualX1 χ ψ s₀ t‖ / t) := by
      funext t
      simpa [c] using congrArg (fun z : ℂ => ‖z‖ / t)
        (lemma23ActualX1_eq_centered_partial_sum χ ψ s₀ t).symm
    rw [hfun]
    exact hX1Integral
  exact lemma23_sectionFour_L79_from_abel_data hL hc0 hExpansion
    hEndpointKernel hCoefficientEndpoint hZ hKernel hPartialIntegral

/-- The parallel conditional Lemma 4.1 estimate for the actual `G`, from the `X₂` endpoint and
weighted-integral bounds in (3.4). -/
theorem lemma23ActualSectionFourG_norm_le_of_X2_data {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N)
    (s₀ s : ℂ) (L : ℝ)
    (hL : 3 ≤ L)
    (hEndpointX2 : ‖lemma23ActualX2 χ ψ s₀ ((D : ℝ) ^ 80)‖ ≤ L ^ 1171)
    (hX2Integral : ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
      ‖lemma23ActualX2 χ ψ s₀ t‖ / t ≤ L ^ 1171)
    (hZ : ‖s₀ - s‖ ≤ L ^ 406)
    (hEndpointKernel :
      ‖lemma23AbelPowerWeight (s₀ - s) ((D ^ 80 : ℕ) : ℝ)‖ ≤ L)
    (hKernel : ∀ t ∈ Set.Ioc (1 : ℝ) ((D ^ 80 : ℕ) : ℝ),
      ‖lemma23AbelPowerWeight (s₀ - s) t‖ ≤ L) :
    ‖lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s‖ ≤ L ^ 79 := by
  let c : ℕ → ℂ := lemma23ActualUpsilon20CenteredCoefficient χ ψ s₀
  have hc0 : c 0 = 0 := by simp [c]
  have hExpansion :
      (lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s) ^ 20 =
        ∑ k ∈ Finset.Icc 0 (D ^ 80),
          lemma23AbelPowerWeight (s₀ - s) k * c k := by
    rw [lemma23ActualSectionFourG20_eq_centered_abel_sum]
  have hCoefficientEndpoint :
      ‖∑ k ∈ Finset.Icc 0 (D ^ 80), c k‖ ≤ L ^ 1171 := by
    have hfloor : ⌊(D : ℝ) ^ 80⌋₊ = D ^ 80 := by
      rw [← Nat.cast_pow, Nat.floor_natCast]
    have hEq : (∑ k ∈ Finset.Icc 0 (D ^ 80), c k) =
        lemma23ActualX2 χ ψ s₀ ((D : ℝ) ^ 80) := by
      have hpart := (lemma23ActualX2_eq_centered_partial_sum χ ψ s₀
        ((D : ℝ) ^ 80)).symm
      rw [hfloor] at hpart
      simpa [c] using hpart
    rw [hEq]
    exact hEndpointX2
  have hPartialIntegral :
      ∫ t in Set.Ioc (1 : ℝ) ((D ^ 80 : ℕ) : ℝ),
        ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t ≤ L ^ 1171 := by
    rw [Nat.cast_pow]
    have hfun :
        (fun t : ℝ => ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t) =
        (fun t => ‖lemma23ActualX2 χ ψ s₀ t‖ / t) := by
      funext t
      simpa [c] using congrArg (fun z : ℂ => ‖z‖ / t)
        (lemma23ActualX2_eq_centered_partial_sum χ ψ s₀ t).symm
    rw [hfun]
    exact hX2Integral
  exact lemma23_sectionFour_L79_from_abel_data hL hc0 hExpansion
    hEndpointKernel hCoefficientEndpoint hZ hKernel hPartialIntegral

end ZhangLS.Spec
