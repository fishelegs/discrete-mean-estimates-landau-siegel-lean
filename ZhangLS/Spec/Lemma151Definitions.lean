import ZhangLS.Spec.Lemma151Arithmetic
import ZhangLS.Spec.Lemma56
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Literal and repaired-basis Lemma 15.1 data are kept separate.
Equation (15.1) uses χψ, whereas the coefficient convolution immediately before
(15.5) uses ψ. Both conventions below refer to the same B from (12.2). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ComplexConjugate

noncomputable def lemma151P1 (D : ℕ) : ℝ := (lemma23PaperP D)^(0.504 : ℝ)
noncomputable def lemma151P2 (D : ℕ) : ℝ := (lemma23PaperP D)^(0.5 : ℝ) * lemma56PaperT D^(-10 : ℤ)
noncomputable def lemma151P3 (D : ℕ) : ℝ := (lemma23PaperP D)^(0.498 : ℝ)
noncomputable def lemma151Beta6 (D : ℕ) : ℂ := 3 * I * (lemma44PaperAlpha D : ℂ) / 2
noncomputable def lemma151Beta7 (D : ℕ) : ℂ := 5 * I * (lemma44PaperAlpha D : ℂ) / 2
noncomputable def lemma151Iota2 : ℂ := 0.94977 - 1.38995 * I
noncomputable def lemma151Iota3 : ℂ := -1.00635 - 0.22789 * I
noncomputable def lemma151Iota4 : ℂ := -0.68738 + 1.60688 * I

/-- The Section 8 kernel, retaining the strict support and actual complex power. -/
noncomputable def lemma151Kernel (X : ℝ) (β : ℂ) (n : ℕ) : ℂ :=
  if 0 < n ∧ (n : ℝ) < X then
    (1 - (Real.log (n : ℝ) / Real.log X : ℂ)) *
      ((X / n : ℝ) : ℂ)^β else 0

noncomputable def lemma151First (D n : ℕ) : ℂ :=
  (if (n : ℝ) < (lemma23PaperP D)^(1/2 : ℝ)
    then lemma151Kernel (lemma151P1 D) (lemma151Beta6 D) n else 0) +
  lemma151Iota2 * lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n

noncomputable def lemma151Second (D n : ℕ) : ℂ :=
  conj lemma151Iota3 * lemma151Kernel (lemma151P3 D) (lemma151Beta6 D) n +
  conj lemma151Iota4 * lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n

/-- Natural unramified extension of the χψ coefficient literally printed in (15.1). -/
noncomputable def lemma151BChiPsi (D n : ℕ) : ℂ :=
  ∑ a ∈ n.divisorsAntidiagonal, lemma151First D a.1 * lemma151Second D a.2

/-- Actual ψ coefficient of the same B. It is this coefficient that the subsequent
κ₁*b convolution uses. This is a change of basis, not a numerical repair. -/
noncomputable def lemma151BPsi {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) : ℂ :=
  χ.evalNat n * lemma151BChiPsi D n

/-- The original finite small-prime product, with strict q<D⁴. -/
noncomputable def lemma151Q (D : ℕ) : ℕ := ∏ q ∈ (Finset.range (D^4)).filter Nat.Prime, q

def Lemma151Supported (Q n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ∣ Q

/-- The exact source sum, including n₁, Q, coprimality, actual βj and χ. -/
noncomputable def lemma151ArithmeticSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (b : ℕ → ℂ) (n₁ : ℕ) : ℂ :=
  ∑' n : ℕ, if n.Coprime (lemma151Q D) then
    b (n₁*n) * χ.evalNat n * lemma151RhoStar χ (lemma83PaperBeta D c j) n / n else 0

noncomputable def lemma151FullKernelConstant (r a : ℝ) (j : ℕ) : ℂ :=
  (1 - j / (a : ℂ) + j / ((a : ℂ)^2*r*Real.pi*I)) *
    Complex.exp ((a*r*Real.pi : ℝ)*I) - j / ((a : ℂ)^2*r*Real.pi*I)

/-- Printed e1j'', retained literally rather than silently identified with the tail. -/
noncomputable def lemma151PrintedTail (j : ℕ) : ℂ :=
  (j : ℂ)/0.756 * ∫ z : ℝ in (0 : ℝ)..0.004,
    (Complex.exp (((3/2 : ℝ)*(0.504-z)*Real.pi : ℝ)*I) -
      Complex.exp (((3/4 : ℝ)*Real.pi : ℝ)*I))

/-- Small-phase expression dictated by Appendix B's last displayed residue.
It is not asserted here to equal the full arithmetic tail. -/
noncomputable def lemma151ResidueTail (j : ℕ) : ℂ :=
  (j : ℂ)/0.756 * ∫ z : ℝ in (0.5 : ℝ)..0.504,
    (Complex.exp (((3/2 : ℝ)*(0.504-z)*Real.pi : ℝ)*I) -
      Complex.exp ((0.006*Real.pi : ℝ)*I))

noncomputable def lemma151MainConstant (tail : ℕ → ℂ) (j : ℕ) : ℂ :=
  (lemma151FullKernelConstant 0.504 (3/2) j - tail j +
      lemma151Iota2 * lemma151FullKernelConstant 0.5 (5/2) j) *
    (conj lemma151Iota3 * lemma151FullKernelConstant 0.498 (3/2) j +
      conj lemma151Iota4 * lemma151FullKernelConstant 0.5 (5/2) j)

/-- The original target with its unspecified α₁ as an explicit parameter. No
value or rate for α₁ is invented, and no proof of this target is claimed. -/
def Lemma151OriginalTarget (c : ℝ) (α₁ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ D : ℕ in Filter.atTop,
    ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ∀ j : Fin 3, ∀ n₁ : ℕ, Lemma151Supported (lemma151Q D) n₁ →
    (n₁ : ℝ) < lemma56PaperT D →
    ‖lemma151ArithmeticSum χ c j (lemma151BChiPsi D) n₁ -
      χ.evalNat n₁ * (n₁.divisors.card : ℂ) * lemma151MainConstant lemma151PrintedTail (j.val+1)‖ ≤
      C * α₁ D * n₁.divisors.card

lemma lemma151_actual_psi_coefficient {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    (∑ a ∈ n.divisorsAntidiagonal,
      (χ.evalNat a.1 * lemma151First D a.1) *
        (χ.evalNat a.2 * lemma151Second D a.2)) = lemma151BPsi χ n := by
  unfold lemma151BPsi lemma151BChiPsi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he := (Nat.mem_divisorsAntidiagonal.mp ha).1
  rw [← he]
  simp only [RealPrimitiveCharacter.evalNat, Nat.cast_mul, map_mul]
  ring

end ZhangLS.Spec
