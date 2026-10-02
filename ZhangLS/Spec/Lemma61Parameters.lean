import ZhangLS.Spec.Lemma51
import ZhangLS.Spec.Lemma56
import ZhangLS.Spec.Lemma44ProductMellin
import ZhangLS.Spec.Lemma44RightMellinApproximation

/-! # Actual Gaussian inputs for the original Lemma 6.1

The original family, strict region, actual K/N and actual E1 are retained.
Gaussian inversion and both cutoff errors are proved for the actual weights.
The full Lemma61Target remains unproved: contour and Z-difference bounds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def lemma61GaussianStar (D : ℕ) (y : ℝ) : ℝ :=
  if (1 / 2 : ℝ) < y then zhangGaussianWeight D y else 0

noncomputable def lemma61PaperP4 (D : ℕ) : ℝ :=
  lemma23PaperP D * (lemma56PaperT D) ^ (-2 : ℤ) * lemma51PaperT0 D

noncomputable def lemma61WeightedPolynomial {p : ℕ}
    (D : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌈2 * x⌉₊, ψ (n : ZMod p) *
    Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) * (lemma61GaussianStar D (x / n) : ℂ)

noncomputable def lemma61ActualK {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  lemma61WeightedPolynomial D ψ (lemma61PaperP4 D) s

noncomputable def lemma61ActualN {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  lemma61WeightedPolynomial D ψ (lemma56PaperT D ^ 2) s

noncomputable def lemma61ShortPolynomial {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌈lemma56PaperT D ^ 3⌉₊).filter
      (fun (n : ℕ) => (n : ℝ) < lemma56PaperT D ^ 3),
    ψ (n : ZMod p) * Complex.exp (-s * (Real.log (n : ℝ) : ℂ))

noncomputable def lemma61ActualE1 {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (k : ℝ) : ℝ :=
  lemma23PaperL D ^ (-68 : ℤ) *
    (∫ v in (-(lemma23PaperL D ^ 20))..(lemma23PaperL D ^ 20),
      ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ *
        Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) +
      Real.exp (-k * lemma23PaperL D ^ 10)

def Lemma61InRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| < 2 * lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2

def Lemma61Target : Prop :=
  ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∃ D₀ : ℕ,
    ∀ {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi (D := D) ψ → ∀ {s : ℂ}, Lemma61InRegion D s →
    ‖DirichletCharacter.LFunction ψ s - lemma61ActualK D ψ s -
      lemma23DirichletZ ψ s * lemma61ActualN D ψ⁻¹ (1 - s)‖ ≤ C * lemma61ActualE1 D ψ s k

noncomputable def lemma61WeightedTerm {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ψ (n : ZMod p) *
    Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) * (lemma61GaussianStar D (x / n) : ℂ)

noncomputable def lemma61RightMellinIntegrand {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (B σ t : ℝ) : ℂ :=
  let w := (σ : ℂ) + (t : ℂ) * I
  DirichletCharacter.LFunction ψ (s + w) * exp (w * (Real.log B : ℂ)) *
    lemma57OmegaOne D w / w

noncomputable def lemma61GaussianCutoffCorrection {p : ℕ} (D : ℕ)
    (ψ : DirichletCharacter ℂ p) (x : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (fun m => ψ (m : ZMod p)) s n *
    ((zhangGaussianWeight D (x / n) - lemma61GaussianStar D (x / n) : ℝ) : ℂ)

end ZhangLS.Spec
