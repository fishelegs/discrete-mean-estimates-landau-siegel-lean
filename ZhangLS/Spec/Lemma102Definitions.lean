import ZhangLS.Spec.Lemma101ExactBridge
import ZhangLS.Spec.Lemma84LogPerronSeries

/-! Literal Lemma 10.2 of arXiv:2211.02515v1, TeX 2789–2860 (PDF pp.55–56).
The finite sum uses the original tent, actual Section 7 ξ and cyclic shifts.
The original additive exponents and strict/open endpoints are frozen here.
No theorem in a replacement file is to be identified with this target. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset

noncomputable def lemma102Sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊lemma101Cutoff D (d*r:ℝ) (63/125)⌋₊,
    χ.evalNat n * lemma83Xi (lemma83PaperBeta D c) j n d r / (n:ℂ) *
      (lemma111Tent (Real.log ((d*r:ℝ)*(n:ℝ))/Real.log (lemma23PaperP D)):ℂ)

noncomputable def lemma102Y1 (D : ℕ) (c : ℝ) (j : Fin 3) (y : ℝ) : ℂ :=
  (lemma83PaperBeta D c (j+1)+lemma83PaperBeta D c (j+2))*
    (Real.log (y/lemma23PaperP D^(1/2:ℝ)):ℂ) +
  (lemma83PaperBeta D c (j+1)*lemma83PaperBeta D c (j+2)/2)*
    ((Real.log (lemma23PaperP D^(63/125:ℝ)/y):ℂ)^2-
      2*(Real.log (lemma23PaperP D^(251/500:ℝ)/y):ℂ)^2)

noncomputable def lemma102Y2 (D : ℕ) (c : ℝ) (j : Fin 3) (y : ℝ) : ℂ :=
  (lemma83PaperBeta D c (j+1)+lemma83PaperBeta D c (j+2))*
    (Real.log (lemma23PaperP D^(63/125:ℝ)/y):ℂ) +
  (lemma83PaperBeta D c (j+1)*lemma83PaperBeta D c (j+2)/2)*
    (Real.log (lemma23PaperP D^(63/125:ℝ)/y):ℂ)^2

noncomputable def lemma102MainInitial {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) : ℂ :=
  LDerivAtOne χ*lemma83Pi χ d r/500*
    lemma83PaperBeta D c (j+1)*lemma83PaperBeta D c (j+2)*
      (Real.log (lemma23PaperP D):ℂ)

noncomputable def lemma102MainLower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) : ℂ :=
  (500*LDerivAtOne χ*lemma83Pi χ d r/(Real.log (lemma23PaperP D):ℂ))*
    (-1+lemma102Y1 D c j (d*r:ℝ))

noncomputable def lemma102MainUpper {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) : ℂ :=
  (500*LDerivAtOne χ*lemma83Pi χ d r/(Real.log (lemma23PaperP D):ℂ))*
    (1+lemma102Y2 D c j (d*r:ℝ))

/-- Literal uniform additive target (10.8)–(10.11). The absolute constant
precedes c′; only the modulus threshold is allowed to depend on c′. -/
def Lemma102Target : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ∀ j : Fin 3, ∀ d r : ℕ, 0<d → 0<r →
      ((d*r:ℝ)≤lemma23PaperP D^(1/2:ℝ)/lemma56PaperT D →
        ‖lemma102Sum χ c j d r-lemma102MainInitial χ c j d r‖ ≤ C*lemma23PaperL D^(-15:ℤ)) ∧
      (lemma23PaperP D^(1/2:ℝ)<(d*r:ℝ) →
        (d*r:ℝ)≤lemma23PaperP D^(251/500:ℝ)/lemma56PaperT D →
        ‖lemma102Sum χ c j d r-lemma102MainLower χ c j d r‖ ≤ C*lemma23PaperL D^(-15:ℤ)) ∧
      (lemma23PaperP D^(251/500:ℝ)<(d*r:ℝ) →
        (d*r:ℝ)≤lemma23PaperP D^(63/125:ℝ)/lemma56PaperT D →
        ‖lemma102Sum χ c j d r-lemma102MainUpper χ c j d r‖ ≤ C*lemma23PaperL D^(-15:ℤ)) ∧
      (Lemma101Transition D (d*r:ℝ) →
        ‖lemma102Sum χ c j d r‖ ≤ C*lemma23PaperL D^(-7:ℤ))

/-- Strict, unshifted logarithmic ξ sum. Its frequency is the complex number
zero, independent of the Section 8 Nat-indexed smoothing convention. -/
noncomputable def lemma102LogSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ lemma84StrictCutoff x,
    χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ)*
      (Real.log (x/(n:ℝ)):ℂ)

noncomputable def lemma102LogMain (D : ℕ) (c : ℝ) (j : Fin 3) (x : ℝ) : ℂ :=
  1+(lemma83PaperBeta D c (j+1)+lemma83PaperBeta D c (j+2))*(Real.log x:ℂ)+
    lemma83PaperBeta D c (j+1)*lemma83PaperBeta D c (j+2)/2*(Real.log x:ℂ)^2

end ZhangLS.Spec
