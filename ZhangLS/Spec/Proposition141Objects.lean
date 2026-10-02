import ZhangLS.Spec.Proposition21
import ZhangLS.Spec.Lemma61Parameters
import ZhangLS.Spec.Lemma53Kernels
import ZhangLS.Spec.Lemma32SeriesConvergence

/-! # Original Proposition 14.1: exact Section 14 objects

Source: arXiv:2211.02515v1, printed pp.76–79. The coefficients in this
section are arbitrary κ* ≪ τ₅ and a* ≪ 1 supported at n≤2P₄. They are
NOT the specialized Section 7 κ or coefficients used later in Section 15.
The n=0 values are immaterial because every paper sum is over positive n.
The β parameter is complex and uniform in the full open |β|<5α disk.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical ComplexConjugate

/-- Exactly (14.1), with its fixed implicit constant made explicit. -/
def Proposition141KappaBound (B : ℝ) (κ : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, 0 < n → ‖κ n‖ ≤ B * lemma34Tau 5 n

/-- Exactly (14.2). The upper support endpoint is CLOSED in the statement. -/
def Proposition141AdmissibleSequence (D : ℕ) (B : ℝ) (a : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, 0 < n → ‖a n‖ ≤ B) ∧
    ∀ n : ℕ, 2 * lemma61PaperP4 D < (n : ℝ) → a n = 0

noncomputable def proposition141Indices (D : ℕ) : Finset ℕ :=
  (Icc 1 ⌈2 * lemma61PaperP4 D⌉₊).filter
    (fun n : ℕ => (n : ℝ) ≤ 2 * lemma61PaperP4 D)

/-- The arbitrary infinite κ* Dirichlet series, with the actual character. -/
noncomputable def proposition141KappaSeries {p : ℕ} (κ : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  LSeries (fun n => κ n * ψ (n : ZMod p)) s

/-- The actual finite a* Dirichlet polynomial. -/
noncomputable def proposition141Polynomial {p : ℕ} (D : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  ∑ n ∈ proposition141Indices D, a n * ψ (n : ZMod p) / (n : ℂ)^s

/-- Upward J(1), including the actual center and closed height segment.
The factor i from ds=i dt cancels the i in 1/(2πi). -/
noncomputable def proposition141SegmentIntegral (D : ℕ) (f : ℂ → ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-(lemma23PaperL D ^ 405))..(lemma23PaperL D ^ 405),
      f (lemma23PaperCenter D + 1 + I * (t : ℂ))

/-- The integral Ĩ₂ before averaging. The Z-factor has actual modulus D*p. -/
noncomputable def proposition141Integral {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (κ a : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) : ℂ :=
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  proposition141SegmentIntegral D (fun s =>
    (lemma23DirichletZ (lemma44CharacterTwist χ ψ) s)⁻¹ *
      proposition141KappaSeries κ ψ s * proposition141Polynomial D a ψ⁻¹ (1-s) *
        lemma53PaperOmega D s)

noncomputable def proposition141ShiftWeight (D p : ℕ) (β : ℂ) : ℂ :=
  ((p : ℂ) * (lemma51PaperT0 D : ℂ))^β

/-- The actual Θ₂ from the start of Section 14, on genuine Ψ₁. -/
noncomputable def proposition141ThetaTwo {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ → ℂ) : ℂ :=
  ∑ ψ ∈ proposition21ActualPsi1Family χ,
    proposition141ShiftWeight D ψ.1.val β * proposition141Integral χ κ a ψ.2

/-- The ambient Ψ extension in (14.3). -/
noncomputable def proposition141AmbientMean {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ → ℂ) : ℂ :=
  ∑ ψ ∈ lemma33ActualFamily D,
    proposition141ShiftWeight D ψ.1.val β * proposition141Integral χ κ a ψ.2

/-- The innermost infinite arithmetic sum, retaining coprimality and χ(l).
Summability is a genuine separate analytic obligation, not part of the definition. -/
noncomputable def proposition141InnerMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (κ : ℕ → ℂ) (p d k : ℕ) : ℂ :=
  ∑' l : ℕ+, if (l : ℕ).Coprime k then
    χ.chi ((l : ℕ) : ZMod D) * κ (d*l) *
      lemma53PaperDelta D ((l : ℝ) / ((D : ℝ)*p*k)) else 0

/-- Exactly the arithmetic main term of Proposition 14.1. All d,k outside
these bounds vanish by (14.2); l remains genuinely infinite. -/
noncomputable def proposition141MainTerm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (κ a : ℕ → ℂ) : ℂ :=
  (Nat.totient D : ℂ)⁻¹ * ∑ p ∈ lemma33PrimeWindow D,
    proposition141ShiftWeight D p β *
      ∑ d ∈ proposition141Indices D, (d : ℂ)⁻¹ *
        ∑ k ∈ proposition141Indices D,
          (ArithmeticFunction.moebius k : ℂ) * χ.chi (k : ZMod D) * a (d*k) /
            ((k : ℂ) * (Nat.totient k : ℂ)) * proposition141InnerMain χ κ p d k

/-- Original asymptotic assertion. Fixed coefficient bounds precede ε; the
threshold is uniform over the actual χ, both arbitrary sequences, and β.
Assumption (A) is retained. There is no Section 7 theorem or arbitrary
averaged-error hypothesis in the target. -/
def Proposition141Target : Prop :=
  ∀ Bκ Ba : ℝ, 0 < Bκ → 0 < Ba → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ κ a : ℕ → ℂ, Proposition141KappaBound Bκ κ →
          Proposition141AdmissibleSequence D Ba a →
          ∀ β : ℂ, ‖β‖ < 5 * lemma44PaperAlpha D →
            ‖proposition141ThetaTwo χ β κ a - proposition141MainTerm χ β κ a‖ ≤
              ε * lemma33ActualPrimeMass D

/-- Regression: the support endpoint in the statement has not been replaced
by the strict endpoint used later in the printed proof. -/
theorem proposition141_mem_indices (D n : ℕ) :
    n ∈ proposition141Indices D ↔ 0 < n ∧ (n : ℝ) ≤ 2 * lemma61PaperP4 D := by
  simp only [proposition141Indices,mem_filter,mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    refine ⟨⟨h.1,?_⟩,h.2⟩
    exact_mod_cast h.2.trans (Nat.le_ceil _)

theorem proposition141_segment_real_part (D : ℕ) (t : ℝ) :
    (lemma23PaperCenter D + 1 + I*(t : ℂ)).re = 3/2 := by
  simp [lemma23PaperCenter]
  norm_num

theorem proposition141_zero_shift (D p : ℕ) :
    proposition141ShiftWeight D p 0 = 1 := by
  simp [proposition141ShiftWeight]

end ZhangLS.Spec
