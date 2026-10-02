import ZhangLS.Spec.Lemma52Product
import ZhangLS.Spec.Lemma56
import ZhangLS.Spec.Lemma82WeightedAbel

namespace ZhangLS.Spec
open Complex Finset
open scoped Real

/-- Original (2.13) shifts, indexed cyclically with 0 representing j=1. -/
noncomputable def lemma82PaperBeta (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  if j = 0 then lemma52PaperBetaOne D c else
  if j = 1 then lemma52PaperBetaTwo D c else lemma52PaperBetaThree D c

/-- Original (2.22); used only with μ=6 or μ=7. -/
noncomputable def lemma82SmoothingBeta (D μ : ℕ) : ℂ :=
  if μ = 6 then 3 * I * (lemma44PaperAlpha D : ℂ) / 2
  else 5 * I * (lemma44PaperAlpha D : ℂ) / 2

/-- Positive natural numbers satisfying the paper's strict real cutoff. -/
noncomputable def lemma82StrictCutoff (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n:ℝ) < x)

/-- The actual character sum, with the original powers and logarithm. -/
noncomputable def lemma82ShiftedSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ lemma82StrictCutoff x,
    χ.evalNat n / (n:ℂ)^(1-lemma82PaperBeta D c j) *
      ((x/(n:ℝ) : ℝ) : ℂ)^(lemma82SmoothingBeta D μ) *
        (Real.log (x/(n:ℝ)) : ℂ)

noncomputable def lemma82MainTerm (D : ℕ) (c : ℝ) (j : Fin 3) (μ : ℕ) (x : ℝ) : ℂ :=
  (1 + (lemma82SmoothingBeta D μ - lemma82PaperBeta D c j) * (Real.log x : ℂ)) *
    (x:ℂ)^(lemma82SmoothingBeta D μ)

/-- Original Lemma 8.2. One absolute constant is chosen even before c';
the modulus threshold may depend on that fixed positive c'. -/
def Lemma82Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ x : ℝ,
        lemma56PaperT D < x → x < lemma23PaperP D →
        ∀ j : Fin 3, ∀ μ : ℕ, (μ=6 ∨ μ=7) →
          ‖lemma82ShiftedSum χ c j μ x - LDerivAtOne χ * lemma82MainTerm D c j μ x‖ ≤
            C * lemma23PaperL D ^ (-6 : ℤ)

lemma lemma82_beta_re (D : ℕ) (c : ℝ) (j : Fin 3) :
    (lemma82PaperBeta D c j).re = 0 := by
  unfold lemma82PaperBeta
  split_ifs <;> simp [lemma52PaperBetaOne,lemma52PaperBetaTwo,lemma52PaperBetaThree]

lemma lemma82_smoothing_beta_re (D μ : ℕ) : (lemma82SmoothingBeta D μ).re = 0 := by
  unfold lemma82SmoothingBeta
  split_ifs <;> simp

lemma lemma82_mem_strictCutoff {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ lemma82StrictCutoff x ↔ 0 < n ∧ (n:ℝ) < x := by
  simp only [lemma82StrictCutoff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn,_⟩,hx⟩
    exact ⟨hn,hx⟩
  · rintro ⟨hn,hnx⟩
    exact ⟨⟨hn,(Nat.le_floor_iff hx).mpr hnx.le⟩,hnx⟩

end ZhangLS.Spec
