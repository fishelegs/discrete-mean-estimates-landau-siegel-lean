import ZhangLS.Spec.Lemma83
import ZhangLS.Spec.Lemma58

/-!
# Original Lemma 8.4: unchanged statement

Source: arXiv:2211.02515v1, pp.46–47, TeX lines 2397–2427.
The Section 7 ξ coefficients and Π are exactly those of original Lemma 8.3.
Both paper cutoffs are strict, the error is additive, and no division by Π
occurs. The smoothing shifts are (2.22). The proof's Taylor citation to 5.6
is interpreted as the actual proved Taylor theorem 5.8, without using 5.6.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Original (2.22), used only for μ=6 or μ=7. -/
noncomputable def lemma84SmoothingBeta (D μ : ℕ) : ℂ :=
  if μ = 6 then 3 * I * (lemma44PaperAlpha D : ℂ) / 2
  else 5 * I * (lemma44PaperAlpha D : ℂ) / 2

/-- The paper's positive, strict real cutoff. -/
noncomputable def lemma84StrictCutoff (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) < x)

/-- The actual sum on the left of original Lemma 8.4. -/
noncomputable def lemma84XiSum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ lemma84StrictCutoff x,
    χ.evalNat n * lemma83Xi (lemma83PaperBeta D c) j n d r / (n : ℂ) *
      ((x / (n : ℝ) : ℝ) : ℂ)^(-lemma84SmoothingBeta D μ) *
        (Real.log (x / (n : ℝ)) : ℂ)

/-- The displayed G on p.46, retaining the original signs. -/
noncomputable def lemma84MainTerm (D : ℕ) (c : ℝ) (j : Fin 3) (μ : ℕ) (x : ℝ) : ℂ :=
  let a := lemma83PaperBeta D c (j+1)
  let b := lemma83PaperBeta D c (j+2)
  let m := lemma84SmoothingBeta D μ
  a*b/m^2 + (1-a*b/m^2-(a-m)*(b-m)/m*(Real.log x : ℂ))*(x : ℂ)^(-m)

/-- Original Lemma 8.4, with one fixed positive c′ and a uniform error
constant and modulus threshold. No contour estimate is an input hypothesis. -/
def Lemma84Target : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ μ d r : ℕ,
        (μ=6 ∨ μ=7) → 0 < d → 0 < r →
        (d*r : ℝ) < lemma23PaperP D * lemma56PaperT D^(-2 : ℤ) →
        ∀ x : ℝ, lemma56PaperT D < x → x < lemma23PaperP D →
          ‖lemma84XiSum χ c j μ d r x -
            LDerivAtOne χ * lemma83Pi χ d r * lemma84MainTerm D c j μ x‖ ≤
              C * lemma23PaperL D^(-6 : ℤ)

lemma lemma84_mem_strictCutoff {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ lemma84StrictCutoff x ↔ 0 < n ∧ (n : ℝ) < x := by
  simp only [lemma84StrictCutoff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn,_⟩,hx⟩
    exact ⟨hn,hx⟩
  · rintro ⟨hn,hnx⟩
    exact ⟨⟨hn,(Nat.le_floor_iff hx).mpr hnx.le⟩,hnx⟩

lemma lemma84_smoothing_beta_re (D μ : ℕ) : (lemma84SmoothingBeta D μ).re = 0 := by
  unfold lemma84SmoothingBeta
  split_ifs <;> simp

/-- Endpoint n=x contributes zero because of the logarithm. -/
lemma lemma84_logarithmic_endpoint (a m : ℂ) {x : ℝ} (hx : x ≠ 0) :
    a * ((x/x : ℝ) : ℂ)^(-m) * (Real.log (x/x) : ℂ) = 0 := by
  simp [hx]

/-- The factor at q=2 is genuinely zero when χ(2)=1 and 2|d, 2∤r. -/
lemma lemma84_pi_zero_at_two {D : ℕ} (χ : RealPrimitiveCharacter D)
    {d r : ℕ} (hd : d ≠ 0) (h2d : 2 ∣ d) (h2r : ¬2 ∣ r)
    (hχ : χ.evalNat 2 = 1) : lemma83Pi χ d r = 0 := by
  unfold lemma83Pi
  suffices (∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ r),
      (1 - (q : ℂ)⁻¹ - χ.evalNat q / (q : ℂ)) / (1 - (q : ℂ)⁻¹)) = 0 by
    rw [this,mul_zero]
  apply Finset.prod_eq_zero (i := 2)
  · exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h2d,hd⟩,h2r⟩
  · rw [hχ]
    norm_num

end ZhangLS.Spec
