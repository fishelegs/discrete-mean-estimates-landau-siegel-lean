import ZhangLS.Spec.Lemma51
import ZhangLS.Spec.Lemma23

/-! # Auxiliary inputs for Lemma 5.9

The actual original closed strip, actual coefficients and actual L-function
are retained. The full `Lemma59Target` quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric MeasureTheory Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def Lemma59InRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| ≤ lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10

def Lemma59InExtendedOmega1 (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 - Real.log (lemma23PaperL D) / (100 * lemma23PaperL D) < s.re ∧
    s.re < 1 + Real.log (lemma23PaperL D) / (100 * lemma23PaperL D) ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 20

def Lemma59InExtendedOmega2 (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 - (lemma23PaperL D)⁻¹ < s.re ∧
    s.re < 1 + (lemma23PaperL D)⁻¹ ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 19

def Lemma59ZeroSeparated {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) (s : ℂ) (η : ℝ) : Prop :=
  ∀ ρ : ℂ, ψ.LFunction ρ = 0 → η * lemma44PaperAlpha D ≤ ‖s - ρ‖

def Lemma59Target : Prop :=
  ∀ c : ℝ, 0 < c → ∀ η : ℝ, 0 < η →
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ},
      Lemma59InRegion D s → Lemma59ZeroSeparated (D := D) ψ s η →
      ‖DirichletCharacter.LFunction ψ
        (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
        DirichletCharacter.LFunction ψ s‖ ≤ C * Real.log (lemma23PaperP D)

lemma lemma59_alpha_bounds {D : ℕ} (hL : 100 ≤ lemma23PaperL D) :
    0 < lemma44PaperAlpha D ∧ lemma44PaperAlpha D < (lemma23PaperL D)⁻¹ := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hL8 : lemma23PaperL D ≤ lemma23PaperL D ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 8)
  have hp : Real.pi < lemma23PaperL D ^ 8 := by linarith only [Real.pi_le_four, hL8, hL]
  have hm := mul_lt_mul_of_pos_right hp hLp
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  refine ⟨div_pos Real.pi_pos (pow_pos hLp 9), ?_⟩
  rw [inv_eq_one_div]
  apply (div_lt_div_iff₀ (pow_pos hLp 9) hLp).mpr
  nlinarith only [hm]

lemma lemma59_original_region_in_extended {D : ℕ} (hL : 100 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma59InRegion D s) :
    Lemma59InExtendedOmega2 D s ∧ Lemma51InExtendedRegion D s := by
  have ha := (lemma59_alpha_bounds hL).2
  have hre := abs_le.mp hs.1
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hpow : lemma23PaperL D ≤ lemma23PaperL D ^ 405 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 405)
  exact ⟨⟨by linarith only [hre.1, ha], by linarith only [hre.2, ha], by linarith only [hs.2]⟩,
    ⟨hs.1, by linarith only [hs.2, hpow, hL]⟩⟩

lemma lemma59_zero_separated_LFunction_ne_zero {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hL : 100 ≤ lemma23PaperL D) {s : ℂ} {η : ℝ}
    (hη : 0 < η) (hs : Lemma59ZeroSeparated (D := D) ψ s η) : ψ.LFunction s ≠ 0 := by
  intro hz
  have hh := hs s hz
  rw [sub_self, norm_zero] at hh
  exact (not_le_of_gt (mul_pos hη (lemma59_alpha_bounds hL).1)) hh

lemma lemma59_paper_offset_one_bounds {D : ℕ} {c : ℝ}
    (hL : 100 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : 5 * c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2) :
    0 < lemma23PaperOffsetOne D c ∧ lemma23PaperOffsetOne D c ≤ lemma44PaperAlpha D := by
  have ha := (lemma59_alpha_bounds hL).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hn : 0 ≤ 5 * c * lemma44PaperAlpha D * lemma23PaperL D := by positivity
  unfold lemma23PaperOffsetOne
  constructor
  · exact mul_pos ha (by linarith only [hsmall])
  · have hh := mul_nonneg ha.le hn
    nlinarith only [hh]

lemma lemma59_original_shift_in_extended {D : ℕ} {s : ℂ} {u : ℝ}
    (hL : 100 ≤ lemma23PaperL D) (hs : Lemma59InRegion D s)
    (hu : |u| ≤ lemma44PaperAlpha D) :
    Lemma59InExtendedOmega2 D (s + I * (u : ℂ)) := by
  have ha := lemma59_alpha_bounds hL
  have hainv : (lemma23PaperL D)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hL])
  have hu1 : |u| ≤ 1 := hu.trans (ha.2.le.trans hainv)
  have hsr := abs_le.mp hs.1
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith only [hsr.1, ha.2]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith only [hsr.2, ha.2]
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    have he : s.im + u - (lemma23PaperCenter D).im =
        (s.im - (lemma23PaperCenter D).im) + u := by ring
    rw [he]
    have ht := (abs_add_le (s.im - (lemma23PaperCenter D).im) u).trans
      (add_le_add hs.2 hu1)
    linarith only [ht]

end ZhangLS.Spec
