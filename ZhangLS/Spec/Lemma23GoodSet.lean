import ZhangLS.Spec.Lemma23X1Expansion

/-!
# The actual good-character conditions and Lemma 4.1

`Ψ₁` is defined by (3.4)--(3.6), not by conclusions about zeros or about `F`.
This file records those three conditions on the genuine partial sums and proves
Lemma 4.1 throughout the paper's full region `Ω₁`.  No exceptional-set count,
Assumption (A), kernel estimate, or polynomial norm estimate is an extra input.
-/

namespace ZhangLS.Spec

open MeasureTheory

noncomputable def lemma23PaperL (D : ℕ) : ℝ := Real.log (D : ℝ)

noncomputable def lemma23PaperP (D : ℕ) : ℝ := Real.exp (lemma23PaperL D ^ 9)

/-- The actual center `s₀ = 1/2 + 2π i L^519`. -/
noncomputable def lemma23PaperCenter (D : ℕ) : ℂ :=
  ⟨1 / 2, 2 * Real.pi * lemma23PaperL D ^ 519⟩

/-- The truncated convolution coefficient `varsigma` in Section 3. -/
noncomputable def lemma23ActualVarsigma {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) : ℂ :=
  ∑ q ∈ n.divisorsAntidiagonal with q.1 ≤ D ^ 4 ∧ q.2 ≤ D ^ 4,
    lemma23NuArithmeticFunction χ q.1 * lemma23UpsilonArithmeticFunction χ q.2

/-- The actual long tail `X₃`. -/
noncomputable def lemma23ActualX3 {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (D ^ 4) ⌊x⌋₊,
    lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
      Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))

/-- The actual product tail `X₄`. -/
noncomputable def lemma23ActualX4 {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (D ^ 4) ⌊x⌋₊,
    lemma23ActualVarsigma χ n * ψ (n : ZMod N) *
      Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))

/-- Exactly the three partial-sum inequalities defining the good set in (3.4)--(3.6).
In particular, no estimate for `F`, no approximate functional equation, and no
zero-location assertion is hidden in these fields. -/
structure Lemma23GoodPartialSums {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) : Prop where
  condition34 :
    ‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) ((D : ℝ) ^ 80)‖ +
      ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) ((D : ℝ) ^ 80)‖ +
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
        (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖) / t) <
      lemma23PaperL D ^ 1171
  condition35 :
    ‖lemma23ActualX3 χ ψ (lemma23PaperP D ^ 2)‖ +
      (∫ t in Set.Ioc ((D : ℝ) ^ 4) (lemma23PaperP D ^ 2),
        ‖lemma23ActualX3 χ ψ t‖ / t) < lemma23PaperL D ^ (-585 : ℤ)
  condition36 :
    ‖lemma23ActualX4 χ ψ ((D : ℝ) ^ 8)‖ +
      (∫ t in Set.Ioc ((D : ℝ) ^ 4) ((D : ℝ) ^ 8),
        ‖lemma23ActualX4 χ ψ t‖ / t) < lemma23PaperL D ^ (-633 : ℤ)

/-- The ambient family `Ψ` of primitive characters at primes in the paper's short interval. -/
def Lemma23InPsi {D p : ℕ} (ψ : DirichletCharacter ℂ p) : Prop :=
  p.Prime ∧ ψ.IsPrimitive ∧ lemma23PaperP D < (p : ℝ) ∧
    (p : ℝ) < lemma23PaperP D * (1 + lemma23PaperL D ^ (-68 : ℤ))

/-- Genuine membership in `Ψ₁`, rather than an assumed package of Section 4 conclusions. -/
def Lemma23InPsi1 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) : Prop :=
  Lemma23InPsi (D := D) ψ ∧ Lemma23GoodPartialSums χ ψ

/-- The full open region `Ω₁` of Lemma 4.1. -/
def Lemma23InOmega1 (D : ℕ) (s : ℂ) : Prop :=
  1 / 2 - Real.log (lemma23PaperL D) / (100 * lemma23PaperL D) < s.re ∧
    s.re < 1 + Real.log (lemma23PaperL D) / (100 * lemma23PaperL D) ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 5

private theorem lemma23_X1_div_integrable {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) :
    IntegrableOn (fun t : ℝ => ‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ / t)
      (Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80)) := by
  have h := lemma23_partial_sum_div_integrableOn_Ioc
    (N := D ^ 80) (lemma23ActualNu20CenteredCoefficient χ ψ (lemma23PaperCenter D))
  simpa only [Nat.cast_pow, ← lemma23ActualX1_eq_centered_partial_sum] using h

private theorem lemma23_X2_div_integrable {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) :
    IntegrableOn (fun t : ℝ => ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖ / t)
      (Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80)) := by
  have h := lemma23_partial_sum_div_integrableOn_Ioc
    (N := D ^ 80) (lemma23ActualUpsilon20CenteredCoefficient χ ψ (lemma23PaperCenter D))
  simpa only [Nat.cast_pow, ← lemma23ActualX2_eq_centered_partial_sum] using h

/-- Extract both endpoint and integral bounds from (3.4); integrability and
nonnegativity are proved, not added to good-set membership. -/
theorem Lemma23GoodPartialSums.x1_x2_bounds {D N : ℕ}
    {χ : RealPrimitiveCharacter D} {ψ : DirichletCharacter ℂ N}
    (h : Lemma23GoodPartialSums χ ψ) :
    (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) ((D : ℝ) ^ 80)‖ ≤
        lemma23PaperL D ^ 1171 ∧
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
        ‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ / t) ≤ lemma23PaperL D ^ 1171) ∧
    (‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) ((D : ℝ) ^ 80)‖ ≤
        lemma23PaperL D ^ 1171 ∧
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
        ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖ / t) ≤ lemma23PaperL D ^ 1171) := by
  have hsplit := integral_add (lemma23_X1_div_integrable χ ψ)
    (lemma23_X2_div_integrable χ ψ)
  simp only [← add_div] at hsplit
  have hbudget := h.condition34
  rw [hsplit] at hbudget
  have hI1 : 0 ≤ ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
      ‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ / t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact div_nonneg (norm_nonneg _) (by linarith [ht.1])
  have hI2 : 0 ≤ ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ) ^ 80),
      ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖ / t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact div_nonneg (norm_nonneg _) (by linarith [ht.1])
  have hE1 := norm_nonneg (lemma23ActualX1 χ ψ (lemma23PaperCenter D) ((D : ℝ) ^ 80))
  have hE2 := norm_nonneg (lemma23ActualX2 χ ψ (lemma23PaperCenter D) ((D : ℝ) ^ 80))
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The full region includes a vertical margin `+5`; this exponent absorbs that
margin and the real displacement, unlike a false bound with constant one at `L^405`. -/
theorem lemma23_center_displacement_le_three {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma23InOmega1 D s) :
    ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405 := by
  let L := lemma23PaperL D
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hdelta0 : 0 ≤ Real.log L / (100 * L) :=
    div_nonneg (Real.log_nonneg hL1) (by positivity)
  have hdelta1 : Real.log L / (100 * L) ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity : 0 < 100 * L)).mpr
    nlinarith [Real.log_le_self hLpos.le]
  have hre : |(lemma23PaperCenter D - s).re| ≤ 1 := by
    rw [Complex.sub_re]
    change |1 / 2 - s.re| ≤ 1
    apply abs_le.mpr
    change 1 / 2 - Real.log L / (100 * L) < s.re ∧
      s.re < 1 + Real.log L / (100 * L) ∧ _ at hs
    constructor <;> linarith [hs.1, hs.2.1]
  have him : |(lemma23PaperCenter D - s).im| ≤ L ^ 405 + 5 := by
    rw [Complex.sub_im, abs_sub_comm]
    exact hs.2.2.le
  have hLp : 3 ≤ L ^ 405 := by
    have hp : L ≤ L ^ 405 := by
      simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 405 by norm_num)
    exact hL.trans hp
  calc
    ‖lemma23PaperCenter D - s‖ ≤
        |(lemma23PaperCenter D - s).re| + |(lemma23PaperCenter D - s).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ L ^ 405 + 6 := by linarith
    _ ≤ 3 * L ^ 405 := by linarith

theorem lemma23_center_displacement_le {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma23InOmega1 D s) :
    ‖lemma23PaperCenter D - s‖ ≤ lemma23PaperL D ^ 406 := by
  calc
    ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405 :=
      lemma23_center_displacement_le_three hL hs
    _ ≤ lemma23PaperL D * lemma23PaperL D ^ 405 :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = lemma23PaperL D ^ 406 := by rw [pow_succ]; ring

/-- The paper's power-kernel estimate on its actual truncation interval. -/
theorem lemma23_omega1_power_kernel_le {D : ℕ} {s : ℂ} {t : ℝ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma23InOmega1 D s)
    (ht : 1 ≤ t) (htD : t ≤ (D : ℝ) ^ 80) :
    ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) t‖ ≤ lemma23PaperL D := by
  have hlogt : Real.log t ≤ 80 * lemma23PaperL D := by
    calc
      Real.log t ≤ Real.log ((D : ℝ) ^ 80) := Real.log_le_log (by linarith) htD
      _ = 80 * lemma23PaperL D := by rw [Real.log_pow]; rfl
  apply lemma23AbelPowerWeight_norm_le_of_strip_exponent (by linarith) ht hlogt
  rw [Complex.sub_re]
  change 1 / 2 - s.re ≤ Real.log (lemma23PaperL D) / (100 * lemma23PaperL D)
  linarith [hs.1]

/-- Lemma 4.1 with explicit absolute constant `2`, valid on the full `Ω₁` and
assuming only the genuine defining partial-sum conditions of `Ψ₁`. -/
theorem lemma23_lemma41_of_good_partial_sums {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hs : Lemma23InOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s‖ +
      ‖lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s‖ ≤
      2 * lemma23PaperL D ^ 79 := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast χ.modulus_pos
  have hEndpoint := lemma23_omega1_power_kernel_le hL hs
    (one_le_pow₀ hD1) (le_refl ((D : ℝ) ^ 80))
  rw [← Nat.cast_pow] at hEndpoint
  have hKernel : ∀ t ∈ Set.Ioc (1 : ℝ) ((D ^ 80 : ℕ) : ℝ),
      ‖lemma23AbelPowerWeight (lemma23PaperCenter D - s) t‖ ≤ lemma23PaperL D := by
    intro t ht
    apply lemma23_omega1_power_kernel_le hL hs ht.1.le
    simpa only [Nat.cast_pow] using ht.2
  have hbounds := hgood.x1_x2_bounds
  have hF := lemma23ActualSectionFourF_norm_le_of_X1_data χ ψ
    (lemma23PaperCenter D) s (lemma23PaperL D) hL hbounds.1.1 hbounds.1.2
    (lemma23_center_displacement_le hL hs) hEndpoint hKernel
  have hG := lemma23ActualSectionFourG_norm_le_of_X2_data χ ψ
    (lemma23PaperCenter D) s (lemma23PaperL D) hL hbounds.2.1 hbounds.2.2
    (lemma23_center_displacement_le hL hs) hEndpoint hKernel
  linarith

/-- Paper-facing membership form of Lemma 4.1. -/
theorem lemma23_lemma41 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    (hs : Lemma23InOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ +
      ‖lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) s‖ ≤
      2 * lemma23PaperL D ^ 79 :=
  lemma23_lemma41_of_good_partial_sums χ ψ s hL hψ.2 hs

end ZhangLS.Spec
