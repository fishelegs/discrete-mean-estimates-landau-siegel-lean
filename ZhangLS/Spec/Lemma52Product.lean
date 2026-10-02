import ZhangLS.Spec.Lemma52ShiftEstimates

/-! # The actual three-shift product, with an explicit relative error -/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

noncomputable def lemma52PaperBetaOne (D : ℕ) (c : ℝ) : ℂ :=
  I * (lemma23PaperOffsetOne D c : ℂ)

noncomputable def lemma52PaperBetaTwo (D : ℕ) (c : ℝ) : ℂ :=
  I * (lemma23PaperOffsetTwo D c : ℂ)

noncomputable def lemma52PaperBetaThree (D : ℕ) (c : ℝ) : ℂ :=
  I * (lemma23PaperOffsetThree D c : ℂ)

theorem lemma52_beta_sum (D : ℕ) (c : ℝ) :
    lemma52PaperBetaOne D c + lemma52PaperBetaTwo D c + lemma52PaperBetaThree D c =
      2 * lemma52PaperBetaThree D c := by
  unfold lemma52PaperBetaOne lemma52PaperBetaTwo lemma52PaperBetaThree
  rw [← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add,
    lemma52_offset_sum]
  push_cast
  ring

noncomputable def lemma52ErrorConstant : ℝ := 126 * Real.pi

theorem lemma52_error_constant_pos : 0 < lemma52ErrorConstant := by
  unfold lemma52ErrorConstant
  positivity

def Lemma52Estimate {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (Y : ℂ → ℂ) (c : ℝ) (s : ℂ) (C : ℝ) : Prop :=
  ∃ e : ℂ, ‖e‖ ≤ C * lemma23PaperL D ^ (-123 : ℤ) ∧
    Y (s + lemma52PaperBetaOne D c) * Y (s + lemma52PaperBetaTwo D c) *
        Y (s + lemma52PaperBetaThree D c) / Y s =
      (((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ (lemma52PaperBetaThree D c) *
        (lemma23DirichletZ ψ s)⁻¹ * (1 + e)

theorem lemma52_actual_product_estimate {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ.IsPrimitive) (hp : p ≠ 1)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) {c : ℝ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hc : 0 < c)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 10)
    (hs : Lemma51InRegion D s) : Lemma52Estimate (D := D) ψ Y c s lemma52ErrorConstant := by
  have hb := lemma52_offset_bounds hL hc hsmall
  obtain ⟨e₁, he₁, hr₁⟩ := lemma52_actual_branch_shift ψ hψ hp Y hY hL hs hb.1.1 hb.1.2
  obtain ⟨e₂, he₂, hr₂⟩ := lemma52_actual_branch_shift ψ hψ hp Y hY hL hs hb.2.1.1 hb.2.1.2
  obtain ⟨e₃, he₃, hr₃⟩ := lemma52_actual_branch_shift ψ hψ hp Y hY hL hs hb.2.2.1 hb.2.2.2
  let E := e₁ + e₂ + e₃
  have hK : 0 ≤ (21 / 2 : ℝ) * lemma23PaperL D ^ (-114 : ℤ) := by
    have : 0 < lemma23PaperL D := by linarith
    positivity
  have hE : ‖E‖ ≤ 63 * Real.pi * lemma23PaperL D ^ (-123 : ℤ) := by
    calc
      ‖E‖ ≤ ‖e₁‖ + ‖e₂‖ + ‖e₃‖ :=
        (norm_add_le (e₁ + e₂) e₃).trans (add_le_add (norm_add_le e₁ e₂) le_rfl)
      _ ≤ (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) * lemma23PaperOffsetOne D c +
          (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) * lemma23PaperOffsetTwo D c +
          (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) * lemma23PaperOffsetThree D c :=
        add_le_add (add_le_add he₁ he₂) he₃
      _ = (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) *
          (2 * lemma23PaperOffsetThree D c) := by
        rw [← mul_add, ← mul_add, lemma52_offset_sum]
      _ ≤ (21 / 2) * lemma23PaperL D ^ (-114 : ℤ) *
          (6 * lemma44PaperAlpha D) :=
        mul_le_mul_of_nonneg_left (by linarith [hb.2.2.2]) hK
      _ = 63 * Real.pi * lemma23PaperL D ^ (-123 : ℤ) := by
        calc
          _ = 63 * (lemma44PaperAlpha D * lemma23PaperL D ^ (-114 : ℤ)) := by ring
          _ = _ := by rw [lemma52_alpha_error_scale hL]; ring
  have hEnorm : ‖E‖ ≤ 1 := hE.trans (lemma52_log_error_small hL)
  refine ⟨Complex.exp E - 1, ?_, ?_⟩
  · have hexp := Complex.norm_exp_sub_one_le hEnorm
    unfold lemma52ErrorConstant
    nlinarith
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hsExt := lemma51_shift_segment_region hL hs (w := 0) (by simp)
    (by simpa using pow_pos (by linarith : 0 < lemma23PaperL D) 20)
    (x := 0) (by norm_num)
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hsExt
  have him : 0 < s.im := hT.trans_le (lemma51_extended_region_data hL hsExt).2.2.1
  have hYne := lemma52_actual_branch_ne_zero ψ hψ hp Y hY him
  have hsq := hY.2 s him
  let a : ℂ := (Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) / 2
  change Y (s + lemma52PaperBetaOne D c) / Y s =
    Complex.exp (a * lemma52PaperBetaOne D c + e₁) at hr₁
  change Y (s + lemma52PaperBetaTwo D c) / Y s =
    Complex.exp (a * lemma52PaperBetaTwo D c + e₂) at hr₂
  change Y (s + lemma52PaperBetaThree D c) / Y s =
    Complex.exp (a * lemma52PaperBetaThree D c + e₃) at hr₃
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hpow : (((p : ℝ) * lemma51PaperT0 D : ℝ) : ℂ) ^ (lemma52PaperBetaThree D c) =
      Complex.exp ((Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) *
        lemma52PaperBetaThree D c) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hpR hT).ne'),
      ← Complex.ofReal_log (mul_pos hpR hT).le]
  have hsum : (a * lemma52PaperBetaOne D c + e₁) +
      (a * lemma52PaperBetaTwo D c + e₂) + (a * lemma52PaperBetaThree D c + e₃) =
      (Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) * lemma52PaperBetaThree D c + E := by
    calc
      _ = a * (lemma52PaperBetaOne D c + lemma52PaperBetaTwo D c +
          lemma52PaperBetaThree D c) + E := by dsimp [E]; ring
      _ = _ := by rw [lemma52_beta_sum]; dsimp [a]; ring
  change Y (s + lemma52PaperBetaOne D c) * Y (s + lemma52PaperBetaTwo D c) *
    Y (s + lemma52PaperBetaThree D c) / Y s = _
  calc
    _ = Y s ^ 2 * (Y (s + lemma52PaperBetaOne D c) / Y s) *
        (Y (s + lemma52PaperBetaTwo D c) / Y s) *
        (Y (s + lemma52PaperBetaThree D c) / Y s) := by field_simp
    _ = (lemma23DirichletZ ψ s)⁻¹ *
        Complex.exp (a * lemma52PaperBetaOne D c + e₁) *
        Complex.exp (a * lemma52PaperBetaTwo D c + e₂) *
        Complex.exp (a * lemma52PaperBetaThree D c + e₃) := by rw [hsq, hr₁, hr₂, hr₃]
    _ = (lemma23DirichletZ ψ s)⁻¹ * Complex.exp
        ((Real.log ((p : ℝ) * lemma51PaperT0 D) : ℂ) * lemma52PaperBetaThree D c + E) := by
      rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← add_assoc, hsum]
    _ = _ := by rw [Complex.exp_add, hpow]; ring

end ZhangLS.Spec
