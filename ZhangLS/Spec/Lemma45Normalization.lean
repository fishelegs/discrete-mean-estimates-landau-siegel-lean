import ZhangLS.Spec.Lemma44ApproximateFunctionalEquation

/-! # The actual normalized product and equation (4.10) -/

namespace ZhangLS.Spec

open Complex ComplexConjugate

set_option maxHeartbeats 1000000

noncomputable def lemma45ActualA {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s /
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s

noncomputable def lemma45ActualB {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  lemma44ActualZtilde χ ψ s *
    lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) /
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s

theorem lemma45_short_sum_inv_eq_conj {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) :
    lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod N)) s =
      conj (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) (conj s)) := by
  have hc (n : ℕ) : conj (ψ (n : ZMod N)) = ψ⁻¹ (n : ZMod N) :=
    MulChar.star_apply' ψ _
  simp only [lemma23ActualSectionFourF, lemma23SectionFourF,
    lemma23FiniteDirichletPolynomial, map_sum, map_mul, lemma44_Nu_conj,
    hc, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, conj_conj]

/-- The sharper reciprocal estimate preserves the paper's exponent `-100`. -/
theorem lemma45_omega1_F_inv_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    (hs : Lemma23InOmega1 D s) :
    ‖(lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s)⁻¹‖ ≤
      4 * lemma23PaperL D ^ 79 := by
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod N)) s
  let G := lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod N)) s
  have hn := lemma23_omega1_F_ne_zero χ ψ s hL hψ.2 hs
  have h41 := lemma23_lemma41_of_good_partial_sums χ ψ s hL hψ.2 hs
  have h42 := lemma23_lemma42_of_good_partial_sums χ ψ s hL hψ.2 hs
  have hp : 4 * lemma23PaperL D ^ (-227 : ℤ) ≤ 1 / 2 := by
    have hpow : (9 : ℝ) ≤ lemma23PaperL D ^ 227 := by
      have h2 : (9 : ℝ) ≤ lemma23PaperL D ^ 2 := by nlinarith
      exact h2.trans (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))
    rw [zpow_neg, zpow_ofNat]
    have hi := (inv_le_inv₀ (by positivity : 0 < lemma23PaperL D ^ 227)
      (by norm_num : (0 : ℝ) < 9)).mpr hpow
    norm_num at hi
    linarith
  have hprod : 1 / 2 ≤ ‖F‖ * ‖G‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (F * G)
    rw [norm_one, norm_sub_rev, norm_mul] at ht
    change ‖F * G - 1‖ ≤ _ at h42
    linarith
  have hG : ‖G‖ ≤ 2 * lemma23PaperL D ^ 79 := by
    change ‖F‖ + ‖G‖ ≤ _ at h41
    linarith [norm_nonneg F]
  change ‖F⁻¹‖ ≤ _
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  have hm := mul_le_mul_of_nonneg_left hG (norm_nonneg F)
  nlinarith

/-- Equation (4.10), with a single absolute error constant. -/
theorem lemma45_equation410 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) (hs1 : Lemma23InOmega1 D s) :
    ‖lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)‖ ≤
      (4 * lemma44ErrorConstant) * lemma23PaperL D ^ (-100 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hn := lemma23_omega1_F_ne_zero χ ψ s hL hψ.2 hs1
  have he := lemma44_actual_approximate_functional_equation χ ψ hD hψ hs
  have hi := lemma45_omega1_F_inv_bound χ ψ s hL hψ hs1
  have hid : lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s) =
      (DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
        (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
          lemma44ActualZtilde χ ψ s *
            lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))) *
        (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s)⁻¹ := by
    unfold lemma45ActualA lemma45ActualB
    field_simp
    <;> ring
  rw [hid, norm_mul]
  have hm := mul_le_mul he hi (norm_nonneg _)
    (mul_nonneg lemma44_error_constant_pos.le (by positivity))
  apply hm.trans_eq
  have hpow : lemma23PaperL D ^ (-179 : ℤ) * lemma23PaperL D ^ 79 =
      lemma23PaperL D ^ (-100 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ (by linarith : lemma23PaperL D ≠ 0)]
    norm_num
  calc
    _ = (4 * lemma44ErrorConstant) *
        (lemma23PaperL D ^ (-179 : ℤ) * lemma23PaperL D ^ 79) := by ring
    _ = _ := by rw [hpow]

end ZhangLS.Spec
