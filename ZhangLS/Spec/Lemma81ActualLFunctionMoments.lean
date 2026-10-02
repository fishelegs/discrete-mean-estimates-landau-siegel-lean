import ZhangLS.Spec.Lemma81ActualErrorMoment

/-! # Genuine L-function fourth and shifted-product moments in Lemma 8.1

The actual approximation theorem 6.1, actual Gaussian polynomial moments,
actual E₁ fourth moment, and actual Z bound discharge the first displayed
mean estimate on page 43. No mean bound or Assumption (A) is a hypothesis.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_three_term_fourth_bound {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (u+v+w)^4 ≤ 64*(u^4+v^4+w^4) := by
  have h₁ := add_pow_le (add_nonneg hu hv) hw 4
  have h₂ := add_pow_le hu hv 4
  norm_num only [Nat.reduceSub,Nat.reducePow,OfNat.ofNat] at h₁ h₂
  nlinarith only [h₁,h₂,pow_nonneg hw 4]

/-- Uniform fourth moment of the actual analytically continued L-function. -/
theorem lemma81_uniform_actual_L_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ _χ : RealPrimitiveCharacter D, ∀ s : ℂ,
      |s.re-1/2| ≤ lemma44PaperAlpha D →
      |s.im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 →
      (∑ ψ ∈ lemma33ActualFamily D, ‖ψ.2.LFunction s‖^4) ≤ C*lemma23PaperP D^2*lemma23PaperL D^36 := by
  obtain ⟨C₆₁,k,hC₆₁,hk,N₆₁,h₆₁⟩ := lemma61_proved
  obtain ⟨Np,hNp,hpoly⟩ := lemma81_uniform_six_one_polynomial_moments
  obtain ⟨Ne,hNe,herror⟩ := lemma81_uniform_actual_E1_fourth_moment
  let Z := Real.exp (600*Real.pi)
  let C := 64*lemma81FourthMomentConstant*(1+Z^4+136*C₆₁^4)
  have hCp : 0 < C := by
    dsimp [C]
    have hKp := lemma81_fourth_moment_constant_pos
    positivity
  refine ⟨C,hCp,max N₆₁ (max Np Ne),?_⟩
  intro D hD χ s hsre hsim
  have hD61 := (le_max_left N₆₁ (max Np Ne)).trans hD
  have hDp := (le_max_left Np Ne).trans ((le_max_right N₆₁ (max Np Ne)).trans hD)
  have hDe := (le_max_right Np Ne).trans ((le_max_right N₆₁ (max Np Ne)).trans hD)
  have hp := lemma61_parameters_at_threshold (hNp.trans hDp)
  have hL : 3 ≤ lemma23PaperL D := by linarith only [hp.2]
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hs61 : Lemma61InRegion D s := ⟨by linarith only [hsre,ha],by linarith only [hsim]⟩
  have hs51 : Lemma51InExtendedRegion D s := ⟨hsre,by linarith only [hsim,pow_nonneg hLp.le 405]⟩
  let M := lemma81FourthMomentConstant*lemma23PaperP D^2*lemma23PaperL D^36
  have hK : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ActualK D ψ.2 s‖^4) ≤ M :=
    (hpoly D hDp s hsre).1
  have hN : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ActualN D ψ.2⁻¹ (1-s)‖^4) ≤ M :=
    (hpoly D hDp s hsre).2.1
  have hE : (∑ ψ ∈ lemma33ActualFamily D, lemma61ActualE1 D ψ.2 s k^4) ≤ 136*M := by
    simpa only [M,mul_assoc] using herror D hDe s k hsre hk.le
  have hpoint (ψ : lemma33CharacterIndex D) (hψ : ψ ∈ lemma33ActualFamily D) :
      ‖ψ.2.LFunction s‖^4 ≤ 64*(‖lemma61ActualK D ψ.2 s‖^4 +
        (Z*‖lemma61ActualN D ψ.2⁻¹ (1-s)‖)^4 + (C₆₁*lemma61ActualE1 D ψ.2 s k)^4) := by
    have hfamily : Lemma23InPsi (D := D) ψ.2 := (Finset.mem_filter.mp hψ).2
    have hZ := lemma51_DirichletZ_norm_bound ψ.2 hfamily.2.1 hfamily.1.ne_one
      (lemma51_family_conductor_logs χ ψ.2 hL hfamily).1 hL hs51
    have happrox := h₆₁ ψ.2 hD61 hfamily hs61
    have hnorm : ‖ψ.2.LFunction s‖ ≤ ‖lemma61ActualK D ψ.2 s‖ +
        Z*‖lemma61ActualN D ψ.2⁻¹ (1-s)‖ + C₆₁*lemma61ActualE1 D ψ.2 s k := by
      have he : ψ.2.LFunction s = lemma61ActualK D ψ.2 s +
          lemma23DirichletZ ψ.2 s * lemma61ActualN D ψ.2⁻¹ (1-s) +
          (ψ.2.LFunction s-lemma61ActualK D ψ.2 s-lemma23DirichletZ ψ.2 s*lemma61ActualN D ψ.2⁻¹ (1-s)) := by ring
      calc
        _ ≤ ‖lemma61ActualK D ψ.2 s + lemma23DirichletZ ψ.2 s * lemma61ActualN D ψ.2⁻¹ (1-s)‖ +
            ‖ψ.2.LFunction s-lemma61ActualK D ψ.2 s-lemma23DirichletZ ψ.2 s*lemma61ActualN D ψ.2⁻¹ (1-s)‖ := by
          conv_lhs => rw [he]
          exact norm_add_le _ _
        _ ≤ (‖lemma61ActualK D ψ.2 s‖ + ‖lemma23DirichletZ ψ.2 s*lemma61ActualN D ψ.2⁻¹ (1-s)‖) +
            C₆₁*lemma61ActualE1 D ψ.2 s k := add_le_add (norm_add_le _ _) happrox
        _ ≤ _ := by
          rw [norm_mul]
          have hh := mul_le_mul_of_nonneg_right hZ
            (norm_nonneg (lemma61ActualN D ψ.2⁻¹ (1-s)))
          change ‖lemma23DirichletZ ψ.2 s‖ * ‖lemma61ActualN D ψ.2⁻¹ (1-s)‖ ≤
            Z * ‖lemma61ActualN D ψ.2⁻¹ (1-s)‖ at hh
          linarith only [hh]
    apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 4).trans
    exact lemma81_three_term_fourth_bound (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
      (mul_nonneg hC₆₁.le (lemma61_E1_pos ψ.2 s k).le)
  calc
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D, 64*(‖lemma61ActualK D ψ.2 s‖^4 +
        (Z*‖lemma61ActualN D ψ.2⁻¹ (1-s)‖)^4 + (C₆₁*lemma61ActualE1 D ψ.2 s k)^4) :=
      Finset.sum_le_sum hpoint
    _ = 64*((∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ActualK D ψ.2 s‖^4) +
        Z^4*(∑ ψ ∈ lemma33ActualFamily D, ‖lemma61ActualN D ψ.2⁻¹ (1-s)‖^4) +
        C₆₁^4*(∑ ψ ∈ lemma33ActualFamily D, lemma61ActualE1 D ψ.2 s k^4)) := by
      simp only [mul_pow,← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ 64*(M+Z^4*M+C₆₁^4*(136*M)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hK (mul_le_mul_of_nonneg_left hN (pow_nonneg (Real.exp_nonneg _) 4)))
          (mul_le_mul_of_nonneg_left hE (pow_nonneg hC₆₁.le 4))) (by norm_num)
    _ = _ := by dsimp [M,C]; ring

/-- The first displayed mean on page 43, with the actual two shifted
L-functions, the exact shifts, and the genuine good-character family. -/
theorem lemma81_uniform_actual_shifted_L_product_moment {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ χ : RealPrimitiveCharacter D, ∀ s : ℂ, Lemma81OnRightSegment D s →
      (∑ ψ ∈ lemma81GoodFamily χ,
        ‖ψ.2.LFunction (s+lemma52PaperBetaTwo D c) * ψ.2.LFunction (s+lemma52PaperBetaThree D c)‖^2) ≤
        C*lemma23PaperP D^2*lemma23PaperL D^36 := by
  obtain ⟨C,hC,Nm,hmoment⟩ := lemma81_uniform_actual_L_fourth_moment
  obtain ⟨Ns,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨C,hC,max Nm Ns,?_⟩
  intro D hD χ s hs
  have hDm := (le_max_left Nm Ns).trans hD
  have hDs := (le_max_right Nm Ns).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hDs)).1
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  have hb := lemma52_offset_bounds hL hc (hsmall D hDs)
  have hshift (b : ℝ) (hbn : 0 ≤ b) (hbhi : b ≤ 3*lemma44PaperAlpha D) :
      |(s+I*(b : ℂ)).re-1/2| ≤ lemma44PaperAlpha D ∧
      |(s+I*(b : ℂ)).im-(lemma23PaperCenter D).im| ≤ lemma23PaperL D^405+1 := by
    constructor
    · simp only [add_re,mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
      rw [hs.1]
      simpa using (abs_of_pos ha).le
    · have hh := abs_add_le (s.im-(lemma23PaperCenter D).im) b
      rw [abs_of_nonneg hbn] at hh
      have he : (s+I*(b : ℂ)).im-(lemma23PaperCenter D).im =
          (s.im-(lemma23PaperCenter D).im)+b := by simp; ring
      rw [he]
      linarith only [hh,hs.2,hbhi,haq]
  have h₂ := hshift _ hb.2.1.1 hb.2.1.2
  have h₃ := hshift _ hb.2.2.1 hb.2.2.2
  have hm₂ := hmoment D hDm χ (s+lemma52PaperBetaTwo D c) h₂.1 h₂.2
  have hm₃ := hmoment D hDm χ (s+lemma52PaperBetaThree D c) h₃.1 h₃.2
  have hbound := lemma81_product_moment_of_fourth (lemma33ActualFamily D)
    (fun ψ => ψ.2.LFunction (s+lemma52PaperBetaTwo D c))
    (fun ψ => ψ.2.LFunction (s+lemma52PaperBetaThree D c))
    (show 0 ≤ C*lemma23PaperP D^2*lemma23PaperL D^36 by positivity)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_pow,mul_one] using hm₂) (by simpa only [one_pow,mul_one] using hm₃)
  simp only [mul_one] at hbound
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)).trans hbound

end ZhangLS.Spec
