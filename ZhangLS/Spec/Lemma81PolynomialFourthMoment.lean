import ZhangLS.Spec.Lemma81FourthMomentArithmetic

/-! # Uniform fourth moment of actual finite character polynomials

The proof squares the actual polynomial, applies the proved second large
sieve to its genuine convolution coefficients, and proves their τ₂²/τ₄
energy bound. It holds throughout the original thin real strip and at every
height, with an explicit constant and no moment hypothesis.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Real Classical
set_option maxHeartbeats 2000000

lemma lemma81_thin_strip_exponential_weight {D n : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hn : 0 < n) (hnP : (n : ℝ) ≤ lemma23PaperP D ^ 2)
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    ‖Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖^2 ≤
      Real.exp (4*Real.pi) * (n : ℝ)⁻¹ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn := Real.log_nonneg hn1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hloghi : Real.log (n : ℝ) ≤ 2 * lemma23PaperL D ^ 9 := by
    have hh := Real.log_le_log hnr hnP
    simpa only [Real.log_pow,lemma23PaperP,Real.log_exp,Nat.cast_ofNat] using hh
  have hscale : lemma44PaperAlpha D * lemma23PaperL D ^ 9 = Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    exact div_mul_cancel₀ _ (pow_ne_zero 9 hLp.ne')
  have hphase : (1-2*s.re) * Real.log (n : ℝ) ≤ 4*Real.pi := by
    calc
      _ ≤ (2*lemma44PaperAlpha D) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [(abs_le.mp hs).1]) hlogn
      _ ≤ (2*lemma44PaperAlpha D) * (2*lemma23PaperL D ^ 9) :=
        mul_le_mul_of_nonneg_left hloghi (by positivity)
      _ = _ := by nlinarith only [hscale]
  have he : ‖Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖^2 =
      Real.exp ((1-2*s.re)*Real.log (n : ℝ)) * (n : ℝ)⁻¹ := by
    rw [Complex.norm_exp,pow_two,← Real.exp_add]
    have heq : (-s*(Real.log (n : ℝ) : ℂ)).re + (-s*(Real.log (n : ℝ) : ℂ)).re =
        (1-2*s.re)*Real.log (n : ℝ) + -Real.log (n : ℝ) := by
      simp only [mul_re,neg_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
      ring
    rw [heq,Real.exp_add,Real.exp_neg,Real.exp_log hnr]
  rw [he]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hphase) (by positivity)

lemma lemma81_convolution_coefficient_energy {D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hL : 3 ≤ lemma23PaperL D) (X : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B) {s : ℂ}
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊,
      ‖lemma23TupleConvolutionCoefficient X 2 a n * Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖^2) ≤
      81 * B^4 * Real.exp (4*Real.pi) * lemma23PaperL D ^ 36 := by
  let M := ⌊lemma23PaperP D ^ 2⌋₊
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hP1 : 1 ≤ lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hLp.le 9)
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast one_le_pow₀ hP1 (n := 2))
  have henergy : (∑ n ∈ Finset.Icc 1 M,
      ‖lemma23TupleConvolutionCoefficient X 2 a n * Complex.exp (-s*(Real.log (n : ℝ) : ℂ))‖^2) ≤
      (B^4 * Real.exp (4*Real.pi)) *
        ∑ n ∈ Finset.Icc 1 M, (lemma34Tau 2 n : ℝ)^2 * (n : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnP : (n : ℝ) ≤ lemma23PaperP D ^ 2 :=
      (show (n : ℝ) ≤ M by exact_mod_cast (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (sq_nonneg _))
    have hc := lemma81_tuple_coefficient_norm_le hB X 2 a ha n
    have hc2 : ‖lemma23TupleConvolutionCoefficient X 2 a n‖^2 ≤ B^4*(lemma34Tau 2 n : ℝ)^2 := by
      calc
        _ ≤ (B^2*(lemma34Tau 2 n : ℝ))^2 :=
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hc
        _ = _ := by ring
    rw [norm_mul,mul_pow]
    apply (mul_le_mul hc2 (lemma81_thin_strip_exponential_weight hL hnpos hnP hs)
      (sq_nonneg _) (by positivity)).trans_eq
    ring
  have hsum := lemma81_tau_two_square_harmonic_sum M hM1
  have hlogM : 1+Real.log (M : ℝ) ≤ 3*lemma23PaperL D ^ 9 := by
    have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
    have hh := Real.log_le_log hMp (Nat.floor_le (sq_nonneg (lemma23PaperP D)))
    simp only [Real.log_pow,lemma23PaperP,Real.log_exp,Nat.cast_ofNat] at hh
    have hh1 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ hL1
    linarith only [hh,hh1]
  have hlognonneg : 0 ≤ 1+Real.log (M : ℝ) := by
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith only [Real.log_nonneg hm]
  have hpow : (1+Real.log (M : ℝ))^4 ≤ 81*lemma23PaperL D ^ 36 := by
    apply (pow_le_pow_left₀ hlognonneg hlogM 4).trans_eq
    ring
  apply henergy.trans
  apply (mul_le_mul_of_nonneg_left (hsum.trans hpow) (by positivity : 0 ≤ B^4*Real.exp (4*Real.pi))).trans_eq
  ring

noncomputable def lemma81FourthMomentConstant : ℝ :=
  81*(32+Real.pi^2)*Real.exp (4*Real.pi)

lemma lemma81_fourth_moment_constant_pos : 0 < lemma81FourthMomentConstant := by
  unfold lemma81FourthMomentConstant
  positivity

/-- The actual fourth moment, uniform over all bounded coefficient sequences
of length at most P and all heights in the original thin real strip. -/
theorem lemma81_actual_polynomial_fourth_moment {D : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hL : 3 ≤ lemma23PaperL D) (X : ℕ) (hX : X ≤ ⌊lemma23PaperP D⌋₊) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B) {s : ℂ}
    (hs : |s.re-1/2| ≤ lemma44PaperAlpha D) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81FiniteCharacterPolynomial X a ψ.2 s‖^4) ≤
      lemma81FourthMomentConstant * B^4 * lemma23PaperP D^2 * lemma23PaperL D^36 := by
  let M := ⌊lemma23PaperP D ^ 2⌋₊
  let b := fun n => lemma23TupleConvolutionCoefficient X 2 a n *
    Complex.exp (-s*(Real.log (n : ℝ) : ℂ))
  have hXP : (X : ℝ) ≤ lemma23PaperP D :=
    (show (X : ℝ) ≤ ⌊lemma23PaperP D⌋₊ by exact_mod_cast hX).trans (Nat.floor_le (Real.exp_nonneg _))
  have hX2 : X^2 ≤ M := Nat.le_floor (by
    exact_mod_cast pow_le_pow_left₀ (Nat.cast_nonneg X) hXP 2)
  have hsquare {p : ℕ} (ψ : DirichletCharacter ℂ p) :
      lemma81FiniteCharacterPolynomial X a ψ s^2 =
        ∑ n ∈ Finset.Icc 1 M, b n * ψ (n : ZMod p) := by
    rw [lemma81_actual_polynomial_square_expansion]
    calc
      _ = ∑ n ∈ Finset.Icc 1 (X^2), b n * ψ (n : ZMod p) := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [b]
        ring
      _ = _ := by
        apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hX2)
        intro n hn hnot
        have hnlo := (Finset.mem_Icc.mp hn).1
        have hgt : X^2 < n := by
          by_contra hh
          exact hnot (Finset.mem_Icc.mpr ⟨hnlo,le_of_not_gt hh⟩)
        simp only [b,lemma81_tuple_coefficient_zero_of_large X 2 a hgt,zero_mul]
  have hmean : (∑ ψ ∈ lemma33ActualFamily D, ‖lemma81FiniteCharacterPolynomial X a ψ.2 s‖^4) =
      lemma33ActualMean D M b := by
    unfold lemma33ActualMean
    apply Finset.sum_congr rfl
    intro ψ hψ
    rw [show ‖lemma81FiniteCharacterPolynomial X a ψ.2 s‖^4 =
      ‖lemma81FiniteCharacterPolynomial X a ψ.2 s^2‖^2 by rw [norm_pow]; ring,hsquare]
  rw [hmean]
  apply (lemma33_actual_second_mean_bound hL b).trans
  have he := lemma81_convolution_coefficient_energy hB hL X a ha hs
  change (∑ n ∈ Finset.Icc 1 M, ‖b n‖^2) ≤ _ at he
  apply (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (32+Real.pi^2)*lemma23PaperP D^2)).trans_eq
  unfold lemma81FourthMomentConstant
  ring

end ZhangLS.Spec
