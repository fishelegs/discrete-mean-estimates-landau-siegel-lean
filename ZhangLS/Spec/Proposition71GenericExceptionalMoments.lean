import ZhangLS.Spec.Proposition71ExceptionalMoments

/-! # Arbitrary τ₅ long coefficients and bounded finite short moments

These actual primitive-prime-family moments are independent of the character
in the functional equation. Both strict and closed long cutoffs are handled by
the caller's genuine coefficient sequence, without identifying κ* with κ*a.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_generic_tau_five_energy {B : ℝ} (hB : 0≤B)
    (X : ℕ) (hX : 1≤X) (a : ℕ → ℂ)
    (ha : ∀n∈Icc 1 X, ‖a n‖≤B*(lemma34Tau 5 n : ℝ)) :
    (∑ n∈Icc 1 X, ‖a n‖^2*(n : ℝ)⁻¹)≤B^2*(1+Real.log (X : ℝ))^25 := by
  calc
    _≤∑ n∈Icc 1 X, (B*(lemma34Tau 5 n : ℝ))^2*(n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (ha n hn)) (by positivity)
    _=B^2*∑ n∈Icc 1 X, (lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹ := by
      simp_rw [mul_pow,mul_assoc]
      rw [mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left (proposition71_tau_five_square_harmonic_sum X hX) (sq_nonneg B)

/-- A fully proved original critical-line second moment, with explicit logarithmic exponent 225. -/
theorem proposition71_generic_tau_five_second_moment {D : ℕ} {B : ℝ}
    (hB : 0≤B) (hL : 3≤lemma23PaperL D) (a : ℕ → ℂ) (ha : ∀ n∈Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖a n‖≤B*(lemma34Tau 5 n : ℝ))
    {s : ℂ} (hs : s.re=1/2) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ a ψ.2 s‖^2) ≤
        ((32+Real.pi^2)*3^25)*B^2*lemma23PaperP D^2*lemma23PaperL D^225 := by
  have hP1 : 1≤lemma23PaperP D := by
    apply Real.one_le_exp_iff.mpr
    exact pow_nonneg (by linarith : 0≤lemma23PaperL D) 9
  have hX : 1≤⌊lemma23PaperP D^2⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_pow₀ (n := 2) hP1)
  have hb := lemma33_actual_second_Dirichlet_mean_bound hL
    a s
  have hm : (∑ ψ ∈ lemma33ActualFamily D,
      ‖lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ a ψ.2 s‖^2) =
      lemma33ActualMean D ⌊lemma23PaperP D^2⌋₊
        (LSeries.term a s) := by
    simp only [lemma33ActualMean,lemma81_finite_character_polynomial_eq_cpow_sum,lemma33_original_Dirichlet_sum_eq_actual]
  rw [hm]
  norm_num only [hs,show (2:ℝ)*(1/2)=1 by norm_num,Real.rpow_one] at hb
  simp only [div_eq_mul_inv] at hb
  have he := proposition71_generic_tau_five_energy hB _ hX a ha
  have hlog : Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ) ≤ 2*lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<⌊lemma23PaperP D^2⌋₊)
      (Nat.floor_le (sq_nonneg (lemma23PaperP D)))
    simpa [Real.log_pow,lemma23PaperP] using hh
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hp9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL1
  have hlog0 : 0≤1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤⌊lemma23PaperP D^2⌋₊)
    linarith
  have hlp : (1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ))^25 ≤
      3^25*lemma23PaperL D^225 := by
    have hh := pow_le_pow_left₀ hlog0 (show 1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ)≤3*lemma23PaperL D^9 by linarith) 25
    simpa only [mul_pow,←pow_mul] using hh
  apply hb.trans
  have hf : 0≤(32+Real.pi^2)*lemma23PaperP D^2 := by positivity
  calc
    _≤(32+Real.pi^2)*lemma23PaperP D^2*(B^2*(1+Real.log (⌊lemma23PaperP D^2⌋₊ : ℝ))^25) := mul_le_mul_of_nonneg_left he hf
    _≤(32+Real.pi^2)*lemma23PaperP D^2*(B^2*(3^25*lemma23PaperL D^225)) := by gcongr
    _=_ := by ring


lemma proposition71_finite_polynomial_conjugate {p : ℕ} (X : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    conj (lemma81FiniteCharacterPolynomial X a ψ s)=
      lemma81FiniteCharacterPolynomial X (fun n => conj (a n)) ψ⁻¹ (conj s) := by
  unfold lemma81FiniteCharacterPolynomial lemma23FiniteDirichletPolynomial
  rw [map_sum]
  apply sum_congr rfl
  intro n hn
  have he : conj (ψ (n : ZMod p))=ψ⁻¹ (n : ZMod p) := MulChar.star_apply' ψ _
  simp only [map_mul,he,←Complex.exp_conj,map_neg,Complex.conj_ofReal]

lemma proposition71_generic_inverse_fourth_moment {D : ℕ} {B : ℝ}
    (hB : 0≤B) (hL : 3≤lemma23PaperL D) (X : ℕ) (hX : X≤⌊lemma23PaperP D⌋₊)
    (a : ℕ → ℂ) (ha : ∀n∈Icc 1 X, ‖a n‖≤B) {s : ℂ} (hs : s.re=1/2) :
    (∑ ψ∈lemma33ActualFamily D, ‖lemma81FiniteCharacterPolynomial X a ψ.2⁻¹ (1-s)‖^4)≤
      lemma81FourthMomentConstant*B^4*lemma23PaperP D^2*lemma23PaperL D^36 := by
  have he (ψ : lemma33CharacterIndex D) :
      ‖lemma81FiniteCharacterPolynomial X a ψ.2⁻¹ (1-s)‖=
        ‖lemma81FiniteCharacterPolynomial X (fun n => conj (a n)) ψ.2 (conj (1-s))‖ := by
    have hh := proposition71_finite_polynomial_conjugate X (fun n => conj (a n)) ψ.2 (conj (1-s))
    simp only [conj_conj] at hh
    rw [←hh,Complex.norm_conj]
  simp_rw [he]
  apply lemma81_actual_polynomial_fourth_moment hB hL X hX
  · intro n hn
    simpa only [Complex.norm_conj] using ha n hn
  · have hα := (lemma44_alpha_pos_le_one hL).1.le
    norm_num [hs]
    exact hα

end ZhangLS.Spec
