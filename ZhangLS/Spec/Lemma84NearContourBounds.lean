import ZhangLS.Spec.Lemma84RightTailBounds
import ZhangLS.Spec.ChiReciprocalRegression
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
set_option maxHeartbeats 1500000

noncomputable def lemma84UContourScale (D K : ℕ) : ℝ :=
  lemma84UGrowthConstant*Real.exp (lemma84UGrowthConstant/Real.log 2)*
    (1+20*Real.log (lemma23PaperL D))^K

lemma lemma84_u_contour_scale_nonneg {D K : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    0 ≤ lemma84UContourScale D K := by
  unfold lemma84UContourScale
  positivity [lemma84_u_growth_constant_pos,Real.log_nonneg hL]

lemma lemma84_right_majorant_polylog {D : ℕ} (hL : 100 ≤ lemma23PaperL D)
    (hlog : 20*Real.log (lemma23PaperL D) ≤ lemma23PaperL D)
    (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 9*lemma84UGrowthConstant ≤ (K:ℝ)) {b : ℝ} (hb : 0 < b) :
    lemma84RightLineMajorant b d r ≤ (1+b⁻¹)^3*lemma84UContourScale D K := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hh := lemma84_paper_near_one_prime_product (d*r) (Nat.mul_pos hd hr) (lemma23PaperL D)
    (1+b) lemma84UGrowthConstant K (by linarith only [hL]) hlog (by
      have hh : 0 < 1/lemma23PaperL D := by positivity
      linarith only [hb,hh])
    lemma84_u_growth_constant_pos.le hK (lemma83_paper_cutoff_log hL hd hr hcut)
  unfold lemma84RightLineMajorant lemma84UContourScale
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hh lemma84_u_growth_constant_pos.le).trans_eq (by ring)) (by positivity)

lemma lemma84_shifted_L_near_contour_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 100 ≤ lemma23PaperL D) (β s : ℂ)
    (hβre : β.re = 0) (hβnorm : ‖β‖ ≤ 3*lemma44PaperAlpha D)
    (hsre : -1/lemma23PaperL D ≤ s.re) (hsim : |s.im| ≤ D) :
    ‖dirichletLFunction χ (1+s+β)‖ ≤ 14*Real.exp 16*lemma23PaperL D := by
  have hα := lemma83_alpha_small hL
  have hLp : 0 < lemma23PaperL D := by linarith
  apply chi_actual_L_uniform_height_bound χ hD (by change 8 ≤ lemma23PaperL D; linarith only [hL])
  · change 1-4/lemma23PaperL D ≤ (1+s+β).re
    simp only [Complex.add_re,Complex.one_re,hβre,add_zero]
    have hi : 0 < 1/lemma23PaperL D := by positivity
    simp only [div_eq_mul_inv,one_mul,neg_mul] at hi hsre ⊢
    linarith only [hsre,hi]
  · simp only [Complex.add_im,Complex.one_im,zero_add]
    have hh := abs_add_le s.im β.im
    have hb := (Complex.abs_im_le_norm β).trans hβnorm
    linarith only [hh,hb,hsim,hα.2]

lemma lemma84_actual_near_contour_numerator_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 100 ≤ lemma23PaperL D)
    (hlog : 20*Real.log (lemma23PaperL D) ≤ lemma23PaperL D)
    {c : ℝ} (hc : 0 < c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 9*lemma84UGrowthConstant ≤ (K:ℝ)) (s : ℂ)
    (hsre : -1/lemma23PaperL D ≤ s.re) (hsim : |s.im| ≤ D)
    (C : ℝ) (hC : 0 ≤ C) (hinv : ‖(dirichletLFunction χ (1+s))⁻¹‖ ≤ C*lemma23PaperL D^26) :
    ‖(dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+1))*
        dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+2))/dirichletLFunction χ (1+s))*
      lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+s)‖ ≤
        (14*Real.exp 16)^2*C*lemma23PaperL D^28*lemma84UContourScale D K := by
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3 ≤ lemma23PaperL D) hc hsmall
  have h1 := lemma84_shifted_L_near_contour_bound χ hD hL (lemma83PaperBeta D c (j+1)) s (lemma83_beta_re D c (j+1)) (hb (j+1)) hsre hsim
  have h2 := lemma84_shifted_L_near_contour_bound χ hD hL (lemma83PaperBeta D c (j+2)) s (lemma83_beta_re D c (j+2)) (hb (j+2)) hsre hsim
  have hU := lemma84_actual_u_contour_bound χ c j d r K hd hr hL hlog hcut hK (1+s)
    (by
      simp only [Complex.add_re,Complex.one_re]
      have hh : -(1/lemma23PaperL D) ≤ s.re := by simpa only [neg_div] using hsre
      linarith only [hh])
  change ‖lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+s)‖ ≤ lemma84UContourScale D K at hU
  rw [norm_mul,div_eq_mul_inv,norm_mul,norm_mul]
  have hLp : 0 < lemma23PaperL D := by linarith
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hinv (norm_nonneg _) (by positivity))
    hU (norm_nonneg _) (by positivity : 0 ≤ (14*Real.exp 16*lemma23PaperL D)*(14*Real.exp 16*lemma23PaperL D)*(C*lemma23PaperL D^26))
  exact hprod.trans_eq (by ring)

/-- The actual (A)-based reciprocal theorem is consumed here; the resulting
bound on the full numerator has no reciprocal or zero-free input hypothesis. -/
theorem lemma84_actual_uniform_contour_numerator :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), D₀ ≤ D → NormalizedAssumptionA χ →
      ∀ c : ℝ, 0 < c → c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10 →
      ∀ j : Fin 3, ∀ d r K : ℕ, 0 < d → 0 < r →
      (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) →
      9*lemma84UGrowthConstant ≤ (K:ℝ) →
      100 ≤ lemma23PaperL D → 20*Real.log (lemma23PaperL D) ≤ lemma23PaperL D →
      ∀ s : ℂ,
        ((s.re = -1/lemma23PaperL D ∧ |s.im| ≤ D) ∨
          (|s.im| = D ∧ -1/lemma23PaperL D ≤ s.re ∧ s.re ≤ 1/lemma23PaperL D)) →
        ‖(dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+1))*
            dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+2))/dirichletLFunction χ (1+s))*
          lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+s)‖ ≤
            C*lemma23PaperL D^28*lemma84UContourScale D K := by
  obtain ⟨C,hC,D₀,hD02,hrec⟩ := chi_actual_shifted_polynomial_reciprocal
  refine ⟨(14*Real.exp 16)^2*C,by positivity,D₀,hD02,?_⟩
  intro D χ hDN hA c hc hsmall j d r K hd hr hcut hK hL hlog s hs
  have hh := hrec χ hDN hA s hs
  have hre : -1/lemma23PaperL D ≤ s.re := by rcases hs with h | h; exact h.1.ge; exact h.2.1
  have him : |s.im| ≤ D := by rcases hs with h | h; exact h.2; exact h.1.le
  exact lemma84_actual_near_contour_numerator_bound χ (by omega) hL hlog hc hsmall j d r K hd hr hcut hK s hre him C hC.le hh.2

end ZhangLS.Spec
