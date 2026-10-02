import ZhangLS.Spec.Lemma102CircleObjects
import ZhangLS.Spec.Lemma102UnshiftedInfiniteContourAlgebra
import ZhangLS.Spec.Lemma84ContourErrorBudget
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
set_option maxHeartbeats 2000000

noncomputable def lemma102_unshiftedPaperIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (x : ℝ) : ℂ → ℂ :=
  lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
    (lemma83PaperBeta D c (j+2)) ((0:ℂ))
    (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x

noncomputable def lemma102_unshiftedContourNumerator {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (s : ℂ) : ℂ :=
  (dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+1))*
    dirichletLFunction χ (1+s+lemma83PaperBeta D c (j+2))/dirichletLFunction χ (1+s))*
      lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+s)

def Lemma102UnshiftedContourPoint (D : ℕ) (s : ℂ) : Prop :=
  (s.re = -1/lemma23PaperL D ∧ |s.im| ≤ D) ∨
    (|s.im| = D ∧ -1/lemma23PaperL D ≤ s.re ∧ s.re ≤ 1/lemma23PaperL D)

lemma lemma102_unshifted_alpha_log_x_le_pi {D : ℕ} (hL : 0 < lemma23PaperL D)
    {x : ℝ} (hx : 0 < x) (hxP : x < lemma23PaperP D) :
    lemma44PaperAlpha D*Real.log x ≤ Real.pi := by
  have hxlog := (Real.log_lt_log hx hxP).le
  unfold lemma23PaperP at hxlog
  rw [Real.log_exp] at hxlog
  have hα : 0 < lemma44PaperAlpha D := by unfold lemma44PaperAlpha lemma23PaperP; rw [Real.log_exp]; positivity
  have hh := mul_le_mul_of_nonneg_left hxlog hα.le
  have he : lemma44PaperAlpha D*lemma23PaperL D^9 = Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp,div_mul_cancel₀ _ (pow_ne_zero _ hL.ne')]
  exact hh.trans_eq he

lemma lemma102_unshifted_actual_left_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 0 < lemma23PaperL D) (c : ℝ) (j : Fin 3) (d r : ℕ)
    {x M : ℝ} (hx : 0 < x) (hM : 0 ≤ M)
    (hnum : ∀ s : ℂ, Lemma102UnshiftedContourPoint D s → ‖lemma102_unshiftedContourNumerator χ c j d r s‖ ≤ M) :
    ‖∫ t : ℝ in -(D:ℝ)..D, lemma102_unshiftedPaperIntegrand χ c j d r x
      ((-1/lemma23PaperL D:ℝ)+I*(t:ℂ))‖ ≤
        M*Real.exp (-Real.log x/lemma23PaperL D)*Real.pi*lemma23PaperL D := by
  have hh := lemma84_left_vertical_integral_bound
    (fun t : ℝ => lemma102_unshiftedPaperIntegrand χ c j d r x ((-1/lemma23PaperL D:ℝ)+I*(t:ℂ)))
    (δ := 1/lemma23PaperL D) (H := D) (M := M) (by positivity) (by positivity) hM
    (Real.log x) ((0:ℂ)).im (by
      intro t ht
      have hs : Lemma102UnshiftedContourPoint D ((-1/lemma23PaperL D:ℝ)+I*(t:ℂ)) := by
        apply Or.inl
        constructor
        · simp
        · simpa using abs_le.mpr ⟨ht.1.le,ht.2⟩
      unfold lemma102_unshiftedPaperIntegrand
      dsimp only
      rw [lemma102_unshifted_actual_integrand_eq_log_kernel χ c j d r hx t,norm_mul]
      have hb := mul_le_mul_of_nonneg_right (hnum _ hs)
        (norm_nonneg (lemma84LogKernel (-1/lemma23PaperL D) (Real.log x) ((0:ℂ)).im t))
      simpa only [lemma102_unshiftedContourNumerator,neg_div] using hb)
  apply hh.trans_eq
  rw [show -(1/lemma23PaperL D)*Real.log x = -Real.log x/lemma23PaperL D by ring]
  field_simp

lemma lemma102_unshifted_actual_horizontal_bounds {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) (c : ℝ) (j : Fin 3) (d r : ℕ)
    {x M : ℝ} (hx : 1 ≤ x) (hxP : x < lemma23PaperP D) (hM : 0 ≤ M)
    (hnum : ∀ s : ℂ, Lemma102UnshiftedContourPoint D s → ‖lemma102_unshiftedContourNumerator χ c j d r s‖ ≤ M) :
    ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D),
      lemma102_unshiftedPaperIntegrand χ c j d r x ((σ:ℂ)-I*(D:ℂ))‖ +
    ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D),
      lemma102_unshiftedPaperIntegrand χ c j d r x ((σ:ℂ)+I*(D:ℂ))‖ ≤
      8*M*Real.exp (6*Real.pi)*(6*lemma44PaperAlpha D+1/lemma23PaperL D)/(D:ℝ)^2 := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hDpos : (1:ℝ) < D := by exact_mod_cast hD
  have hgeom := lemma84_paper_rectangle_geometry hD hL
  have hα := lemma83_alpha_small (by linarith only [hL] : 100 ≤ lemma23PaperL D)
  have hm := lemma102_zero_shift_norm hα.1
  have hmD : ‖(0:ℂ)‖ ≤ (D:ℝ)/2 := by linarith only [hm.2,hα.2,hDpos]
  have hscale : (6*lemma44PaperAlpha D)*Real.log x ≤ 6*Real.pi := by
    have hh := lemma102_unshifted_alpha_log_x_le_pi hLp hxp hxP
    linarith only [hh]
  have hpoint (s : ℂ) (hs : Lemma102UnshiftedContourPoint D s) (him : |s.im| = D)
      (hre : s.re ≤ 6*lemma44PaperAlpha D) :
      ‖lemma102_unshiftedPaperIntegrand χ c j d r x s‖ ≤ 4*M*Real.exp (6*Real.pi)/(D:ℝ)^2 := by
    have hk := lemma84_horizontal_kernel_bound s ((0:ℂ))
      (by linarith only [hDpos] : 0 < (D:ℝ)) (Real.log_nonneg hx) him hmD hre hscale
    unfold lemma102_unshiftedPaperIntegrand lemma84AnalyticCircleIntegrand
    rw [mul_div_assoc,lemma84_positive_cpow_eq_exp hxp,norm_mul]
    have hh := mul_le_mul (hnum s hs) hk (norm_nonneg _) hM
    exact hh.trans_eq (by ring)
  have hab : -1/lemma23PaperL D ≤ 6*lemma44PaperAlpha D := by
    have hi : 0 < 1/lemma23PaperL D := by positivity
    simp only [neg_div]
    linarith only [hi,hα.1]
  have hl (σ : ℝ) (hσ : σ ∈ Icc (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)) :
      ‖lemma102_unshiftedPaperIntegrand χ c j d r x ((σ:ℂ)-I*(D:ℂ))‖ ≤ 4*M*Real.exp (6*Real.pi)/(D:ℝ)^2 := by
    have hre : ((σ:ℂ)-I*(D:ℂ)).re = σ := by simp
    have him : |((σ:ℂ)-I*(D:ℂ)).im| = (D:ℝ) := by simp
    exact hpoint _ (Or.inr ⟨him,by rw [hre]; exact hσ.1,
      by rw [hre]; exact hσ.2.trans hgeom.2.2.2.2⟩) him (by rw [hre]; exact hσ.2)
  have hu (σ : ℝ) (hσ : σ ∈ Icc (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)) :
      ‖lemma102_unshiftedPaperIntegrand χ c j d r x ((σ:ℂ)+I*(D:ℂ))‖ ≤ 4*M*Real.exp (6*Real.pi)/(D:ℝ)^2 := by
    have hre : ((σ:ℂ)+I*(D:ℂ)).re = σ := by simp
    have him : |((σ:ℂ)+I*(D:ℂ)).im| = (D:ℝ) := by simp
    exact hpoint _ (Or.inr ⟨him,by rw [hre]; exact hσ.1,
      by rw [hre]; exact hσ.2.trans hgeom.2.2.2.2⟩) him (by rw [hre]; exact hσ.2)
  have hh := lemma84_horizontal_integrals_bound (lemma102_unshiftedPaperIntegrand χ c j d r x)
    hab (by positivity : 0 ≤ 4*M*Real.exp (6*Real.pi)/(D:ℝ)^2) hl hu
  exact hh.trans_eq (by ring)

end ZhangLS.Spec
