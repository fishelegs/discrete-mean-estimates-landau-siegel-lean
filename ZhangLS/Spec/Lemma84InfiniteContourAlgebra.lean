import ZhangLS.Spec.Lemma84FiniteContour
import ZhangLS.Spec.Lemma84RightTailBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
set_option maxHeartbeats 1500000

lemma lemma84_integral_split_three (f : ℝ → ℂ) (hi : Integrable f) {H : ℝ} (hH : 0 ≤ H) :
    (∫ t : ℝ, f t) = (∫ t : ℝ in Iic (-H), f t) +
      (∫ t : ℝ in -H..H, f t) + (∫ t : ℝ in Ioi H, f t) := by
  have hall := integral_add_compl (s := Iic H) measurableSet_Iic hi
  rw [compl_Iic] at hall
  have hdis : Disjoint (Iic (-H)) (Ioc (-H) H) := Set.disjoint_left.mpr (by
    intro t ht ht'
    exact (not_lt_of_ge ht) ht'.1)
  have hp := setIntegral_union hdis measurableSet_Ioc hi.integrableOn hi.integrableOn
  rw [Iic_union_Ioc_eq_Iic (by linarith : -H ≤ H)] at hp
  rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
  rw [←hp]
  exact hall.symm

lemma lemma84_normalizer_norms :
    ‖(2*Real.pi:ℂ)⁻¹‖ ≤ 1 ∧ ‖(2*Real.pi*I:ℂ)⁻¹‖ ≤ 1 := by
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  constructor <;> simp only [norm_inv,norm_mul,norm_I,mul_one,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  · exact inv_le_one_of_one_le₀ hpi
  · exact inv_le_one_of_one_le₀ hpi

lemma lemma84_normalized_boundary_error (X C R L lo hi tl tr : ℂ)
    (hX : X=(2*Real.pi:ℂ)⁻¹*(tl+R+tr))
    (hC : C=(2*Real.pi:ℂ)⁻¹*(R-L)+(2*Real.pi*I:ℂ)⁻¹*(lo-hi)) :
    ‖X-C‖ ≤ ‖L‖+‖lo‖+‖hi‖+‖tl‖+‖tr‖ := by
  let a : ℂ := (2*Real.pi:ℂ)⁻¹
  let b : ℂ := (2*Real.pi*I:ℂ)⁻¹
  have hne : ‖a‖ ≤ 1 := lemma84_normalizer_norms.1
  have hni : ‖b‖ ≤ 1 := lemma84_normalizer_norms.2
  have ha (z : ℂ) : ‖a*z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hne
  have hb (z : ℂ) : ‖b*z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hni
  have he : X-C = a*L+a*tl+a*tr-b*lo+b*hi := by rw [hX,hC]; dsimp [a,b]; ring
  rw [he]
  have h1 := norm_add_le (a*L) (a*tl)
  have h2 := norm_add_le (a*L+a*tl) (a*tr)
  have h3 := norm_sub_le (a*L+a*tl+a*tr) (b*lo)
  have h4 := norm_add_le (a*L+a*tl+a*tr-b*lo) (b*hi)
  linarith only [h1,h2,h3,h4,ha L,ha tl,ha tr,hb lo,hb hi]

/-- The exact actual Perron identity and finite contour geometry reduce the
sum-to-circle error to five genuine boundary integrals. -/
lemma lemma84_actual_sum_circle_boundary_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) {ρ : ℝ}
    (hρ : 0 < 1-ρ) (hclose : 1-ρ ≤ 64*lemma23PaperL D^(-2022 : ℤ))
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0 < d) (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    let F := lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x
    ‖lemma84XiSum χ c j μ d r x-lemma84PaperCircle χ c j μ d r x‖ ≤
      ‖∫ t : ℝ in -(D:ℝ)..D, F ((-1/lemma23PaperL D:ℝ)+I*(t:ℂ))‖ +
      ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D), F ((σ:ℂ)-I*(D:ℂ))‖ +
      ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D), F ((σ:ℂ)+I*(D:ℂ))‖ +
      ‖∫ t : ℝ in Iic (-(D:ℝ)), F ((6*lemma44PaperAlpha D:ℝ)+I*(t:ℂ))‖ +
      ‖∫ t : ℝ in Ioi (D:ℝ), F ((6*lemma44PaperAlpha D:ℝ)+I*(t:ℂ))‖ := by
  dsimp only
  have hα := (lemma84_paper_rectangle_geometry hD hL).1
  have hb : 0 < 6*lemma44PaperAlpha D := by positivity
  have hi := lemma84_actual_right_line_integrable χ hD c j μ d r hb hx
  have hper := lemma84_actual_xi_perron_factored χ c j μ d r hd hr hb hx
  rw [lemma84_integral_split_three _ hi (show 0 ≤ (D:ℝ) by positivity)] at hper
  have hfin := lemma84_actual_normalized_finite_contour χ hD hL hρ hclose hzero hsimple hunique c j μ d r hx
  exact lemma84_normalized_boundary_error _ _ _ _ _ _ _ _ hper hfin.symm

end ZhangLS.Spec
