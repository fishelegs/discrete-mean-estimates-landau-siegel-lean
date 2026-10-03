import ZhangLS.Spec.AppendixBTailGaussianMellin
import ZhangLS.Spec.AppendixBKernelContour

/-! A single-pole continuation of the genuine complementary-tail integrand.
The apparent gamma pole is canceled before l1 is specialized or estimated. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex Metric Set Filter
open scoped Topology

noncomputable def appendixBTailHolomorphicNumerator (D : ℕ) (L z : ℝ)
    (β γ : ℂ) (l₁ : ℕ) (s : ℂ) : ℂ :=
  dslope (lemma151TailNumerator L z γ) γ s *
    zetaPoleRemoved (1+s)*(s-β)/zetaPoleRemoved (1+s-β)*
      lemma57OmegaOne D (s-γ)*exp (-s*(Real.log (l₁ : ℝ) : ℂ))

noncomputable def appendixBTailContinuedIntegrand (D : ℕ) (L z : ℝ)
    (β γ : ℂ) (l₁ : ℕ) (s : ℂ) : ℂ :=
  appendixBTailHolomorphicNumerator D L z β γ l₁ s/s

lemma appendixB_tail_continued_agrees (D : ℕ) (L z : ℝ) (β γ : ℂ) (l₁ : ℕ)
    {s : ℂ} (hs : s≠0) (hs1 : 1+s≠0) (hsβ : s≠β)
    (hsβ1 : 1+s-β≠0) (hsγ : s≠γ) :
    appendixBTailContinuedIntegrand D L z β γ l₁ s=
      lemma151TailIntegrand D L z β γ l₁ s := by
  unfold appendixBTailContinuedIntegrand appendixBTailHolomorphicNumerator lemma151TailIntegrand
  rw [lemma151_tail_gamma_quotient_eq L z γ hsγ]
  simp only [mul_div_assoc]
  rw [appendixB_zeta_ratio_regularized hs hs1 hsβ hsβ1]
  ring

lemma appendixB_tail_numerator_differentiableOn (D : ℕ) (L z : ℝ)
    (β γ : ℂ) (l₁ : ℕ) (S : Set ℂ)
    (hpos : ∀ s∈S, 0<(1+s).re ∧ 0<(1+s-β).re)
    (hfree : ∀ s∈S, zetaPoleRemoved (1+s-β)≠0) :
    DifferentiableOn ℂ (appendixBTailHolomorphicNumerator D L z β γ l₁) S := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  unfold appendixBTailHolomorphicNumerator
  have h₁ := (lemma55_actual_zeta_pole_removed_analyticAt (hpos s hs).1).differentiableAt
  have h₂ := (lemma55_actual_zeta_pole_removed_analyticAt (hpos s hs).2).differentiableAt
  have hc₁ : DifferentiableAt ℂ (fun u : ℂ => zetaPoleRemoved (1+u)) s :=
    h₁.comp s (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1+u) s)
  have hc₂ : DifferentiableAt ℂ (fun u : ℂ => zetaPoleRemoved (1+u-β)) s :=
    DifferentiableAt.comp s (g := zetaPoleRemoved) (f := fun u : ℂ => 1+u-β) h₂ (by fun_prop)
  have ho : DifferentiableAt ℂ (fun u : ℂ => lemma57OmegaOne D (u-γ)) s := by
    unfold lemma57OmegaOne
    fun_prop
  exact (((((lemma151_tail_gamma_quotient_differentiable L z γ) s).mul hc₁).mul
    (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => u-β) s)).div hc₂ (hfree s hs)).mul ho |>.mul
      (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => exp (-u*(Real.log (l₁ : ℝ) : ℂ))) s)

/-- The only residue is independent of l1. Both finite-D analytic correction
factors are retained. -/
lemma appendixB_tail_holomorphic_at_zero (D : ℕ) (L z : ℝ) {β γ : ℂ}
    (l₁ : ℕ) (hβ : β≠0) (hβ1 : 1-β≠0) (hγ : γ≠0) :
    appendixBTailHolomorphicNumerator D L z β γ l₁ 0=
      lemma151ExactTailResidue D L z β γ := by
  rw [lemma151_exact_tail_residue_factorization D L z hβ hβ1]
  unfold appendixBTailHolomorphicNumerator
  rw [lemma151_tail_gamma_quotient_eq L z γ (Ne.symm hγ)]
  simp only [add_zero,lemma55_actual_zeta_pole_removed_at_one,mul_one,
    zero_sub,neg_zero,zero_mul,exp_zero]
  ring

lemma appendixB_tail_single_pole_decomposition (D : ℕ) (L z : ℝ)
    (β γ : ℂ) (l₁ : ℕ) {s : ℂ} (hs : s≠0) :
    appendixBTailContinuedIntegrand D L z β γ l₁ s=
      appendixBTailHolomorphicNumerator D L z β γ l₁ 0/s+
      dslope (appendixBTailHolomorphicNumerator D L z β γ l₁) 0 s := by
  rw [dslope_of_ne _ hs,slope_def_module]
  unfold appendixBTailContinuedIntegrand
  simp only [sub_zero,smul_eq_mul]
  field_simp
  ring

/-- Exact rectangle-to-circle deformation after gamma cancellation. Zero-free
conditions are ordinary analytic hypotheses, not an assumed tail remainder. -/
theorem appendixB_tail_rectangle_circle (D : ℕ) (L z : ℝ)
    (β γ : ℂ) (l₁ : ℕ) {a b Y R : ℝ}
    (ha : R< -a) (hb : R<b) (hY : R<Y) (hR : 0<R)
    (hpos : ∀ s∈lemma44ClosedRectangle a b Y, 0<(1+s).re ∧ 0<(1+s-β).re)
    (hfree : ∀ s∈lemma44ClosedRectangle a b Y, zetaPoleRemoved (1+s-β)≠0) :
    lemma44GeneralRectangleBoundaryIntegral (appendixBTailContinuedIntegrand D L z β γ l₁)
      a b Y = circleIntegral (appendixBTailContinuedIntegrand D L z β γ l₁) 0 R := by
  let N := appendixBTailHolomorphicNumerator D L z β γ l₁
  let S := lemma44ClosedRectangle a b Y
  have hN := appendixB_tail_numerator_differentiableOn D L z β γ l₁ S hpos hfree
  have hball : closedBall (0 : ℂ) R⊆S := lemma84_closedBall_subset_rectangle ha.le hb.le hY.le
  have hnhds : S∈𝓝 (0 : ℂ) :=
    Filter.mem_of_superset (closedBall_mem_nhds (0 : ℂ) hR) hball
  have hrem := (Complex.differentiableOn_dslope hnhds).mpr hN
  apply lemma84_rectangle_circle_bridge_of_decomposition
    (w₁ := (0 : ℂ)) (w₂ := (0 : ℂ)) _ (dslope N 0) (N 0) 0 0
    ha hb hY (by simpa using hR) (by simpa using hR) hrem
  intro s hs hs0 _
  simpa only [sub_zero,zero_div,add_zero] using
    appendixB_tail_single_pole_decomposition D L z β γ l₁ hs0

/-- The actual local contour contains exactly the residue at zero.
Unlike the full ramp, it has no gamma contribution. -/
theorem appendixB_tail_circle_residue (D : ℕ) (L z : ℝ) {β γ : ℂ}
    (l₁ : ℕ) {R : ℝ} (hR : 0<R) (hβ : β≠0) (hβ1 : 1-β≠0) (hγ : γ≠0)
    (hpos : ∀ s∈closedBall (0 : ℂ) R, 0<(1+s).re ∧ 0<(1+s-β).re)
    (hfree : ∀ s∈closedBall (0 : ℂ) R, zetaPoleRemoved (1+s-β)≠0) :
    (2*(Real.pi : ℂ)*I)⁻¹*circleIntegral
      (appendixBTailContinuedIntegrand D L z β γ l₁) 0 R=
        lemma151ExactTailResidue D L z β γ := by
  let N := appendixBTailHolomorphicNumerator D L z β γ l₁
  have hN := appendixB_tail_numerator_differentiableOn D L z β γ l₁
    (closedBall (0 : ℂ) R) hpos hfree
  have hrem := (Complex.differentiableOn_dslope (closedBall_mem_nhds (0 : ℂ) hR)).mpr hN
  have hc := lemma84_circle_principal_parts
    (appendixBTailContinuedIntegrand D L z β γ l₁) (dslope N 0) (N 0) 0 0
    (w₁ := (0 : ℂ)) (w₂ := (0 : ℂ)) (by simpa using hR) (by simpa using hR) hrem
    (by
      intro s hs
      have hs0 := lemma84_sphere_ne_pole (show ‖(0 : ℂ)‖<R by simpa using hR) hs
      simpa only [N,sub_zero,zero_mul,zero_div,add_zero,←div_eq_mul_inv] using
        appendixB_tail_single_pole_decomposition D L z β γ l₁ hs0)
  rw [hc]
  simp only [add_zero]
  rw [←mul_assoc,inv_mul_cancel₀ (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero),one_mul]
  exact appendixB_tail_holomorphic_at_zero D L z l₁ hβ hβ1 hγ

/-- The genuine local zeta contour is evaluated unconditionally for the
paper-sized imaginary shifts; zero-free conditions are discharged locally. -/
theorem appendixB_tail_actual_circle_residue (D : ℕ) (L z : ℝ)
    {α : ℝ} (hα : 0<α) (hαs : α≤1/100) {β γ : ℂ}
    (hβ : β≠0) (hβre : β.re=0) (hβn : ‖β‖≤3*α)
    (hγ : γ≠0) (hγn : ‖γ‖≤3*α) (l₁ : ℕ) :
    (2*(Real.pi : ℂ)*I)⁻¹*circleIntegral
      (lemma151TailIntegrand D L z β γ l₁) 0 (5*α)=
        lemma151ExactTailResidue D L z β γ := by
  have hR : 0<5*α := by positivity
  have hβ1 : 1-β≠0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [hβre] at hr
  have hpos (s : ℂ) (hs : s∈closedBall (0 : ℂ) (5*α)) :
      0<(1+s).re ∧ 0<(1+s-β).re := by
    have hn : ‖s‖≤5*α := by simpa [Metric.mem_closedBall,dist_eq_norm] using hs
    have hr := (abs_le.mp (Complex.abs_re_le_norm s)).1
    simp only [add_re,one_re,sub_re,hβre,sub_zero]
    constructor <;> linarith
  have hfree (s : ℂ) (hs : s∈closedBall (0 : ℂ) (5*α)) :
      zetaPoleRemoved (1+s-β)≠0 := by
    have hn : ‖s‖≤5*α := by simpa [Metric.mem_closedBall,dist_eq_norm] using hs
    have hsb : ‖s-β‖≤8*α := (norm_sub_le _ _).trans (by linarith)
    have he : 1+s-β-1=s-β := by ring
    have hh := section15_zeta_regular_error (z := 1+s-β) (by rw [he]; linarith)
    rw [he] at hh
    exact section15_ne_zero_of_near_one hh (by linarith)
  have hc : circleIntegral (appendixBTailContinuedIntegrand D L z β γ l₁) 0 (5*α)=
      circleIntegral (lemma151TailIntegrand D L z β γ l₁) 0 (5*α) := by
    apply circleIntegral.integral_congr hR.le
    intro s hs
    have hn : ‖s‖=5*α := by simpa using mem_sphere_iff_norm.mp hs
    have hs0 : s≠0 := norm_pos_iff.mp (by rw [hn]; positivity)
    have hsb : s≠β := by intro he; rw [he] at hn; linarith
    have hsg : s≠γ := by intro he; rw [he] at hn; linarith
    have hp := hpos s (sphere_subset_closedBall hs)
    exact appendixB_tail_continued_agrees D L z β γ l₁ hs0
      (by intro he; rw [he] at hp; norm_num at hp) hsb
      (by intro he; rw [he] at hp; norm_num at hp) hsg
  rw [←hc]
  exact appendixB_tail_circle_residue D L z l₁ hR hβ hβ1 hγ hpos hfree

end ZhangLS.Spec
