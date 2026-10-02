import ZhangLS.Spec.Lemma171LeftMajorant
import ZhangLS.Spec.Lemma171UniformThresholds

/-! # Absolute uniform decay of the actual left-contour majorant -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
open scoped Topology
set_option maxHeartbeats 2000000

noncomputable def lemma171LeftErrorConstant : ℝ :=
  (2*Real.pi)⁻¹*(4*64^2*lemma32RegularProductBound (3/4))*
    Real.exp 1*17^2*Real.sqrt (8*Real.pi)

lemma lemma171_left_error_constant_pos : 0 < lemma171LeftErrorConstant := by
  have hK := lemma32_regular_product_bound_pos (3/4)
  unfold lemma171LeftErrorConstant
  positivity

lemma lemma171_left_majorant_polynomial_bound {D : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    lemma171LeftMajorant D ≤ lemma171LeftErrorConstant*(D : ℝ)^4*lemma23PaperL D^75*
      Real.exp (-(1/4 : ℝ)*lemma23PaperL D^(11/10 : ℝ)) := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by dsimp [L]; linarith
  have h30 : 1 ≤ L^30 := one_le_pow₀ hL
  have hsmall : 1/(64*L^30) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 64*L^30)).mpr
    nlinarith
  have hpoly : (1+16*L^30)^2 ≤ (17*L^30)^2 := by gcongr; linarith
  have hsqrt : Real.sqrt (8*Real.pi*L^30) = Real.sqrt (8*Real.pi)*L^15 := by
    rw [Real.sqrt_mul (by positivity)]
    have he : L^30 = (L^15)^2 := by ring
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (pow_nonneg hL0.le _)]
  have he : -(L^(11/10 : ℝ))/4 = -(1/4 : ℝ)*L^(11/10 : ℝ) := by ring
  have hK := lemma32_regular_product_bound_pos (3/4)
  change (2*Real.pi)⁻¹*(4*64^2*lemma32RegularProductBound (3/4)*(D : ℝ)^4)*
    Real.exp (-(L^(11/10 : ℝ))/4+1/(64*L^30))*(1+16*L^30)^2*
      Real.sqrt (8*Real.pi*L^30) ≤ _
  rw [Real.exp_add,hsqrt,he]
  calc
    _ ≤ (2*Real.pi)⁻¹*(4*64^2*lemma32RegularProductBound (3/4)*(D : ℝ)^4)*
        (Real.exp (-(1/4 : ℝ)*L^(11/10 : ℝ))*Real.exp 1)*(17*L^30)^2*
          (Real.sqrt (8*Real.pi)*L^15) := by gcongr
    _ = _ := by unfold lemma171LeftErrorConstant; dsimp [L]; ring

/-- The genuine left-line majorant tends to zero uniformly, with its absolute
constant and threshold fixed before any character is selected. -/
lemma lemma171_left_majorant_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → lemma171LeftMajorant D < ε := by
  obtain ⟨D₁,hD₁,hbound⟩ := lemma171_subexponential_absorption
    lemma171LeftErrorConstant (1/4) lemma171_left_error_constant_pos.le (by norm_num) 4 75 ε hε
  obtain ⟨D₂,hlog⟩ := eventually_atTop.mp
    (lemma171_log_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D hD
  have h1 : D₁ ≤ D := (le_max_left _ _).trans hD
  have h2 : D₂ ≤ D := (le_max_right _ _).trans hD
  exact (lemma171_left_majorant_polynomial_bound (hlog D h2)).trans_lt (hbound D h1)

end ZhangLS.Spec
