import ZhangLS.Spec.ChiUniformLBound
import ZhangLS.Spec.Lemma55FullZeroExclusion
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax

namespace ZhangLS.Spec
open Complex Metric Set
open scoped Topology Real
set_option maxHeartbeats 1000000

/-- Entire removal of the exceptional zero with a bounded-height normalization.
The multiplier is (s−ρ+1)/(s−ρ), so no conductor-height loss occurs at the Euler anchor. -/
noncomputable def chiExceptionalRemoved {D : ℕ} (χ : RealPrimitiveCharacter D)
    (ρ : ℝ) (s : ℂ) : ℂ :=
  dirichletLFunction χ s + dslope (dirichletLFunction χ) (ρ : ℂ) s

lemma chi_exceptional_removed_differentiable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (ρ : ℝ) : Differentiable ℂ (chiExceptionalRemoved χ ρ) := by
  have hd := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hds : Differentiable ℂ (dslope (dirichletLFunction χ) (ρ:ℂ)) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 (ρ:ℂ))).mpr hd.differentiableOn
  exact hd.add hds

lemma chi_exceptional_removed_factorization {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hzero : dirichletLFunction χ (ρ:ℂ) = 0) (s : ℂ) :
    (s-(ρ:ℂ)) * chiExceptionalRemoved χ ρ s =
      (s-(ρ:ℂ)+1) * dirichletLFunction χ s := by
  have hh := sub_smul_dslope (dirichletLFunction χ) (ρ:ℂ) s
  simp only [smul_eq_mul,hzero,sub_zero] at hh
  unfold chiExceptionalRemoved
  rw [mul_add,hh]
  ring

lemma chi_exceptional_removed_quotient {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hzero : dirichletLFunction χ (ρ:ℂ) = 0) {s : ℂ} (hs : s ≠ (ρ:ℂ)) :
    chiExceptionalRemoved χ ρ s =
      dirichletLFunction χ s * (s-(ρ:ℂ)+1) / (s-(ρ:ℂ)) := by
  apply (eq_div_iff (sub_ne_zero.mpr hs)).mpr
  simpa only [mul_comm] using chi_exceptional_removed_factorization χ hzero s

lemma chi_exceptional_removed_ne_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hρ : ρ ≤ 1) (hzero : dirichletLFunction χ (ρ:ℂ) = 0)
    (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z →
      dirichletLFunction χ z = 0 → z = (ρ:ℂ))
    {s : ℂ} (hs : Lemma55InZeroRegion D s) (hspos : 0 < s.re) :
    chiExceptionalRemoved χ ρ s ≠ 0 := by
  by_cases he : s = (ρ:ℂ)
  · subst s
    simpa [chiExceptionalRemoved,hzero] using hsimple
  · rw [chi_exceptional_removed_quotient χ hzero he]
    apply div_ne_zero (mul_ne_zero (fun hz => he (hunique s hs hz)) ?_)
      (sub_ne_zero.mpr he)
    apply Complex.ne_zero_of_re_pos
    simp only [add_re,sub_re,ofReal_re,one_re]
    linarith

lemma chi_exceptional_removed_anchor_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hzero : dirichletLFunction χ (ρ:ℂ) = 0)
    {s : ℂ} (hs : ρ < s.re) :
    ‖dirichletLFunction χ s‖ ≤ ‖chiExceptionalRemoved χ ρ s‖ := by
  have hsne : s ≠ (ρ:ℂ) := by intro he; subst s; simpa using hs
  have hp : 0 < ‖s-(ρ:ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsne)
  have hnorm : ‖s-(ρ:ℂ)‖ ≤ ‖s-(ρ:ℂ)+1‖ := by
    have ha := Complex.sq_norm (s-(ρ:ℂ))
    have hb := Complex.sq_norm (s-(ρ:ℂ)+1)
    simp only [normSq_apply,add_re,sub_re,ofReal_re,one_re,add_im,sub_im,ofReal_im,one_im,sub_zero,add_zero] at ha hb
    nlinarith [norm_nonneg (s-(ρ:ℂ)),norm_nonneg (s-(ρ:ℂ)+1)]
  rw [chi_exceptional_removed_quotient χ hzero hsne,norm_div,norm_mul]
  apply (le_div_iff₀ hp).mpr
  exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

/-- A removable divided difference inherits the boundary Cauchy bound. -/
lemma chi_dslope_closed_disk_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c z : ℂ} {R M : ℝ} (hR : 0 < R) (hc : f c = 0)
    (hbound : ∀ w ∈ sphere c R, ‖f w‖ ≤ M)
    (hz : z ∈ closedBall c R) : ‖dslope f c z‖ ≤ M/R := by
  have hd : Differentiable ℂ (dslope f c) := by
    rw [←differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 c)).mpr hf.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd.diffContOnCl
  · intro w hw
    rw [frontier_ball c hR.ne'] at hw
    have hnorm : ‖w-c‖ = R := mem_sphere_iff_norm.mp hw
    have hne : w ≠ c := by intro he; subst w; simp only [sub_self,norm_zero] at hnorm; linarith
    rw [dslope_of_ne f hne,slope_def_field,hc,sub_zero,norm_div,hnorm]
    exact div_le_div_of_nonneg_right (hbound w hw) hR.le
  · rwa [closure_ball c hR.ne']

/-- Uniform logarithmic-square growth after removing the actual simple zero.
No lower bound or conclusion-shaped contour hypothesis is used. -/
theorem chi_exceptional_removed_uniform_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 8 ≤ Real.log (D : ℝ)) {ρ : ℝ}
    (hρ : 0 ≤ 1-ρ) (hclose : 1-ρ ≤ 1/Real.log (D : ℝ))
    (hzero : dirichletLFunction χ (ρ:ℂ) = 0) {s : ℂ}
    (hσ : 1-4/Real.log (D : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 4*(D:ℝ)) :
    ‖chiExceptionalRemoved χ ρ s‖ ≤ 28 * Real.exp 16 * Real.log (D : ℝ)^2 := by
  let L := Real.log (D : ℝ)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD.le
  have hi : 1/L ≤ 1 := (div_le_one hLp).mpr hL1
  have hρpos : 0 ≤ ρ := by change 1-ρ ≤ 1/L at hclose; linarith
  have hρ1 : ρ ≤ 1 := by linarith
  have hρnorm : ‖(ρ:ℂ)‖ ≤ 1 := by simpa only [norm_real,Real.norm_eq_abs,abs_of_nonneg hρpos] using hρ1
  have hcircle (z : ℂ) (hz : z ∈ sphere (ρ:ℂ) (1/L)) :
      ‖dirichletLFunction χ z‖ ≤ 14 * Real.exp 16 * L := by
    have hdist : ‖z-(ρ:ℂ)‖ = 1/L := mem_sphere_iff_norm.mp hz
    have hzre : 1-4/L ≤ z.re := by
      have hh := (abs_le.mp ((Complex.abs_re_le_norm (z-(ρ:ℂ))).trans_eq hdist)).1
      simp only [sub_re,ofReal_re] at hh
      change 1-ρ ≤ 1/L at hclose
      have hip : 0 < 1/L := by positivity
      simp only [div_eq_mul_inv,one_mul] at hh hclose hip ⊢
      linarith
    have hznorm : ‖z‖ ≤ 4*(D:ℝ) := by
      have hh := norm_add_le (z-(ρ:ℂ)) (ρ:ℂ)
      rw [sub_add_cancel,hdist] at hh
      linarith
    exact chi_actual_L_uniform_log_bound χ hD hL hzre hznorm
  have hpoint := chi_actual_L_uniform_log_bound χ hD hL hσ hnorm
  have hds : ‖dslope (dirichletLFunction χ) (ρ:ℂ) s‖ ≤ 14 * Real.exp 16 * L^2 := by
    by_cases hnear : ‖s-(ρ:ℂ)‖ ≤ 1/L
    · have hh := chi_dslope_closed_disk_bound
        (differentiable_dirichletLFunction_of_one_lt_modulus χ hD)
        (show 0 < 1/L by positivity) hzero hcircle (mem_closedBall_iff_norm.mpr hnear)
      apply hh.trans_eq
      field_simp
    · have hfar : 1/L ≤ ‖s-(ρ:ℂ)‖ := (lt_of_not_ge hnear).le
      have hp : 0 < ‖s-(ρ:ℂ)‖ := (by positivity : 0 < 1/L).trans_le hfar
      have hsne : s ≠ (ρ:ℂ) := sub_ne_zero.mp (norm_pos_iff.mp hp)
      rw [dslope_of_ne _ hsne,slope_def_field,hzero,sub_zero,norm_div]
      have hh := div_le_div_of_nonneg_left
        (show 0 ≤ 14 * Real.exp 16 * L by positivity) (by positivity : 0 < 1/L) hfar
      apply ((div_le_div_of_nonneg_right hpoint hp.le).trans hh).trans_eq
      field_simp
  have hh := (norm_add_le (dirichletLFunction χ s)
    (dslope (dirichletLFunction χ) (ρ:ℂ) s)).trans (add_le_add hpoint hds)
  apply hh.trans
  change 14 * Real.exp 16 * L + 14 * Real.exp 16 * L^2 ≤ 28 * Real.exp 16 * L^2
  have hm := mul_le_mul_of_nonneg_left (show L ≤ L^2 by nlinarith)
    (show 0 ≤ 14 * Real.exp 16 by positivity)
  linarith

end ZhangLS.Spec
