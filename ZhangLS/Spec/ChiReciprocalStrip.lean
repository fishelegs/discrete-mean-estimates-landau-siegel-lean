import ZhangLS.Spec.ChiEulerAnchor
import ZhangLS.Spec.ChiBorelReciprocal
import ZhangLS.Spec.ChiExceptionalRemoval

namespace ZhangLS.Spec
open Complex Metric Set
open scoped Real
set_option maxHeartbeats 1500000

noncomputable def chiReciprocalConstant : ℝ := 2 * (56 * Real.exp 16)^8

lemma chi_reciprocal_constant_pos : 0 < chiReciprocalConstant := by
  unfold chiReciprocalConstant
  positivity

lemma chi_exceptional_removed_inverse_right_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    {ρ : ℝ} (hzero : dirichletLFunction χ (ρ:ℂ) = 0)
    {s : ℂ} (hs : 1 < s.re) (hρs : ρ < s.re) :
    ‖(chiExceptionalRemoved χ ρ s)⁻¹‖ ≤ 1+(s.re-1)⁻¹ := by
  have hne : dirichletLFunction χ s ≠ 0 := by
    rw [dirichletLFunction_eq_series χ hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ.chi hs
  have hp := norm_pos_iff.mpr hne
  have hh := one_div_le_one_div_of_le hp (chi_exceptional_removed_anchor_norm χ hzero hρs)
  simp only [one_div,←norm_inv] at hh
  exact hh.trans (chi_actual_L_inverse_right_bound χ hs)

/-- Geometry of the right-anchored five-halves reciprocal disk. -/
lemma chi_reciprocal_disk_geometry {D : ℕ} (hD : 1 < D)
    (hL : 8 ≤ Real.log (D:ℝ)) {t : ℝ} (ht : |t| ≤ D) {z : ℂ}
    (hz : z ∈ ball (((1+1/Real.log (D:ℝ):ℝ):ℂ)+(t:ℂ)*I)
      ((5/2:ℝ)*(1/Real.log (D:ℝ)))) :
    Lemma55InZeroRegion D z ∧
      1-4/Real.log (D:ℝ) ≤ z.re ∧ ‖z‖ ≤ 4*(D:ℝ) ∧ 0 < z.re := by
  let d := 1/Real.log (D:ℝ)
  let c : ℂ := ((1+d:ℝ):ℂ)+(t:ℂ)*I
  have hDp : (2:ℝ) ≤ D := by exact_mod_cast hD
  have hLp : 0 < Real.log (D:ℝ) := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hd8 : d ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) hL
  have hzdist : ‖z-c‖ < (5/2)*d := mem_ball_iff_norm.mp hz
  have hcRe : c.re = 1+d := by simp [c]
  have hcIm : c.im = t := by simp [c]
  have hre := (Complex.abs_re_le_norm (z-c)).trans_lt hzdist
  have him := (Complex.abs_im_le_norm (z-c)).trans_lt hzdist
  rw [Complex.sub_re,hcRe] at hre
  rw [Complex.sub_im,hcIm] at him
  have hzr : 1-2*d < z.re := by have := (abs_lt.mp hre).1; linarith
  have hzpos : 0 < z.re := by linarith
  have hzim : |z.im| < 2*(D:ℝ) := by
    have hh := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hh
    linarith
  have hzNorm : ‖z‖ ≤ 4*(D:ℝ) := by
    have hnc : ‖c‖ ≤ 1+d+|t| := by
      have hh := Complex.norm_le_abs_re_add_abs_im c
      rw [hcRe,hcIm,abs_of_pos (by linarith : 0 < 1+d)] at hh
      exact hh
    have hh := norm_add_le (z-c) c
    rw [sub_add_cancel] at hh
    linarith
  have he2 : 2/Real.log (D:ℝ)=2*d := by dsimp [d]; ring
  have he4 : 4/Real.log (D:ℝ)=4*d := by dsimp [d]; ring
  exact ⟨⟨by simpa [he2] using hzr,hzim⟩,by rw [he4]; linarith,hzNorm,hzpos⟩

/-- Polynomial reciprocal bound on the entire narrow strip, with the exact
exceptional-zero distance loss retained. Its zero data will be discharged by actual 5.5. -/
theorem chi_actual_inverse_strip_from_zero_data {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 8 ≤ Real.log (D:ℝ)) {ρ : ℝ}
    (hρ : 0 ≤ 1-ρ) (hclose : 1-ρ ≤ 1/Real.log (D:ℝ))
    (hzero : dirichletLFunction χ (ρ:ℂ) = 0)
    (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z →
      dirichletLFunction χ z = 0 → z = (ρ:ℂ))
    {s : ℂ} (hslo : 1-1/Real.log (D:ℝ) ≤ s.re)
    (hshi : s.re ≤ 1+1/Real.log (D:ℝ)) (ht : |s.im| ≤ D) :
    ‖(dirichletLFunction χ s)⁻¹‖ ≤ chiReciprocalConstant * Real.log (D:ℝ)^25 *
      (1+‖s-(ρ:ℂ)‖⁻¹) := by
  let L := Real.log (D:ℝ)
  let d := 1/L
  let c : ℂ := ((1+d:ℝ):ℂ)+(s.im:ℂ)*I
  let R : ℝ := (5/2)*d
  let H : ℝ := 56*Real.exp 16*L^3
  have hLp : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hρ1 : ρ ≤ 1 := by linarith
  have hcRe : c.re = 1+d := by simp [c]
  have hcRight : 1 < c.re := by rw [hcRe]; linarith
  have hcρ : ρ < c.re := by rw [hcRe]; linarith
  have hanchor : ‖(chiExceptionalRemoved χ ρ c)⁻¹‖ ≤ 2*L := by
    have hh := chi_exceptional_removed_inverse_right_bound χ hzero hcRight hcρ
    rw [hcRe,add_sub_cancel_left] at hh
    have he : d⁻¹ = L := by simp [d]
    rw [he] at hh
    linarith
  have hH : 1 < H := by
    have he : 1 ≤ Real.exp 16 := Real.one_le_exp_iff.mpr (by norm_num)
    have hpow : 1 ≤ L^3 := one_le_pow₀ hL1
    have hh := mul_le_mul he hpow (by norm_num : (0:ℝ) ≤ 1) (Real.exp_pos 16).le
    dsimp [H]
    nlinarith
  have hgeom (z : ℂ) (hz : z ∈ ball c R) := chi_reciprocal_disk_geometry hD hL ht hz
  have hnonzero : ∀ z ∈ ball c R, chiExceptionalRemoved χ ρ z ≠ 0 := by
    intro z hz
    exact chi_exceptional_removed_ne_zero χ hρ1 hzero hsimple hunique (hgeom z hz).1 (hgeom z hz).2.2.2
  have hbound : ∀ z ∈ ball c R, ‖chiExceptionalRemoved χ ρ z / chiExceptionalRemoved χ ρ c‖ ≤ H := by
    intro z hz
    have hb := chi_exceptional_removed_uniform_bound χ hD hL hρ hclose hzero
      (hgeom z hz).2.1 (hgeom z hz).2.2.1
    rw [norm_div,div_eq_mul_inv,←norm_inv]
    apply (mul_le_mul hb hanchor (norm_nonneg _) (by positivity)).trans_eq
    dsimp [H,L]
    ring
  have hdist : ‖s-c‖ ≤ 4*R/5 := by
    have he : s-c = ((s.re-(1+d):ℝ):ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [he,norm_real,Real.norm_eq_abs]
    apply abs_le.mpr
    change -(4*((5/2)*d)/5) ≤ s.re-(1+d) ∧ s.re-(1+d) ≤ 4*((5/2)*d)/5
    change 1-d ≤ s.re at hslo
    change s.re ≤ 1+d at hshi
    constructor <;> linarith
  have hG := chi_inverse_bound_on_disk hR hH
    (fun z _ => chi_exceptional_removed_differentiable χ hD ρ z) hnonzero hbound hdist
  have hG' : ‖(chiExceptionalRemoved χ ρ s)⁻¹‖ ≤ chiReciprocalConstant*L^25 := by
    apply (hG.trans (mul_le_mul_of_nonneg_right hanchor (by positivity : 0 ≤ H^8))).trans_eq
    dsimp [H,chiReciprocalConstant]
    ring
  by_cases hsρ : s = (ρ:ℂ)
  · rw [hsρ,hzero,inv_zero,norm_zero]
    exact mul_nonneg (mul_nonneg chi_reciprocal_constant_pos.le (by positivity)) (by positivity)
  · have hfact : (dirichletLFunction χ s)⁻¹ =
        (chiExceptionalRemoved χ ρ s)⁻¹ * (s-(ρ:ℂ)+1)/(s-(ρ:ℂ)) := by
      rw [chi_exceptional_removed_quotient χ hzero hsρ,inv_div]
      have hp : s-(ρ:ℂ)+1 ≠ 0 := by
        apply Complex.ne_zero_of_re_pos
        simp only [add_re,sub_re,ofReal_re,one_re]
        have hd1 : d ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) hL
        change 1-d ≤ s.re at hslo
        linarith
      have hfs : dirichletLFunction χ s ≠ 0 := by
        intro he
        apply hsρ
        apply hunique s (hgeom s (mem_ball_iff_norm.mpr (by linarith))).1 he
      field_simp [hp,sub_ne_zero.mpr hsρ,hfs]
    have hratio : ‖s-(ρ:ℂ)+1‖ / ‖s-(ρ:ℂ)‖ ≤ 1+‖s-(ρ:ℂ)‖⁻¹ := by
      have hp : 0 < ‖s-(ρ:ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
      apply (div_le_iff₀ hp).mpr
      have hh := norm_add_le (s-(ρ:ℂ)) (1:ℂ)
      rw [norm_one] at hh
      simpa only [add_mul,one_mul,inv_mul_cancel₀ hp.ne'] using hh
    rw [hfact,norm_div,norm_mul,mul_div_assoc]
    exact mul_le_mul hG' hratio (by positivity)
      (mul_nonneg chi_reciprocal_constant_pos.le (pow_nonneg hLp.le _))

end ZhangLS.Spec
