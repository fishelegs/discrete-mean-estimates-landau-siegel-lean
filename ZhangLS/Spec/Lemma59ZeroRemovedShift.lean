import ZhangLS.Spec.Lemma59ZeroRemovedLog
import ZhangLS.Spec.Lemma56LocalLogDerivativeBound
import ZhangLS.Spec.Lemma52
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Actual zero factors and zero-removed L-function bounds for Lemma 5.9

The exact actual L-function, divisor and analytic multiplicities are retained.
The full original Lemma 5.9 quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma59_actual_zero_removed_logDeriv_near_center_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : ‖z - lemma55JensenCenter t‖ ≤ (25 / 16 : ℝ)) :
    ‖logDeriv (lemma59ZeroRemovedL θ t) z‖ ≤ 83200 * lemma59JensenLogSize θ t := by
  obtain ⟨ℓ, hℓ⟩ := lemma59_actual_zero_removed_log_exists θ hθ t
  let w := z - lemma55JensenCenter t
  have hw : ‖w‖ ≤ (25 / 16 : ℝ) := hz
  have hshift {u : ℂ} (hu : u ∈ closedBall w (1 / 16 : ℝ)) :
      u ∈ closedBall (0 : ℂ) (13 / 8 : ℝ) := by
    apply mem_closedBall_iff_norm.mpr
    have hn := norm_add_le (u - w) w
    rw [sub_add_cancel] at hn
    have hd := mem_closedBall_iff_norm.mp hu
    simp only [sub_zero]
    linarith only [hn, hd, hw]
  have hclosure : closure (ball w (1 / 16 : ℝ)) ⊆ ball (0 : ℂ) (7 / 4 : ℝ) := by
    intro u hu
    have hn := mem_closedBall_iff_norm.mp (hshift (closure_ball_subset_closedBall hu))
    apply mem_ball_zero_iff.mpr
    simp only [sub_zero] at hn
    linarith only [hn]
  have hdiff : DifferentiableOn ℂ ℓ (ball (0 : ℂ) (7 / 4 : ℝ)) := fun u hu =>
    (lemma59_actual_zero_removed_log_hasDerivAt θ hθ hℓ hu).differentiableAt.differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := w) (R := (1 / 16 : ℝ)) (C := 5200 * lemma59JensenLogSize θ t) (by norm_num)
    (hdiff.mono hclosure).diffContOnCl (fun u hu =>
      lemma59_actual_zero_removed_log_closed_bound θ hθ hℓ (hshift (sphere_subset_closedBall hu)))
  have hd := (lemma59_actual_zero_removed_log_hasDerivAt θ hθ hℓ
    (mem_ball_zero_iff.mpr (by linarith only [hw] : ‖w‖ < (7 / 4 : ℝ)))).deriv
  have he : lemma55JensenCenter t + w = z := by dsimp [w]; abel
  rw [he] at hd
  rw [hd] at hc
  exact hc.trans_eq (by ring)

lemma lemma59_actual_zero_removed_shift_norm_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {s w : ℂ}
    (hpath : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖s + (x : ℂ) * w - lemma55JensenCenter t‖ ≤ (25 / 16 : ℝ)) :
    ‖lemma59ZeroRemovedL θ t (s + w) / lemma59ZeroRemovedL θ t s‖ ≤
      Real.exp (83200 * lemma59JensenLogSize θ t * ‖w‖) := by
  obtain ⟨ℓ, hℓ⟩ := lemma59_actual_zero_removed_log_exists θ hθ t
  let c := lemma55JensenCenter t
  let E : ℂ → ℂ := fun z => ℓ (s - c + z * w)
  have harg (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      s - c + (x : ℂ) * w ∈ Metric.ball (0 : ℂ) (7 / 4 : ℝ) := by
    apply mem_ball_zero_iff.mpr
    have he : s - c + (x : ℂ) * w = s + (x : ℂ) * w - c := by ring
    rw [he]
    linarith only [hpath x hx]
  have hE (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => E (x : ℂ))
        (logDeriv (lemma59ZeroRemovedL θ t) (s + (x : ℂ) * w) * w) x := by
    have ha : HasDerivAt (fun z : ℂ => s - c + z * w) w (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).mul_const w).const_add (s - c)
    have hd := (lemma59_actual_zero_removed_log_hasDerivAt θ hθ hℓ (harg x hx)).comp (x : ℂ) ha
    have he : lemma55JensenCenter t + (s - c + (x : ℂ) * w) = s + (x : ℂ) * w := by dsimp [c]; ring
    rw [he] at hd
    exact hd.comp_ofReal
  have hn (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ‖logDeriv (lemma59ZeroRemovedL θ t) (s + (x : ℂ) * w) * w‖ ≤
        (83200 * lemma59JensenLogSize θ t) * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (lemma59_actual_zero_removed_logDeriv_near_center_bound θ hθ (hpath x hx)) (norm_nonneg w)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hE x hx).hasDerivWithinAt) hn (convex_Icc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  norm_num only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, norm_one, mul_one] at hb
  have hs := harg 0 (by norm_num)
  have hsw := harg 1 (by norm_num)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hs
  simp only [Complex.ofReal_one, one_mul] at hsw
  have hc : lemma59ZeroRemovedL θ t c ≠ 0 :=
    lemma59_actual_zero_removed_ne_zero θ hθ (mem_closedBall_self (by norm_num))
  have he : Complex.exp (E 1 - E 0) =
      lemma59ZeroRemovedL θ t (s + w) / lemma59ZeroRemovedL θ t s := by
    rw [Complex.exp_sub]
    change Complex.exp (ℓ (s - c + 1 * w)) / Complex.exp (ℓ (s - c + 0 * w)) = _
    simp only [one_mul, zero_mul, add_zero]
    rw [hℓ.2.2 _ hsw, hℓ.2.2 _ hs]
    have heS : lemma55JensenCenter t + (s - c) = s := by dsimp [c]; ring
    have heW : lemma55JensenCenter t + (s - c + w) = s + w := by dsimp [c]; ring
    rw [heS, heW, div_div_div_cancel_right₀ hc]
  rw [← he, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)

lemma lemma59_original_shift_path_near_center {D : ℕ} {s : ℂ} {δ x : ℝ}
    (hL : 100 ≤ lemma23PaperL D) (hs : Lemma59InRegion D s)
    (hδ : 0 ≤ δ) (hδhi : δ ≤ lemma44PaperAlpha D) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖s + (x : ℂ) * (I * (δ : ℂ)) - lemma55JensenCenter s.im‖ ≤ (25 / 16 : ℝ) := by
  have ha := lemma59_alpha_bounds hL
  have hi : (lemma23PaperL D)⁻¹ ≤ 1 / 100 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hL
  have ha100 : lemma44PaperAlpha D ≤ 1 / 100 := ha.2.le.trans hi
  have hre : |s.re - 2| ≤ 3 / 2 + lemma44PaperAlpha D := by
    apply abs_le.mpr
    have hsr := abs_le.mp hs.1
    constructor <;> linarith only [hsr.1,hsr.2]
  have hxd0 : 0 ≤ x * δ := mul_nonneg hx.1 hδ
  have hxd : x * δ ≤ lemma44PaperAlpha D :=
    (mul_le_mul_of_nonneg_right hx.2 hδ).trans (by simpa using hδhi)
  have hn := Complex.norm_le_abs_re_add_abs_im
    (s + (x : ℂ) * (I * (δ : ℂ)) - lemma55JensenCenter s.im)
  simp only [lemma55JensenCenter, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    mul_one, sub_zero, zero_sub, add_zero, zero_add] at hn
  norm_num at hn
  rw [abs_of_nonneg hx.1, abs_of_nonneg hδ] at hn
  change ‖s + (x : ℂ) * (I * (δ : ℂ)) - (2 + (s.im : ℂ) * I)‖ ≤ (25 / 16 : ℝ)
  linarith only [hn,hre,hxd,ha100]

lemma lemma59_uniform_actual_zero_removed_first_shift :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ,
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ}, Lemma59InRegion D s →
        ‖lemma59ZeroRemovedL ψ s.im (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
          lemma59ZeroRemovedL ψ s.im s‖ ≤ C := by
  refine ⟨Real.exp (166400 * Real.pi), Real.exp_pos _, ?_⟩
  intro c hc
  obtain ⟨D₀, hsection, hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨D₀, ?_⟩
  intro D p _ χ ψ hD hψ s hs
  have hparam := lemma23_sectionFour_parameters_at_explicit_threshold (hsection.trans hD)
  have hL : 100 ≤ lemma23PaperL D := by
    have hh := Real.log_le_self (by linarith only [hparam.1] : 0 ≤ lemma23PaperL D)
    linarith only [hh,hparam.2]
  have hsm : 5 * c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2 := by
    nlinarith only [hsmall D hD]
  have hb := lemma59_paper_offset_one_bounds hL hc hsm
  have hbound := lemma59_actual_zero_removed_shift_norm_bound ψ
    (lemma59_family_character_nonprincipal ψ hψ.1)
    (fun x hx => lemma59_original_shift_path_near_center hL hs hb.1.le hb.2 hx)
  have hlog := lemma59_family_large_disk_log_budget ψ hL hψ.1
    (t := s.im) (by linarith only [hs.2])
  have hlog0 : 0 ≤ lemma59JensenLogSize ψ s.im := (lemma59_jensen_log_size_pos ψ s.im).le
  have hnorm : ‖I * (lemma23PaperOffsetOne D c : ℂ)‖ = lemma23PaperOffsetOne D c := by
    rw [norm_mul,norm_I,norm_real,Real.norm_of_nonneg hb.1.le,one_mul]
  have hmul := mul_le_mul hlog hb.2 hb.1.le
    (by positivity : 0 ≤ 2 * lemma23PaperL D ^ 9)
  have hcancel : (2 * lemma23PaperL D ^ 9) * lemma44PaperAlpha D = 2 * Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    have hp : lemma23PaperL D ^ 9 ≠ 0 := pow_ne_zero 9 (by linarith only [hL] : lemma23PaperL D ≠ 0)
    field_simp
  rw [hcancel] at hmul
  apply hbound.trans
  rw [hnorm]
  apply Real.exp_le_exp.mpr
  change 83200 * lemma59JensenLogSize ψ s.im * lemma23PaperOffsetOne D c ≤ _
  change Real.log (32 * (p : ℝ) * (4 + |s.im|)) * lemma23PaperOffsetOne D c ≤ 2 * Real.pi at hmul
  dsimp [lemma59JensenLogSize]
  nlinarith only [hmul]

lemma lemma59_actual_L_quotient_factorization {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (s w : ℂ) :
    DirichletCharacter.LFunction θ (s + w) / DirichletCharacter.LFunction θ s =
      (lemma59LocalZeroFactor θ t (s + w) / lemma59LocalZeroFactor θ t s) *
      (lemma59ZeroRemovedL θ t (s + w) / lemma59ZeroRemovedL θ t s) := by
  rw [lemma59_actual_zero_factorization θ hθ t (s + w),
    lemma59_actual_zero_factorization θ hθ t s, div_mul_div_comm]

lemma lemma59_actual_zero_factor_ratio_eq_product {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (s w : ℂ) :
    lemma59LocalZeroFactor θ t (s + w) / lemma59LocalZeroFactor θ t s =
      ∏ ρ ∈ lemma59LocalZeroFinset θ t,
        ((s + w - ρ) / (s - ρ)) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
  rw [lemma59_actual_zero_factor_eq_product θ hθ t, lemma59_actual_zero_factor_eq_product θ hθ t,
    ← Finset.prod_div_distrib]
  simp only [div_pow]

def Lemma59InZeroOmega (D : ℕ) (ρ : ℂ) : Prop :=
  |ρ.re - 1 / 2| < 1 / 2 ∧
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13

lemma lemma59_actual_local_zero_re_bounds {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma59LocalZeroFinset θ t) : (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re < 1 := by
  have hm := (lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ
  have hd := mem_closedBall_iff_norm.mp hm.1
  have hr : |ρ.re - 2| ≤ (7 / 4 : ℝ) := by
    simpa only [Complex.sub_re,lemma55_jensen_center_re] using
      (Complex.abs_re_le_norm (ρ - lemma55JensenCenter t)).trans hd
  refine ⟨by linarith only [(abs_le.mp hr).1], ?_⟩
  by_contra hn
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re θ (.inl hθ) (not_lt.mp hn)) hm.2

lemma lemma59_actual_local_zeros_in_extended_region {D r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {ρ : ℂ}
    (ht : |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10)
    (hρ : ρ ∈ lemma59LocalZeroFinset θ t) : Lemma59InZeroOmega D ρ := by
  have hr := lemma59_actual_local_zero_re_bounds θ hθ hρ
  have hm := (lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ
  have hd := mem_closedBall_iff_norm.mp hm.1
  have hi : |ρ.im - t| ≤ (7 / 4 : ℝ) := by
    simpa only [Complex.sub_im,lemma55_jensen_center_im] using
      (Complex.abs_im_le_norm (ρ - lemma55JensenCenter t)).trans hd
  constructor
  · apply abs_lt.mpr
    constructor <;> linarith only [hr.1,hr.2]
  · have hsum := abs_sub_le ρ.im t (lemma23PaperCenter D).im
    linarith only [hsum,hi,ht]

end ZhangLS.Spec
