import ZhangLS.Spec.Lemma56ActualLocalZeros
import ZhangLS.Spec.Lemma59Parameters

/-! # Actual local zeros for Lemma 5.9

Actual L-function zeros, divisors and analytic multiplicities are retained.
The full original quotient estimate is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeromorphicOn Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma59_actual_L_large_disk_bound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (15 / 8 : ℝ)) :
    ‖DirichletCharacter.LFunction θ z‖ ≤ 8 * (r : ℝ) * (4 + |t|) := by
  have hd := mem_closedBall_iff_norm.mp hz
  have hr := (Complex.abs_re_le_norm (z - lemma55JensenCenter t)).trans hd
  simp only [Complex.sub_re, lemma55JensenCenter, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im] at hr
  norm_num at hr
  have hσ : 1 / 8 ≤ z.re := by linarith only [(abs_le.mp hr).1]
  have hσp : 0 < z.re := by linarith only [hσ]
  have hzn : ‖z‖ ≤ 4 + |t| := by
    have hn := norm_add_le (z - lemma55JensenCenter t) (lemma55JensenCenter t)
    rw [sub_add_cancel] at hn
    linarith only [hn, hd, lemma55_jensen_center_norm_le t]
  have hquot : (r : ℝ) / z.re ≤ 8 * (r : ℝ) := by
    apply (div_le_iff₀ hσp).mpr
    nlinarith only [hσ, (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  calc
    _ ≤ ‖z‖ * ((r : ℝ) / z.re) := lemma56_actual_LFunction_bound_re_pos θ hθ hσp
    _ ≤ (4 + |t|) * (8 * (r : ℝ)) :=
      mul_le_mul hzn hquot (by positivity) (by positivity)
    _ = _ := by ring

noncomputable def lemma59JensenMultiplicityCount {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℤ :=
  ∑ᶠ ρ : ℂ, divisor (DirichletCharacter.LFunction θ)
    (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) ρ

lemma lemma59_actual_large_disk_multiplicity_bound {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (lemma59JensenMultiplicityCount θ t : ℝ) ≤ 15 * Real.log (32 * (r : ℝ) * (4 + |t|)) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hM : 1 ≤ 8 * (r : ℝ) * (4 + |t|) := by nlinarith only [hr1, abs_nonneg t]
  have ha := (lemma56_actual_L_analyticOnNhd θ hθ).mono
    (subset_univ (closedBall (lemma55JensenCenter t) |(15 / 8 : ℝ)|))
  have hJ := ha.sum_divisor_le (r := (7 / 4 : ℝ)) (R := (15 / 8 : ℝ))
    (M := 8 * (r : ℝ) * (4 + |t|)) (by norm_num) (by norm_num) hM
    (lemma56_actual_jensen_center_ne_zero θ t)
    (fun z hz => lemma59_actual_L_large_disk_bound θ hθ (by
      have hz' := sphere_subset_closedBall hz
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 15 / 8)] at hz'
      exact hz'))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4),
    show (15 / 8 : ℝ) / (7 / 4) = 15 / 14 by norm_num] at hJ
  have hcenter := lemma56_actual_jensen_center_lower_bound θ t
  have hcp : 0 < ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖ := by linarith only [hcenter]
  have hratio : (8 * (r : ℝ) * (4 + |t|)) /
      ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖ ≤ 32 * (r : ℝ) * (4 + |t|) := by
    apply (div_le_iff₀ hcp).mpr
    have hh := mul_le_mul_of_nonneg_left hcenter (by positivity : 0 ≤ 32 * (r : ℝ) * (4 + |t|))
    nlinarith only [hh]
  have hlog := Real.log_le_log (by positivity :
      0 < (8 * (r : ℝ) * (4 + |t|)) /
        ‖DirichletCharacter.LFunction θ (lemma55JensenCenter t)‖) hratio
  have hden : (1 : ℝ) / 15 ≤ Real.log (15 / 14 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 15 / 14)
    norm_num at h
    exact h
  have hdenp : 0 < Real.log (15 / 14 : ℝ) := by linarith only [hden]
  have hlogn : 0 ≤ Real.log (32 * (r : ℝ) * (4 + |t|)) := by
    apply Real.log_nonneg
    nlinarith only [hr1, abs_nonneg t]
  apply hJ.trans
  apply (div_le_iff₀ hdenp).mpr
  have hscale := mul_le_mul_of_nonneg_left hden hlogn
  nlinarith only [hlog, hscale]

noncomputable def lemma59LocalZeroFinset {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (t : ℝ) : Finset ℂ :=
  ((divisor (DirichletCharacter.LFunction θ)
    (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ))).finiteSupport
      (isCompact_closedBall _ _)).toFinset

theorem lemma59_actual_local_divisor_eq_order
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) :
    divisor (DirichletCharacter.LFunction θ) (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) ρ =
      (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
  have ha := (lemma56_actual_L_analyticOnNhd θ hθ).mono
    (subset_univ (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)))
  rw [ha.divisor_apply hρ, ← Nat.cast_analyticOrderNatAt
    (lemma56_actual_analytic_order_finite θ hθ ρ)]
  simp

theorem lemma59_mem_actual_local_zero_finset
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (ρ : ℂ) :
    ρ ∈ lemma59LocalZeroFinset θ t ↔
      ρ ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ) ∧ DirichletCharacter.LFunction θ ρ = 0 := by
  classical
  let d := divisor (DirichletCharacter.LFunction θ) (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ))
  have hmem : ρ ∈ lemma59LocalZeroFinset θ t ↔ ρ ∈ Function.support d := by
    simp [lemma59LocalZeroFinset, d]
  rw [hmem]
  constructor
  · intro hsupp
    have hρ : ρ ∈ closedBall (lemma55JensenCenter t) (7 / 4 : ℝ) :=
      d.supportWithinDomain hsupp
    have hNZ : analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ ≠ 0 := by
      intro hzero
      have hd := lemma59_actual_local_divisor_eq_order θ hθ hρ
      rw [hzero, Nat.cast_zero] at hd
      exact hsupp hd
    exact ⟨hρ, apply_eq_zero_of_analyticOrderNatAt_ne_zero hNZ⟩
  · rintro ⟨hρ, hzero⟩
    change d ρ ≠ 0
    dsimp [d]
    rw [lemma59_actual_local_divisor_eq_order θ hθ hρ]
    have hNZ : analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ ≠ 0 := by
      intro hnat
      have ho : analyticOrderAt (DirichletCharacter.LFunction θ) ρ = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (lemma56_actual_analytic_order_finite θ hθ ρ), hnat]
        rfl
      have haρ := lemma56_actual_L_analyticOnNhd θ hθ ρ (mem_univ ρ)
      exact (haρ.analyticOrderAt_eq_zero.mp ho) hzero
    exact_mod_cast hNZ

theorem lemma59_actual_local_zero_order_pos
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma59LocalZeroFinset θ t) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ := by
  have hzero := (lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ
  apply Nat.one_le_iff_ne_zero.mpr
  intro hnat
  have ho : analyticOrderAt (DirichletCharacter.LFunction θ) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (lemma56_actual_analytic_order_finite θ hθ ρ), hnat]
    rfl
  have haρ := lemma56_actual_L_analyticOnNhd θ hθ ρ (mem_univ ρ)
  exact (haρ.analyticOrderAt_eq_zero.mp ho) hzero.2

theorem lemma59_actual_multiplicity_count_eq_sum_orders
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    lemma59JensenMultiplicityCount θ t =
      ∑ ρ ∈ lemma59LocalZeroFinset θ t, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
  classical
  let d := divisor (DirichletCharacter.LFunction θ) (closedBall (lemma55JensenCenter t) (7 / 4 : ℝ))
  have heq : lemma59JensenMultiplicityCount θ t = ∑ ρ ∈ lemma59LocalZeroFinset θ t, d ρ := by
    exact finsum_eq_sum d (d.finiteSupport (isCompact_closedBall _ _))
  rw [heq]
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact lemma59_actual_local_divisor_eq_order θ hθ
    ((lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).1

theorem lemma59_actual_local_zero_card_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    ((lemma59LocalZeroFinset θ t).card : ℝ) ≤
      15 * Real.log (32 * (r : ℝ) * (4 + |t|)) := by
  have hsum : ∑ ρ ∈ lemma59LocalZeroFinset θ t, (1 : ℤ) ≤
      ∑ ρ ∈ lemma59LocalZeroFinset θ t, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    exact_mod_cast lemma59_actual_local_zero_order_pos θ hθ hρ
  rw [← lemma59_actual_multiplicity_count_eq_sum_orders θ hθ t] at hsum
  have hcard : ((lemma59LocalZeroFinset θ t).card : ℝ) ≤
      (lemma59JensenMultiplicityCount θ t : ℝ) := by
    have hi : ((lemma59LocalZeroFinset θ t).card : ℤ) ≤ lemma59JensenMultiplicityCount θ t := by
      simpa using hsum
    exact_mod_cast hi
  exact hcard.trans (lemma59_actual_large_disk_multiplicity_bound θ hθ t)

end ZhangLS.Spec
