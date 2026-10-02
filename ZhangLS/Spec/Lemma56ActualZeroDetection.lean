import ZhangLS.Spec.Lemma56WeightedPowerError

/-! # Actual local Fejer detection and near-one zero geometry

Actual Dirichlet L-functions and their actual analytic orders are retained.
These auxiliary results do not assert the complete Lemma 5.6 prime-window estimate.
-/

namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

theorem lemma56_actual_zero_re_lt_one
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction θ ρ = 0) : ρ.re < 1 := by
  by_contra hnot
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re θ (.inl hθ) (le_of_not_gt hnot)) hρ

theorem lemma56_actual_local_zero_center_distance
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma56LocalZeroFinset θ t) :
    1 < ‖lemma55JensenCenter t - ρ‖ := by
  have hr := lemma56_actual_zero_re_lt_one θ hθ
    ((lemma56_mem_actual_local_zero_finset θ hθ t ρ).mp hρ).2
  have hn := re_le_norm (lemma55JensenCenter t - ρ)
  rw [sub_re, lemma55_jensen_center_re] at hn
  linarith only [hr, hn]

theorem lemma56_actual_inverse_square_norm_bounds
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ lemma56LocalZeroFinset θ t) :
    0 < ‖lemma55ZeroInverseSquare t ρ‖ ∧ ‖lemma55ZeroInverseSquare t ρ‖ < 1 := by
  have hd := lemma56_actual_local_zero_center_distance θ hθ hρ
  have hdpos : 0 < ‖lemma55JensenCenter t - ρ‖ := by linarith only [hd]
  have hi : 0 < ‖lemma55JensenCenter t - ρ‖⁻¹ := inv_pos.mpr hdpos
  have hi1 : ‖lemma55JensenCenter t - ρ‖⁻¹ < 1 :=
    (inv_lt_one₀ hdpos).mpr hd
  unfold lemma55ZeroInverseSquare
  rw [norm_pow, norm_inv]
  exact ⟨by positivity, by nlinarith only [hi, hi1]⟩

theorem lemma56_actual_subset_max_inverse_square
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (t : ℝ) (S : Finset ℂ)
    (hS : S ⊆ lemma56LocalZeroFinset θ t) (hne : S.Nonempty) :
    ∃ ρ₀ ∈ S, 0 < ‖lemma55ZeroInverseSquare t ρ₀‖ ∧
      ‖lemma55ZeroInverseSquare t ρ₀‖ < 1 ∧
      ∀ ρ ∈ S, ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖ := by
  obtain ⟨ρ₀, hρ₀, hmax⟩ := S.exists_max_image (fun ρ => ‖lemma55ZeroInverseSquare t ρ‖) hne
  have hb := lemma56_actual_inverse_square_norm_bounds θ hθ (hS hρ₀)
  exact ⟨ρ₀, hρ₀, hb.1, hb.2, hmax⟩

noncomputable def lemma56SubsetZeroPowerSum {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (t : ℝ) (S : Finset ℂ) (k : ℕ) : ℂ :=
  ∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) /
    (lemma55JensenCenter t - ρ) ^ k

lemma lemma56_normalized_inverse_square_power_sum {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (t : ℝ) (S : Finset ℂ) (r : ℝ) (k : ℕ) :
    (∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ) *
      ((lemma55ZeroInverseSquare t ρ / (r : ℂ)) ^ k).re) =
        (lemma56SubsetZeroPowerSum θ t S (2 * k) / (r : ℂ) ^ k).re := by
  unfold lemma56SubsetZeroPowerSum lemma55ZeroInverseSquare
  rw [sum_div, Complex.re_sum]
  apply sum_congr rfl
  intro ρ _
  rw [div_pow, ← pow_mul, inv_pow]
  have he : ((analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) /
      (lemma55JensenCenter t - ρ) ^ (2 * k)) / (r : ℂ) ^ k =
        (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) *
          (((lemma55JensenCenter t - ρ) ^ (2 * k))⁻¹ / (r : ℂ) ^ k) := by ring
  rw [he]
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]

theorem lemma56_actual_subset_weighted_power_detection
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) (t : ℝ) (S : Finset ℂ)
    (hS : S ⊆ lemma56LocalZeroFinset θ t) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ S)
    (hmax : ∀ ρ ∈ S, ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖)
    (J : ℕ) :
    (J : ℝ) / 4 - ∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ) ≤
      ∑ j ∈ range J,
        lemma55FejerDetectionWeight
          (lemma55ZeroInverseSquare t ρ₀ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))⁻¹ J j *
          (lemma56SubsetZeroPowerSum θ t S (2 * (j + 1)) /
            (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ) ^ (j + 1)).re := by
  have hr := (lemma56_actual_inverse_square_norm_bounds θ hθ (hS hρ₀)).1
  have hm : 1 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ₀ : ℝ) := by
    exact_mod_cast lemma56_actual_local_zero_order_pos θ hθ (hS hρ₀)
  have h := lemma55_fejer_finite_weighted_power_detection S
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ))
    (fun ρ => lemma55ZeroInverseSquare t ρ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))
    hρ₀ (fun _ _ => Nat.cast_nonneg _) hm
    (fun ρ hρ => lemma55_normalized_inverse_square_le_one t ρ ρ₀ hr (hmax ρ hρ))
    (lemma55_normalized_inverse_square_unit t ρ₀ hr) J
  simpa only [lemma56_normalized_inverse_square_power_sum] using h

theorem lemma56_actual_subset_weighted_detection_log_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t : ℝ} (S : Finset ℂ)
    (hS : S ⊆ lemma56LocalZeroFinset θ t) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ S)
    (hmax : ∀ ρ ∈ S, ‖lemma55ZeroInverseSquare t ρ‖ ≤ ‖lemma55ZeroInverseSquare t ρ₀‖)
    (J : ℕ) :
    (J : ℝ) / 4 - 6 * lemma56JensenLogSize θ t ≤
      ∑ j ∈ range J,
        lemma55FejerDetectionWeight
          (lemma55ZeroInverseSquare t ρ₀ / (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ))⁻¹ J j *
          (lemma56SubsetZeroPowerSum θ t S (2 * (j + 1)) /
            (‖lemma55ZeroInverseSquare t ρ₀‖ : ℂ) ^ (j + 1)).re := by
  have hN : ∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ) ≤
      6 * lemma56JensenLogSize θ t := by
    calc
      _ ≤ ∑ ρ ∈ lemma56LocalZeroFinset θ t,
          (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.cast_nonneg _)
      _ = (lemma56LocalMultiplicity θ t : ℝ) := by simp [lemma56LocalMultiplicity]
      _ ≤ _ := lemma56_actual_local_multiplicity_bound θ hθ t
  have hd := lemma56_actual_subset_weighted_power_detection θ hθ t S hS hρ₀ hmax J
  linarith only [hN, hd]

theorem lemma56_near_one_zero_in_own_local_disk
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) {ρ : ℂ}
    {ε : ℝ} (hε : ε ≤ 1 / 4) (hre : 1 - ε < ρ.re)
    (hzero : DirichletCharacter.LFunction θ ρ = 0) :
    ρ ∈ lemma56LocalZeroFinset θ ρ.im := by
  have hr := lemma56_actual_zero_re_lt_one θ hθ hzero
  apply (lemma56_mem_actual_local_zero_finset θ hθ ρ.im ρ).mpr
  refine ⟨?_, hzero⟩
  rw [mem_closedBall_iff_norm, norm_sub_rev, lemma55_jensen_center_at_zero_height,
    norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < 2 - ρ.re)]
  linarith only [hre, hε]

theorem lemma56_near_one_zero_inverse_square_lower_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1) {ρ : ℂ}
    {ε : ℝ} (hε : 0 ≤ ε) (hre : 1 - ε < ρ.re)
    (hzero : DirichletCharacter.LFunction θ ρ = 0) :
    ((1 + ε)⁻¹) ^ 2 ≤ ‖lemma55ZeroInverseSquare ρ.im ρ‖ := by
  have hr := lemma56_actual_zero_re_lt_one θ hθ hzero
  have hd : 0 < 2 - ρ.re := by linarith only [hr]
  have ha : 2 - ρ.re ≤ 1 + ε := by linarith only [hre]
  have hi : (1 + ε)⁻¹ ≤ (2 - ρ.re)⁻¹ :=
    (inv_le_inv₀ (by positivity : 0 < 1 + ε) hd).mpr ha
  unfold lemma55ZeroInverseSquare
  rw [norm_pow, norm_inv, lemma55_jensen_center_at_zero_height,
    norm_real, Real.norm_eq_abs, abs_of_pos hd]
  exact pow_le_pow_left₀ (by positivity) hi 2

end ZhangLS.Spec
