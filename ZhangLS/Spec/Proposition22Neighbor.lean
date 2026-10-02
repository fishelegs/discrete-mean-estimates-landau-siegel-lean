import ZhangLS.Spec.Proposition22ModelNearZero

/-! # A genuine zero near the expected upper neighbor

Rouché is applied on a radius `k α² L` disk about `ρ+iα`. The full
radius-`2α` estimate is centered at the original zero `ρ`, so this argument
does not assume that the nearby zero already lies in Ω.
-/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

theorem proposition22_exists_zero_of_count_one {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hcount :
      (∑ a ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
        (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
        (((MeromorphicOn.divisor f (closedBall 0 R)) a).toNat : ℂ)) = 1) :
    ∃ z ∈ closedBall (0 : ℂ) R, f z = 0 := by
  classical
  by_contra h
  push Not at h
  have hd : ∀ z : ℂ, (MeromorphicOn.divisor f (closedBall 0 R)) z = 0 := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz,
        (hf z hz).analyticOrderAt_eq_zero.mpr (h z hz)]
      simp
    · simp [hz]
  simp only [hd, Int.toNat_zero, Nat.cast_zero, Finset.sum_const_zero] at hcount
  exact zero_ne_one hcount

theorem proposition22_actual_upper_neighbor {m k : ℝ}
    (hk : 0 < k) (hcmp : lemma47ModelErrorConstant < m * k)
    (hmodel : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      m * ‖z‖ ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : k * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    ∃ v : ℂ, ‖v‖ ≤ k * lemma44PaperAlpha D ^ 2 * lemma23PaperL D ∧
      lemma45ActualA χ ψ (ρ + I * (lemma44PaperAlpha D : ℂ) + v) = 0 := by
  let a := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let M := Real.log (lemma23PaperP D)
  let R := k * a ^ 2 * L
  let f := fun v : ℂ => lemma45ActualA χ ψ (ρ + I * (a : ℂ) + v)
  have ha : 0 < a := (lemma46_alpha_parameters hD).1
  have hL : 0 < L := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hM : 0 < M := by simp only [M, lemma23PaperP, Real.log_exp]; positivity
  have haM : a * M = Real.pi := by
    dsimp [a, M, lemma44PaperAlpha]
    exact div_mul_cancel₀ _ hM.ne'
  have hRp : 0 < R := by dsimp [R]; positivity
  have hRhi : R ≤ a / 2 := by
    have hh := mul_le_mul_of_nonneg_left hsmall ha.le
    change a * (k * a * L) ≤ a * (1 / 2) at hh
    dsimp [R]
    nlinarith only [hh]
  have hRsmall : R < a := by linarith
  have hshift (v : ℂ) (hv : ‖v‖ ≤ R) : ‖I * (a : ℂ) + v‖ ≤ (3 / 2) * a := by
    have hn : ‖I * (a : ℂ)‖ = a := by
      rw [norm_mul, norm_I, norm_real, Real.norm_of_nonneg ha.le, one_mul]
    have ht := norm_add_le (I * (a : ℂ)) v
    rw [hn] at ht
    linarith
  have hfa : AnalyticOnNhd ℂ f (closedBall 0 R) := by
    have houter := lemma47_actual_A_analyticOn_outer_disk χ ψ hD hψ hre him
      (R := (7 / 4) * a) (by linarith)
    intro v hv
    have hvn : ‖v‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hv
    have hw : I * (a : ℂ) + v ∈ closedBall (0 : ℂ) ((7 / 4) * a) := by
      rw [mem_closedBall, dist_zero_right]
      linarith [hshift v hvn]
    simpa only [f, add_assoc] using (houter _ hw).comp
      (show AnalyticAt ℂ (fun v : ℂ => I * (a : ℂ) + v) v by fun_prop)
  have hclose : ∀ v ∈ sphere (0 : ℂ) R,
      ‖f v - lemma23ExponentialGapModel M v‖ < ‖lemma23ExponentialGapModel M v‖ := by
    intro v hv
    have hvn : ‖v‖ = R := by simpa [mem_sphere, dist_zero_right] using hv
    have hw : ‖I * (a : ℂ) + v‖ < 2 * a := by linarith [hshift v hvn.le]
    have herr := lemma47_actual_model_approximation χ ψ hD hψ hre him hzero hw
    have hperiod : lemma23ExponentialGapModel M (I * (a : ℂ) + v) =
        lemma23ExponentialGapModel M v := by
      simpa only [a, lemma44PaperAlpha, M] using proposition22_model_upper_shift hM v
    change ‖lemma45ActualA χ ψ (ρ + (I * (a : ℂ) + v)) -
      lemma23ExponentialGapModel M (I * (a : ℂ) + v)‖ ≤ lemma47ModelErrorConstant * a * L at herr
    rw [hperiod] at herr
    have herr' : ‖f v - lemma23ExponentialGapModel M v‖ ≤ lemma47ModelErrorConstant * a * L := by
      simpa only [f, add_assoc] using herr
    let u := v / (a : ℂ)
    have hun : ‖u‖ = k * a * L := by
      rw [norm_div, norm_real, Real.norm_of_nonneg ha.le, hvn]
      dsimp [R]
      field_simp [ha.ne']
    have hmodelEq : lemma23ExponentialGapModel M v = lemma23ExponentialGapModel Real.pi u := by
      unfold lemma23ExponentialGapModel
      congr 2
      dsimp [u]
      rw [← haM]
      push_cast
      field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne']
    have hb := hmodel u (by rw [hun]; exact hsmall)
    rw [hun, ← hmodelEq] at hb
    apply herr'.trans_lt
    have ht := mul_lt_mul_of_pos_right hcmp (mul_pos ha hL)
    nlinarith only [ht, hb]
  have hcount := lemma23_rouche_model_divisor_sum_eq_one hM hRp
    (by simpa only [a, lemma44PaperAlpha] using hRsmall) f hfa hclose
  obtain ⟨v, hv, hz⟩ := proposition22_exists_zero_of_count_one hfa hcount
  exact ⟨v, by simpa only [mem_closedBall, dist_zero_right, R, a, L] using hv, hz⟩

end ZhangLS.Spec
