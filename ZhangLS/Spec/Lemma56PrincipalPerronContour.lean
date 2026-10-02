import ZhangLS.Spec.Lemma56PrincipalPerronArithmetic

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_principal_perron_rectangle_boundary {x a H : ℝ}
    (hx : 0 < x) (ha0 : 0 < a) (ha1 : a < 1) (hH : 0 < H) (B : ℝ)
    (hfree : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 → |s.im| ≤ H → zetaPoleRemoved s ≠ 0) :
    lemma44GeneralRectangleBoundaryIntegral (lemma56PrincipalPerronArithmeticIntegrand B x) a 2 H =
      2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  let P : ℂ → ℂ := fun s => lemma56PerronComplexKernel B x s / (s - 1)
  let G := lemma56PrincipalPerronRegularIntegrand B x
  have ha2 : a ≤ 2 := by linarith only [ha1]
  have hG : DifferentiableOn ℂ G (lemma44ClosedRectangle a 2 H) := by
    intro s hs
    have hre : 0 < s.re := ha0.trans_le hs.1.1
    exact (lemma56_actual_principal_regular_perron_analytic hx B hre
      (hfree s hs.1.1 hs.1.2 (abs_le.mpr hs.2))).differentiableAt.differentiableWithinAt
  have hc := lemma44_local_rectangle_cauchy G ha2 hH.le hG
  have hPc : ContinuousOn P (Lemma56PerronPuncturedRectangle a H) := by
    intro s hs
    have hre : 0 < s.re := ha0.trans_le hs.1.1.1
    have hn : s ≠ 0 := by intro he; simp [he] at hre
    have hn1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by simpa only [mem_singleton_iff] using hs.2)
    exact ((lemma56_perron_complex_kernel_analytic hx B hn).div
      (analyticAt_id.sub analyticAt_const) hn1).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Lemma56PerronPuncturedRectangle a H) :=
    hG.continuousOn.mono (fun _ hs => hs.1)
  have heq : ∀ s ∈ Lemma56PerronPuncturedRectangle a H,
      lemma56PrincipalPerronArithmeticIntegrand B x s = P s + G s := by
    intro s hs
    exact lemma56_actual_principal_perron_pole_split B x (ha0.trans_le hs.1.1.1)
      (by simpa only [mem_singleton_iff] using hs.2)
      (hfree s hs.1.1.1 hs.1.1.2 (abs_le.mpr hs.1.2))
  rw [lemma56_perron_rectangle_boundary_congr ha1 hH _ _ heq,
    lemma56_perron_rectangle_boundary_add P G
      (lemma56_perron_rectangle_edges_integrable ha1 hH P hPc)
      (lemma56_perron_rectangle_edges_integrable ha1 hH G hGc), hc, add_zero]
  exact lemma56_actual_perron_pole_rectangle hx ha0 ha1 hH B

lemma lemma56_actual_principal_perron_rectangle_shift {x a H : ℝ}
    (hx : 0 < x) (ha0 : 0 < a) (ha1 : a < 1) (hH : 0 < H) (B : ℝ)
    (hfree : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 → |s.im| ≤ H → zetaPoleRemoved s ≠ 0) :
    I * (∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      I * (∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x ((a : ℂ) + (t : ℂ) * I)) +
        (∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) + (H : ℂ) * I)) -
          (∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) - (H : ℂ) * I)) +
            2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  have hb := lemma56_actual_principal_perron_rectangle_boundary hx ha0 ha1 hH B hfree
  unfold lemma44GeneralRectangleBoundaryIntegral at hb
  linear_combination hb

theorem lemma56_uniform_principal_perron_rectangle_shift :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ {x H : ℝ}, 0 < x → 0 < H → H ≤ D → ∀ B : ℝ,
        let a := 1 - 1 / Real.log (D : ℝ)
        I * (∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
          I * (∫ t : ℝ in -H..H, lemma56PrincipalPerronArithmeticIntegrand B x ((a : ℂ) + (t : ℂ) * I)) +
            (∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) + (H : ℂ) * I)) -
              (∫ σ : ℝ in a..2, lemma56PrincipalPerronArithmeticIntegrand B x ((σ : ℂ) - (H : ℂ) * I)) +
                2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_pole_removed_zero_exclusion
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max Dz Dr, ?_⟩
  intro D χ hDN hD hA x H hx hH hHD B
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hp : 0 < 1 / Real.log (D : ℝ) := by positivity
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  apply lemma56_actual_principal_perron_rectangle_shift hx
    (by linarith only [hinv]) (by linarith only [hp]) hH B
  intro s hre _hre2 ht
  apply hz χ ((le_max_left _ _).trans hDN) hD hA
  · rw [show 2 / Real.log (D : ℝ) = 2 * (1 / Real.log (D : ℝ)) by ring]
    linarith only [hre, hp]
  · linarith only [ht, hHD, hD2]

end ZhangLS.Spec
