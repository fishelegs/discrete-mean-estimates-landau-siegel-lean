import ZhangLS.Spec.Lemma57CriticalStripGrowth

/-!
# Uniform vertical-strip bounds for completed Mellin transforms

The completed zeta and Dirichlet L-functions in mathlib are built from weak
functional-equation pairs.  Their pole-corrected completed functions are
Mellin transforms of rapidly decreasing modified kernels.  This module proves
the general analytic fact that such a completed Mellin transform is uniformly
bounded when its real part ranges over a compact interval.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Real Topology

set_option maxHeartbeats 800000 in
/-- The entire completed Mellin transform attached to any weak functional-
equation pair is uniformly bounded on every closed vertical strip. -/
theorem WeakFEPair.exists_norm_Λ₀_le_on_verticalStrip
    (P : WeakFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖P.Λ₀ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  let g : ℝ → ℂ := P.f_modif
  let majorant : ℝ → ℝ := fun x =>
    (x ^ (a - 1) + x ^ (b - 1)) * ‖g x‖
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    P.toStrongFEPair.hf_int.aestronglyMeasurable
  have haConv : MellinConvergent g (a : ℂ) :=
    (P.toStrongFEPair.hasMellin (a : ℂ)).1
  have hbConv : MellinConvergent g (b : ℂ) :=
    (P.toStrongFEPair.hasMellin (b : ℂ)).1
  have haInt : IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖g x‖) (Ioi 0) :=
    (mellin_convergent_iff_norm subset_rfl measurableSet_Ioi hgmeas).mp haConv
  have hbInt : IntegrableOn (fun x : ℝ => x ^ (b - 1) * ‖g x‖) (Ioi 0) :=
    (mellin_convergent_iff_norm subset_rfl measurableSet_Ioi hgmeas).mp hbConv
  have hmajorant : IntegrableOn majorant (Ioi 0) := by
    dsimp [majorant]
    simpa only [add_mul] using haInt.add hbInt
  refine ⟨∫ x : ℝ in Ioi 0, majorant x, ?_, ?_⟩
  · apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg hx.le _)
      (Real.rpow_nonneg hx.le _)) (norm_nonneg _)
  · intro σ t hσa hσb
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hsConv : MellinConvergent g s :=
      (P.toStrongFEPair.hasMellin s).1
    have hsInt : IntegrableOn
        (fun x : ℝ => ‖(x : ℂ) ^ (s - 1) • g x‖) (Ioi 0) :=
      hsConv.norm
    change ‖mellin g s‖ ≤ ∫ x : ℝ in Ioi 0, majorant x
    rw [mellin]
    calc
      ‖∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) • g x‖ ≤
          ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) • g x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ in Ioi 0, majorant x := by
        apply MeasureTheory.integral_mono_ae hsInt hmajorant
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (s - 1).re = σ - 1 := by simp [s]
        rw [hre]
        dsimp [majorant]
        have hpow : x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
          rcases le_total x 1 with hx1 | h1x
          · exact (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)).trans
              (le_add_of_nonneg_right (Real.rpow_nonneg hx0.le _))
          · exact (Real.rpow_le_rpow_of_exponent_le h1x (by linarith)).trans
              (le_add_of_nonneg_left (Real.rpow_nonneg hx0.le _))
        exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

/-- The pole-corrected completed Riemann zeta function is uniformly bounded
on the strip needed for Zhang's contour. -/
theorem exists_completedRiemannZeta₀_norm_le_criticalStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖completedRiemannZeta₀ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  rcases WeakFEPair.exists_norm_Λ₀_le_on_verticalStrip
      (HurwitzZeta.hurwitzEvenFEPair 0)
      ((1 : ℝ) / 4) ((3 : ℝ) / 4) with ⟨C, hC, hbound⟩
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ t hσ0 hσ1
  have h := hbound (σ / 2) (t / 2) (by linarith) (by linarith)
  rw [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀]
  change ‖(HurwitzZeta.hurwitzEvenFEPair 0).Λ₀
      (((σ : ℂ) + (t : ℂ) * I) / 2) / 2‖ ≤ C / 2
  rw [norm_div, norm_ofNat]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
  convert h using 1
  push_cast
  ring_nf

/-- Away from its two displayed poles, the completed Riemann zeta function
is uniformly bounded on the same strip. -/
theorem exists_completedRiemannZeta_norm_le_criticalStrip_away :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      (1 : ℝ) / 2 ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ →
      (1 : ℝ) / 2 ≤ ‖1 - ((σ : ℂ) + (t : ℂ) * I)‖ →
      ‖completedRiemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  rcases exists_completedRiemannZeta₀_norm_le_criticalStrip with
    ⟨C, hC, hbound⟩
  refine ⟨C + 4, by positivity, ?_⟩
  intro σ t hσ0 hσ1 hz h1z
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  have h1zpos : 0 < ‖1 - z‖ := lt_of_lt_of_le (by norm_num) h1z
  rw [completedRiemannZeta_eq]
  calc
    ‖completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)‖ ≤
        ‖completedRiemannZeta₀ z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
      exact (norm_sub_le _ _).trans (by
        gcongr
        exact norm_sub_le _ _)
    _ ≤ C + 2 + 2 := by
      rw [norm_div, norm_one, norm_div, norm_one]
      have hzdiv : 1 / ‖z‖ ≤ 2 := by
        apply (div_le_iff₀ hzpos).2
        nlinarith
      have h1zdiv : 1 / ‖1 - z‖ ≤ 2 := by
        apply (div_le_iff₀ h1zpos).2
        nlinarith
      exact add_le_add (add_le_add (hbound σ t hσ0 hσ1) hzdiv) h1zdiv
    _ = C + 4 := by ring

end ZhangLS.Spec
