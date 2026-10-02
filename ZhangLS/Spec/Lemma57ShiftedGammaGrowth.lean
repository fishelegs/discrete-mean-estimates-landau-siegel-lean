import ZhangLS.Spec.Lemma57CompletedDirichletStripBounds

/-!
# The shifted odd archimedean Gamma factor

The odd Dirichlet L-function uses `Gammaℝ(s+1)`. Its half-Gamma argument crosses
real part one on the critical strip, so Step 43's direct reflection estimate
does not apply throughout. We bound the reciprocal on a compact central
region, and use one Gamma recurrence plus reflection outside that region.
-/

namespace ZhangLS.Spec

open Complex Set
open scoped Real Topology

/-- The reciprocal complex Gamma function is bounded on a closed ball. -/
theorem exists_norm_Gamma_inv_le_on_ball_three :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ ≤ 3 → ‖(Complex.Gamma u)⁻¹‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu
  exact (hC u (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)).trans
    (le_max_left _ _)

set_option maxHeartbeats 800000 in
/-- The reciprocal Gamma function has exponential vertical growth on the
mid-strip `3/4 ≤ Re u ≤ 5/4`, including the crossing of real part one. -/
theorem exists_norm_Gamma_inv_le_exp_on_midStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (3 : ℝ) / 4 ≤ σ → σ ≤ (5 : ℝ) / 4 →
      ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t|) := by
  rcases exists_norm_Gamma_inv_le_on_ball_three with ⟨C₀, hC₀, hcompact⟩
  rcases exists_norm_Gamma_le_on_verticalStrip_of_pos
      ((3 : ℝ) / 4) ((5 : ℝ) / 4) (by norm_num) (by norm_num) with
    ⟨C₁, hC₁, hgamma⟩
  refine ⟨max C₀ C₁, le_trans hC₀ (le_max_left _ _), ?_⟩
  intro σ t hσ0 hσ1
  let u : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hu : 0 < u.re := by simp [u]; linarith
  have h2u : 0 < (2 - u).re := by simp [u]; linarith
  have hexp : 1 ≤ Real.exp (Real.pi * |t|) := by
    rw [Real.one_le_exp_iff]
    positivity
  rcases le_total |t| 1 with ht_small | ht_large
  · have hσabs : |σ| ≤ (5 : ℝ) / 4 := by
      rw [abs_of_pos (by linarith)]
      exact hσ1
    have hu_ball : ‖u‖ ≤ 3 := by
      calc
        ‖u‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + |t| := by simp
        _ ≤ 3 := by linarith
    exact (hcompact u hu_ball).trans
      ((le_max_left C₀ C₁).trans (by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hexp
            (le_trans hC₀ (le_max_left C₀ C₁)))))
  · have ht : 0 < |t| := by linarith
    have hδ : 1 - u ≠ 0 := by
      intro h
      have him : (1 - u).im = -t := by simp [u]
      rw [h] at him
      simp at him
      subst t
      simp at ht
    have hΓu : Complex.Gamma u ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos hu
    have hΓ2u : Complex.Gamma (2 - u) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos h2u
    have hrec : Complex.Gamma (2 - u) =
        (1 - u) * Complex.Gamma (1 - u) := by
      simpa only [show (1 - u) + 1 = 2 - u by ring] using
        Complex.Gamma_add_one (1 - u) hδ
    have hΓ1u : Complex.Gamma (1 - u) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hrec
      exact hΓ2u hrec
    have hsin : Complex.sin (Real.pi * u) ≠ 0 := by
      intro hz
      have href := Complex.Gamma_mul_Gamma_one_sub u
      rw [hz, div_zero] at href
      exact (mul_ne_zero hΓu hΓ1u) href
    have hinv0 : (Complex.Gamma u)⁻¹ =
        Complex.Gamma (1 - u) * Complex.sin (Real.pi * u) / Real.pi := by
      apply (mul_left_cancel₀ hΓu)
      rw [mul_inv_cancel₀ hΓu]
      rw [mul_div_assoc, ← mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
      field_simp [hsin, Real.pi_ne_zero]
    have hΓrewrite : Complex.Gamma (1 - u) =
        Complex.Gamma (2 - u) / (1 - u) := by
      rw [hrec]
      field_simp [hδ]
    have hinv : (Complex.Gamma u)⁻¹ =
        Complex.Gamma (2 - u) * Complex.sin (Real.pi * u) /
          (Real.pi * (1 - u)) := by
      rw [hinv0, hΓrewrite]
      field_simp [hδ, Real.pi_ne_zero]
    have hΓbound : ‖Complex.Gamma (2 - u)‖ ≤ C₁ := by
      have h := hgamma (2 - σ) (-t) (by linarith) (by linarith)
      convert h using 1
      push_cast
      simp [u]
      ring_nf
    have him : |(Real.pi * u).im| = Real.pi * |t| := by
      simp [u, Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]
    have hsinbound : ‖Complex.sin (Real.pi * u)‖ ≤
        Real.exp (Real.pi * |t|) := by
      rw [← him]
      exact norm_sin_le_exp_abs_im (Real.pi * u)
    have hδnorm : 1 ≤ ‖1 - u‖ := by
      have h := Complex.abs_im_le_norm (1 - u)
      have himδ : |(1 - u).im| = |t| := by simp [u]
      rw [himδ] at h
      linarith
    have hdenom : 1 ≤ ‖(Real.pi : ℂ) * (1 - u)‖ := by
      rw [norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
      have hπ : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
      nlinarith
    rw [hinv, norm_div, norm_mul]
    calc
      ‖Complex.Gamma (2 - u)‖ * ‖Complex.sin (Real.pi * u)‖ /
          ‖(Real.pi : ℂ) * (1 - u)‖ ≤
        ‖Complex.Gamma (2 - u)‖ * ‖Complex.sin (Real.pi * u)‖ :=
        div_le_self (by positivity) hdenom
      _ ≤ C₁ * Real.exp (Real.pi * |t|) :=
        mul_le_mul hΓbound hsinbound (norm_nonneg _) hC₁
      _ ≤ max C₀ C₁ * Real.exp (Real.pi * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

set_option maxHeartbeats 800000 in
/-- The reciprocal odd archimedean Gamma factor has exponential vertical
growth on the contour's critical strip. -/
theorem exists_norm_Gammaℝ_shifted_inv_le_exp_on_criticalStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖(Gammaℝ (((σ : ℂ) + (t : ℂ) * I) + 1))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t| / 2) := by
  rcases exists_norm_Gamma_inv_le_exp_on_midStrip with
    ⟨C, hC, hbound⟩
  refine ⟨Real.pi ^ 2 * C, mul_nonneg (by positivity) hC, ?_⟩
  intro σ t hσ0 hσ1
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hγ : ‖(Complex.Gamma ((s + 1) / 2))⁻¹‖ ≤
      C * Real.exp (Real.pi * |t| / 2) := by
    have h := hbound ((σ + 1) / 2) (t / 2) (by linarith) (by linarith)
    convert h using 1
    · congr 2
      push_cast
      simp [s]
      ring_nf
    · congr 1
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring_nf
  have hpow : ‖((Real.pi : ℂ) ^ (-(s + 1) / 2))⁻¹‖ ≤ Real.pi ^ 2 := by
    rw [show -(s + 1) / 2 = -((s + 1) / 2) by ring,
      cpow_neg, inv_inv, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hπ : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
    have hσ : ((s + 1) / 2).re ≤ 2 := by simp [s]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hπ hσ
  rw [Gammaℝ_def, mul_inv, norm_mul]
  exact (mul_le_mul hpow hγ (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Both parity choices of the Dirichlet archimedean factor satisfy one
exponential-growth interface. -/
theorem exists_norm_dirichletGammaFactor_inv_le_exp_on_criticalStrip
    {D : ℕ} (χ : DirichletCharacter ℂ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖(DirichletCharacter.gammaFactor χ
        ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t| / 2) := by
  rcases χ.even_or_odd with he | ho
  · rcases exists_norm_Gammaℝ_inv_le_exp_on_criticalStrip with
      ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro σ t hσ0 hσ1
    rw [he.gammaFactor_def]
    exact hbound σ t hσ0 hσ1
  · rcases exists_norm_Gammaℝ_shifted_inv_le_exp_on_criticalStrip with
      ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro σ t hσ0 hσ1
    rw [ho.gammaFactor_def]
    exact hbound σ t hσ0 hσ1

/-- The actual primitive Dirichlet L-function has exponential vertical growth
on the critical strip needed by the contour. -/
theorem exists_dirichletLFunction_norm_le_exp_on_criticalStrip
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖dirichletLFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (Real.pi * |t| / 2) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  rcases exists_completedDirichletL_norm_le_criticalStrip χ hD with
    ⟨CL, hCL, hL⟩
  rcases exists_norm_dirichletGammaFactor_inv_le_exp_on_criticalStrip χ.chi with
    ⟨Cγ, hCγ, hγ⟩
  refine ⟨CL * Cγ, mul_nonneg hCL hCγ, ?_⟩
  intro σ t hσ0 hσ1
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hsne : s ≠ 0 := by
    intro hs
    have : σ = 0 := by
      have h := congrArg Complex.re hs
      simpa [s] using h
    linarith
  have hLbound := hL σ t hσ0 hσ1
  have hγbound := hγ σ t hσ0 hσ1
  change ‖χ.chi.LFunction s‖ ≤
    CL * Cγ * Real.exp (Real.pi * |t| / 2)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.chi s (.inl hsne),
    div_eq_mul_inv, norm_mul]
  exact (mul_le_mul hLbound hγbound (norm_nonneg _) hCL).trans_eq (by ring)

set_option maxHeartbeats 800000 in
/-- The remaining critical-half-strip growth condition for the undamped
Mellin factor follows from the ordinary zeta and Dirichlet L estimates. -/
theorem lemma57CriticalStripExponentialGrowth_unconditional
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57CriticalStripExponentialGrowth χ := by
  rcases exists_riemannZeta_norm_le_exp_on_criticalStrip_away with
    ⟨Cζ, hCζ, hζ⟩
  rcases exists_dirichletLFunction_norm_le_exp_on_criticalStrip χ hD with
    ⟨CL, hCL, hL⟩
  refine ⟨2 * (Cζ * CL), Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro σ t hσ0 hσ1 hsnorm
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hsnorm
  have hshift : 1 + s = (((1 + σ : ℝ) : ℂ) + (t : ℂ) * I) := by
    simp [s]
    ring_nf
  have hpole : (1 : ℝ) / 2 ≤ ‖1 - (1 + s)‖ := by
    simpa using hsnorm
  have hzeta : ‖riemannZeta (1 + s)‖ ≤
      Cζ * Real.exp (Real.pi * |t| / 2) := by
    rw [hshift]
    exact hζ (1 + σ) t (by linarith) (by linarith) (by simpa [hshift] using hpole)
  have hdir : ‖dirichletLFunction χ (1 + s)‖ ≤
      CL * Real.exp (Real.pi * |t| / 2) := by
    rw [hshift]
    exact hL (1 + σ) t (by linarith) (by linarith)
  rw [lemma57UndampedMellinFactor, norm_div, norm_mul]
  calc
    ‖riemannZeta (1 + s)‖ * ‖dirichletLFunction χ (1 + s)‖ / ‖s‖ ≤
        (Cζ * CL * Real.exp (Real.pi * |t|)) / ‖s‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      calc
        _ ≤ (Cζ * Real.exp (Real.pi * |t| / 2)) *
            (CL * Real.exp (Real.pi * |t| / 2)) :=
          mul_le_mul hzeta hdir (norm_nonneg _) (by positivity)
        _ = Cζ * CL * Real.exp (Real.pi * |t|) := by
          calc
            _ = Cζ * CL * (Real.exp (Real.pi * |t| / 2) *
                Real.exp (Real.pi * |t| / 2)) := by ring_nf
            _ = Cζ * CL * Real.exp (Real.pi * |t|) := by
              rw [← Real.exp_add]
              congr 1
              ring_nf
    _ ≤ 2 * (Cζ * CL) * Real.exp (Real.pi * |t|) := by
      apply (div_le_iff₀ hspos).2
      have hB : 0 ≤ Cζ * CL * Real.exp (Real.pi * |t|) := by positivity
      nlinarith

/-- The exact infinite contour shift of Lemma 5.7 is now unconditional for
primitive real characters of modulus greater than one. -/
theorem lemma57ContourShiftIdentity_unconditional
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_criticalStripExponentialGrowth χ hD
    (lemma57CriticalStripExponentialGrowth_unconditional χ hD)

end ZhangLS.Spec
