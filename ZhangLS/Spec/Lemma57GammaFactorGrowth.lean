import ZhangLS.Spec.Lemma57CompletedStripBounds

/-!
# Exponential growth of the reciprocal archimedean Gamma factor

The Gamma function is bounded on a vertical strip in the right half-plane by
its Euler integral. Euler's reflection formula then controls its reciprocal
by a complex sine, whose norm grows at most exponentially in the imaginary
part. These estimates apply to the factors in the completed zeta and Dirichlet
L-functions.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Real Topology

set_option maxHeartbeats 800000 in
/-- Euler's integral bounds `Gamma` uniformly on a closed vertical strip in
the right half-plane. -/
theorem exists_norm_Gamma_le_on_verticalStrip_of_pos
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  let majorant : ℝ → ℝ := fun x =>
    Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have haInt : IntegrableOn
      (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hbInt : IntegrableOn
      (fun x : ℝ => Real.exp (-x) * x ^ (b - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hb
  have hmajorant : IntegrableOn majorant (Ioi 0) := by
    dsimp [majorant]
    simpa only [mul_add] using haInt.add hbInt
  refine ⟨∫ x : ℝ in Ioi 0, majorant x, ?_, ?_⟩
  · apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.exp_nonneg _) (add_nonneg
      (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))
  · intro σ t hσa hσb
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hsre : 0 < s.re := by simpa [s] using lt_of_lt_of_le ha hσa
    have hsInt : IntegrableOn
        (fun x : ℝ => ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖) (Ioi 0) :=
      (Complex.GammaIntegral_convergent hsre).norm
    rw [Complex.Gamma_eq_integral hsre, Complex.GammaIntegral]
    calc
      ‖∫ x : ℝ in Ioi 0, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
          ∫ x : ℝ in Ioi 0, ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ in Ioi 0, majorant x := by
        apply MeasureTheory.integral_mono_ae hsInt hmajorant
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
          norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (s - 1).re = σ - 1 := by simp [s]
        rw [hre]
        dsimp [majorant]
        have hpow : x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
          rcases le_total x 1 with hx1 | h1x
          · exact (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)).trans
              (le_add_of_nonneg_right (Real.rpow_nonneg hx0.le _))
          · exact (Real.rpow_le_rpow_of_exponent_le h1x (by linarith)).trans
              (le_add_of_nonneg_left (Real.rpow_nonneg hx0.le _))
        exact mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)

/-- A complex sine grows at most exponentially in the absolute imaginary
part, independently of the real part. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h₁ : 2 * ‖Complex.sin z‖ =
      ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ := by
    have h := congrArg norm (Complex.two_sin (x := z))
    simpa [norm_mul] using h
  have h₂ : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    simp [Complex.norm_exp, Complex.mul_re]
  have h₃ : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    simp [Complex.norm_exp, Complex.mul_re]
  have h₄ : Real.exp z.im ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self _)
  have h₅ : Real.exp (-z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs _)
  have hbound := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  rw [h₂, h₃] at hbound
  rw [← h₁] at hbound
  linarith

set_option maxHeartbeats 800000 in
/-- Euler's reflection formula gives an exponential bound for reciprocal
`Gamma` on a strip whose real part lies strictly between zero and one. -/
theorem exists_norm_Gamma_inv_le_exp_on_verticalStrip
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ), a ≤ σ → σ ≤ b →
      ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t|) := by
  rcases exists_norm_Gamma_le_on_verticalStrip_of_pos
      (1 - b) (1 - a) (by linarith) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσa hσb
  let u : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hu : 0 < u.re := by simp [u]; linarith
  have h1u : 0 < (1 - u).re := by simp [u]; linarith
  have hΓu : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu
  have hΓ1u : Complex.Gamma (1 - u) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1u
  have hsin : Complex.sin (Real.pi * u) ≠ 0 := by
    intro hz
    have hreflection := Complex.Gamma_mul_Gamma_one_sub u
    rw [hz, div_zero] at hreflection
    exact (mul_ne_zero hΓu hΓ1u) hreflection
  have hinv : (Complex.Gamma u)⁻¹ =
      Complex.Gamma (1 - u) * Complex.sin (Real.pi * u) / Real.pi := by
    apply (mul_left_cancel₀ hΓu)
    rw [mul_inv_cancel₀ hΓu]
    rw [mul_div_assoc, ← mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
    field_simp [hsin, Real.pi_ne_zero]
  have hΓbound : ‖Complex.Gamma (1 - u)‖ ≤ C := by
    have h := hbound (1 - σ) (-t) (by linarith) (by linarith)
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
  rw [hinv, norm_div, norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
  have hπ : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hmul : ‖Complex.Gamma (1 - u)‖ *
      ‖Complex.sin (Real.pi * u)‖ ≤ C * Real.exp (Real.pi * |t|) :=
    mul_le_mul hΓbound hsinbound (norm_nonneg _) hC
  exact (div_le_self (by positivity) hπ).trans hmul

set_option maxHeartbeats 800000 in
/-- On the critical strip used for the zeta contour, the reciprocal of the
archimedean Gamma factor has at most exponential vertical growth. -/
theorem exists_norm_Gammaℝ_inv_le_exp_on_criticalStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      ‖(Gammaℝ ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t| / 2) := by
  rcases exists_norm_Gamma_inv_le_exp_on_verticalStrip
      ((1 : ℝ) / 4) ((3 : ℝ) / 4) (by norm_num) (by norm_num)
      (by norm_num) with ⟨C, hC, hbound⟩
  refine ⟨Real.pi * C, mul_nonneg Real.pi_pos.le hC, ?_⟩
  intro σ t hσa hσb
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hγ : ‖(Complex.Gamma (s / 2))⁻¹‖ ≤
      C * Real.exp (Real.pi * |t| / 2) := by
    have h := hbound (σ / 2) (t / 2) (by linarith) (by linarith)
    convert h using 1
    · congr 2
      push_cast
      simp [s]
      ring_nf
    · congr 1
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring_nf
  have hpow : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ ≤ Real.pi := by
    rw [show -s / 2 = -(s / 2) by ring, cpow_neg, inv_inv,
      norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hπ : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
    have hσ : (s / 2).re ≤ 1 := by simp [s]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hπ hσ
  rw [Gammaℝ_def, mul_inv, norm_mul]
  exact (mul_le_mul hpow hγ (norm_nonneg _) Real.pi_pos.le).trans_eq (by ring)

/-- The ordinary Riemann zeta function has an exponential vertical bound on
the contour's critical strip away from its pole at one. -/
theorem exists_riemannZeta_norm_le_exp_on_criticalStrip_away :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ t : ℝ),
      (1 : ℝ) / 2 ≤ σ → σ ≤ (3 : ℝ) / 2 →
      (1 : ℝ) / 2 ≤ ‖1 - ((σ : ℂ) + (t : ℂ) * I)‖ →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (Real.pi * |t| / 2) := by
  rcases exists_completedRiemannZeta_norm_le_criticalStrip_away with
    ⟨Cζ, hCζ, hζ⟩
  rcases exists_norm_Gammaℝ_inv_le_exp_on_criticalStrip with
    ⟨Cγ, hCγ, hγ⟩
  refine ⟨Cζ * Cγ, mul_nonneg hCζ hCγ, ?_⟩
  intro σ t hσa hσb h1s
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hsre : s.re = σ := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hsne : s ≠ 0 := by
    intro hs
    have : s.re = 0 := by rw [hs]; simp
    linarith
  have hsnorm : (1 : ℝ) / 2 ≤ ‖s‖ := by
    exact (hsre ▸ hσa).trans (Complex.re_le_norm s)
  have hζbound := hζ σ t hσa hσb hsnorm h1s
  have hγbound := hγ σ t hσa hσb
  rw [riemannZeta_def_of_ne_zero hsne, div_eq_mul_inv, norm_mul]
  exact (mul_le_mul hζbound hγbound (norm_nonneg _) hCζ).trans_eq (by ring)

end ZhangLS.Spec
