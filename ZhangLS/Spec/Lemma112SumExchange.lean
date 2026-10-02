import ZhangLS.Spec.Lemma112Mellin
/-! # Summability and interval exchange for the genuine integrated cutoffs -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

lemma lemma112_profile_monotone {D : ℕ} (hD : 1 < D) :
    Monotone (lemma111Profile D) := by
  apply monotone_of_hasDerivAt_nonneg (lemma111_profile_hasDerivAt D)
  intro x
  exact mul_nonneg (div_nonneg (lemma111_scale_pos hD).le (Real.sqrt_nonneg _))
    (Real.exp_nonneg _)

lemma lemma112_scaled_weight_coordinate {D : ℕ} (hD : 1 < D)
    {A y : ℝ} (hA : 0 < A) (hy : 0 < y) (z : ℝ) :
    zhangGaussianWeight D (lemma23PaperP D ^ z * A / y) =
      lemma111Profile D (z - Real.log (y / A) / Real.log (lemma23PaperP D)) := by
  rw [← lemma111_weight_log_coordinate hD (div_pos hy hA)]
  congr 1
  field_simp

noncomputable def lemma112ScaledGaussianTerm {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (A : ℝ) (n : ℕ) (z : ℝ) : ℂ :=
  LSeries.term (lemma112Coefficient χ ψ) s n *
    (zhangGaussianWeight D (lemma23PaperP D ^ z * A / n) : ℂ)

lemma lemma112_scaled_gaussian_term_continuous {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Continuous (lemma112ScaledGaussianTerm χ ψ s A n) := by
  by_cases hn : n = 0
  · subst n
    change Continuous (fun z : ℝ => lemma112ScaledGaussianTerm χ ψ s A 0 z)
    simp only [lemma112ScaledGaussianTerm, LSeries.term_zero, zero_mul]
    exact continuous_const
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold lemma112ScaledGaussianTerm
    simp_rw [lemma112_scaled_weight_coordinate hD hA hn0]
    have hc := lemma111_profile_continuous D
    fun_prop

lemma lemma112_scaled_gaussian_term_norm_le {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {A : ℝ} (hA : 0 < A)
    (n : ℕ) {z b : ℝ} (hz : z ≤ b) :
    ‖lemma112ScaledGaussianTerm χ ψ s A n z‖ ≤
      ‖lemma112ScaledGaussianTerm χ ψ s A n b‖ := by
  by_cases hn : n = 0
  · simp [lemma112ScaledGaussianTerm, hn]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold lemma112ScaledGaussianTerm
    rw [norm_mul, norm_mul]
    rw [Complex.norm_of_nonneg (zhangGaussianWeight_nonneg hD
        (div_pos (mul_pos (Real.rpow_pos_of_pos (show 0 < lemma23PaperP D from Real.exp_pos _) _) hA) hn0)),
      Complex.norm_of_nonneg (zhangGaussianWeight_nonneg hD
        (div_pos (mul_pos (Real.rpow_pos_of_pos (show 0 < lemma23PaperP D from Real.exp_pos _) _) hA) hn0))]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simp_rw [lemma112_scaled_weight_coordinate hD hA hn0]
    exact lemma112_profile_monotone hD (sub_le_sub_right hz _)

/-- Absolute summability uniformly on each finite z interval supplies the
original infinite-series/integral exchange. -/
lemma lemma112_scaled_gaussian_interval_hasSum {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {A a b : ℝ} (hA : 0 < A) (hab : a ≤ b) :
    HasSum (fun n : ℕ => ∫ z in a..b, lemma112ScaledGaussianTerm χ ψ s A n z)
      (∫ z in a..b, lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z * A) s) := by
  let F := lemma112ScaledGaussianTerm χ ψ s A
  have hcont (n : ℕ) : Continuous (F n) :=
    lemma112_scaled_gaussian_term_continuous χ ψ s hD hA n
  have hsum : Summable (fun n : ℕ => ‖F n b‖) := summable_norm_iff.mpr
    (lemma112_actual_gaussian_summable χ ψ s hD
      (mul_pos (Real.rpow_pos_of_pos (show 0 < lemma23PaperP D from Real.exp_pos _) _) hA))
  have hint (n : ℕ) : Integrable (F n) (volume.restrict (Ioc a b)) :=
    ((hcont n).intervalIntegrable a b).1
  have hbound (n : ℕ) : (∫ z in Ioc a b, ‖F n z‖) ≤ (b - a) * ‖F n b‖ := by
    rw [← intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ _z in a..b, ‖F n b‖ := intervalIntegral.integral_mono_on hab
        ((hcont n).norm.intervalIntegrable a b) (continuous_const.intervalIntegrable a b)
        (fun z hz => lemma112_scaled_gaussian_term_norm_le χ ψ s hD hA n hz.2)
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]
  have hsumint : Summable (fun n : ℕ => ∫ z in Ioc a b, ‖F n z‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun z => norm_nonneg _)) hbound
      (hsum.mul_left (b - a))
  have hi := hasSum_integral_of_summable_integral_norm hint hsumint
  simpa only [← intervalIntegral.integral_of_le hab, F, lemma112ScaledGaussianTerm,
    lemma112GaussianSeries] using hi

lemma lemma112_scaled_gaussian_interval_series {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {A a b : ℝ} (hA : 0 < A) (hab : a ≤ b) :
    Summable (fun n : ℕ => LSeries.term (lemma112Coefficient χ ψ) s n *
        (Complex.ofReal (∫ z in a..b, zhangGaussianWeight D (lemma23PaperP D ^ z * A / n)))) ∧
      (∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
        (Complex.ofReal (∫ z in a..b, zhangGaussianWeight D (lemma23PaperP D ^ z * A / n)))) =
        ∫ z in a..b, lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z * A) s := by
  have hi := lemma112_scaled_gaussian_interval_hasSum χ ψ s hD hA hab
  simp only [lemma112ScaledGaussianTerm, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal] at hi
  exact ⟨hi.summable, hi.tsum_eq⟩

lemma lemma112_gaussian_series_continuousOn {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {A a b : ℝ} (hA : 0 < A) :
    ContinuousOn (fun z => lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z * A) s) (Icc a b) := by
  have hsum : Summable (fun n : ℕ => ‖lemma112ScaledGaussianTerm χ ψ s A n b‖) := summable_norm_iff.mpr
    (lemma112_actual_gaussian_summable χ ψ s hD
      (mul_pos (Real.rpow_pos_of_pos (show 0 < lemma23PaperP D from Real.exp_pos _) _) hA))
  exact continuousOn_tsum
    (fun n => (lemma112_scaled_gaussian_term_continuous χ ψ s hD hA n).continuousOn)
    hsum (fun n z hz => lemma112_scaled_gaussian_term_norm_le χ ψ s hD hA n hz.2)

lemma lemma112_gaussian_series_interval_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) {A : ℝ} (hA : 0 < A) (a b : ℝ) :
    IntervalIntegrable (fun z => lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z * A) s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact lemma112_gaussian_series_continuousOn χ ψ s hD hA

lemma lemma112_JtildeOne_integral {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) :
    Summable (fun n : ℕ => LSeries.term (lemma112Coefficient χ ψ) s n *
      (lemma111SmoothedOne D n : ℂ)) ∧
    lemma112JtildeOne χ ψ s =
      -500 * (∫ z in (1 / 2 : ℝ)..(251 / 500 : ℝ),
        lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s) +
      500 * (∫ z in (251 / 500 : ℝ)..(63 / 125 : ℝ),
        lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z) s) := by
  have h₁ := lemma112_scaled_gaussian_interval_series χ ψ s hD
    (A := 1) (by norm_num) (a := 1 / 2) (b := 251 / 500) (by norm_num)
  have h₂ := lemma112_scaled_gaussian_interval_series χ ψ s hD
    (A := 1) (by norm_num) (a := 251 / 500) (b := 63 / 125) (by norm_num)
  simp only [mul_one] at h₁ h₂
  have he (n : ℕ) : LSeries.term (lemma112Coefficient χ ψ) s n *
      (lemma111SmoothedOne D n : ℂ) =
      (-500 : ℂ) * (LSeries.term (lemma112Coefficient χ ψ) s n *
        Complex.ofReal (∫ z in (1 / 2 : ℝ)..(251 / 500 : ℝ),
          zhangGaussianWeight D (lemma23PaperP D ^ z / n))) +
      500 * (LSeries.term (lemma112Coefficient χ ψ) s n *
        Complex.ofReal (∫ z in (251 / 500 : ℝ)..(63 / 125 : ℝ),
          zhangGaussianWeight D (lemma23PaperP D ^ z / n))) := by
    unfold lemma111SmoothedOne
    push_cast
    ring
  constructor
  · simp_rw [he]
    exact (h₁.1.mul_left (-500 : ℂ)).add (h₂.1.mul_left (500 : ℂ))
  · unfold lemma112JtildeOne
    simp_rw [he]
    rw [Summable.tsum_add (h₁.1.mul_left (-500 : ℂ)) (h₂.1.mul_left (500 : ℂ)),
      tsum_mul_left, tsum_mul_left, h₁.2, h₂.2]

lemma lemma112_JtildeTwo_integral {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (hD : 1 < D) :
    Summable (fun n : ℕ => LSeries.term (lemma112Coefficient χ ψ) s n *
      (lemma111SmoothedTwo D n : ℂ)) ∧
    lemma112JtildeTwo χ ψ s =
      -500 * (∫ z in (62 / 125 : ℝ)..(249 / 500 : ℝ),
        lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z * (D : ℝ) * lemma51PaperT0 D) s) +
      500 * (∫ z in (249 / 500 : ℝ)..(1 / 2 : ℝ),
        lemma112GaussianSeries χ ψ (lemma23PaperP D ^ z * (D : ℝ) * lemma51PaperT0 D) s) := by
  have hA : 0 < (D : ℝ) * lemma51PaperT0 D := mul_pos
    (by exact_mod_cast lt_trans Nat.zero_lt_one hD)
    (pow_pos (Real.log_pos (by exact_mod_cast hD)) _)
  have h₁ := lemma112_scaled_gaussian_interval_series χ ψ s hD hA
    (a := 62 / 125) (b := 249 / 500) (by norm_num)
  have h₂ := lemma112_scaled_gaussian_interval_series χ ψ s hD hA
    (a := 249 / 500) (b := 1 / 2) (by norm_num)
  simp only [← mul_assoc] at h₁ h₂
  have he (n : ℕ) : LSeries.term (lemma112Coefficient χ ψ) s n *
      (lemma111SmoothedTwo D n : ℂ) =
      (-500 : ℂ) * (LSeries.term (lemma112Coefficient χ ψ) s n *
        Complex.ofReal (∫ z in (62 / 125 : ℝ)..(249 / 500 : ℝ),
          zhangGaussianWeight D (lemma23PaperP D ^ z * (D : ℝ) * lemma51PaperT0 D / n))) +
      500 * (LSeries.term (lemma112Coefficient χ ψ) s n *
        Complex.ofReal (∫ z in (249 / 500 : ℝ)..(1 / 2 : ℝ),
          zhangGaussianWeight D (lemma23PaperP D ^ z * (D : ℝ) * lemma51PaperT0 D / n))) := by
    unfold lemma111SmoothedTwo lemma51PaperT0
    push_cast
    ring
  constructor
  · simp_rw [he]
    exact (h₁.1.mul_left (-500 : ℂ)).add (h₂.1.mul_left (500 : ℂ))
  · unfold lemma112JtildeTwo
    simp_rw [he]
    rw [Summable.tsum_add (h₁.1.mul_left (-500 : ℂ)) (h₂.1.mul_left (500 : ℂ)),
      tsum_mul_left, tsum_mul_left, h₁.2, h₂.2]

end ZhangLS.Spec
