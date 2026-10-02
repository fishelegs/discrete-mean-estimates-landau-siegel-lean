import ZhangLS.Spec.Lemma44LongSum
import ZhangLS.Spec.Lemma57GaussianMellinTransform

/-!
# Gaussian smoothing of the actual long sum in Lemma 4.4

The derivative of the Gaussian cutoff costs at most `L^15/t`. This fits
within the existing `L^405` displacement budget, so smoothing preserves
the exponent `-180` obtained from the genuine condition (3.5).
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

/-- The Gaussian cutoff in logarithmic coordinates. -/
noncomputable def lemma44GaussianCutoff (D : ℕ) (B t : ℝ) : ℂ :=
  lemma57GaussianLogWeight D (Real.log B - Real.log t)

theorem lemma44GaussianCutoff_eq_weight {D : ℕ} {B t : ℝ}
    (hB : 0 < B) (ht : 0 < t) :
    lemma44GaussianCutoff D B t = (zhangGaussianWeight D (B / t) : ℂ) := by
  rw [lemma44GaussianCutoff, lemma57GaussianLogWeight,
    Real.exp_sub, Real.exp_log hB, Real.exp_log ht]

theorem lemma44GaussianLogDensity_norm_le {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) (u : ℝ) :
    ‖lemma57GaussianLogDensity D u‖ ≤ lemma23PaperL D ^ 15 := by
  let c := lemma23PaperL D ^ 15
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsqrt : 1 ≤ Real.sqrt Real.pi := by
    have h := Real.sqrt_le_sqrt (by linarith [Real.one_le_pi_div_two] : 1 ≤ Real.pi)
    simpa using h
  have heq : ‖lemma57GaussianLogDensity D u‖ =
      (c / Real.sqrt Real.pi) * Real.exp (-(c ^ 2 * u ^ 2)) := by
    change ‖((c / Real.sqrt Real.pi : ℝ) : ℂ) *
      Complex.exp (-((c : ℂ) ^ 2) * (u : ℂ) ^ 2)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hc (Real.sqrt_nonneg _)), Complex.norm_exp]
    congr 2
    simp [pow_two, Complex.mul_re]
  rw [heq]
  have he : Real.exp (-(c ^ 2 * u ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg c) (sq_nonneg u)))
  calc
    (c / Real.sqrt Real.pi) * Real.exp (-(c ^ 2 * u ^ 2)) ≤
        (c / Real.sqrt Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left he (div_nonneg hc (Real.sqrt_nonneg _))
    _ ≤ c := by simpa only [mul_one] using div_le_self hc hsqrt

theorem lemma44GaussianCutoff_norm_le_one {D : ℕ}
    (hD : 1 < D) (B t : ℝ) : ‖lemma44GaussianCutoff D B t‖ ≤ 1 :=
  lemma57GaussianLogWeight_norm_le_one hD _

theorem lemma44GaussianCutoff_hasDerivAt {D : ℕ}
    (hD : 1 < D) (B : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (lemma44GaussianCutoff D B)
      ((-t⁻¹) • lemma57GaussianLogDensity D (Real.log B - Real.log t)) t := by
  have hi := (Real.hasDerivAt_log ht).const_sub (Real.log B)
  simpa only [Function.comp_def, lemma44GaussianCutoff] using
    (lemma57GaussianLogWeight_hasDerivAt hD _).scomp t hi

theorem lemma44GaussianCutoff_norm_deriv_le {D : ℕ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (B : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖deriv (lemma44GaussianCutoff D B) t‖ ≤ lemma23PaperL D ^ 15 / t := by
  rw [(lemma44GaussianCutoff_hasDerivAt hD B ht.ne').deriv, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr ht)]
  have h := mul_le_mul_of_nonneg_left
    (lemma44GaussianLogDensity_norm_le hL (Real.log B - Real.log t)) (inv_nonneg.mpr ht.le)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The genuine smoothed sum; `B=P^(9/5)` is the paper's application. -/
noncomputable def lemma44GaussianLongDirichletSum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ) (B : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊,
    lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
      Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) * (zhangGaussianWeight D (B / n) : ℂ)

theorem lemma44_gaussian_long_sum_eq_centered_abel_sum {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    {B : ℝ} (hB : 0 < B) :
    lemma44GaussianLongDirichletSum χ ψ s B =
      ∑ n ∈ Finset.Icc 0 ⌊lemma23PaperP D ^ 2⌋₊,
        (lemma23AbelPowerWeight (lemma23PaperCenter D - s) n *
          lemma44GaussianCutoff D B n) * lemma44X3CenteredCoefficient χ ψ n := by
  classical
  have hfilter : (Finset.Icc 0 ⌊lemma23PaperP D ^ 2⌋₊).filter (fun n => D ^ 4 < n) =
      Finset.Ioc (D ^ 4) ⌊lemma23PaperP D ^ 2⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [lemma44X3CenteredCoefficient, mul_ite, mul_zero, ← Finset.sum_filter, hfilter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
  rw [lemma44GaussianCutoff_eq_weight hB hnpos]
  simp only [lemma23AbelPowerWeight]
  rw [show (Complex.exp ((lemma23PaperCenter D - s) * (Real.log (n : ℝ) : ℂ)) *
      (zhangGaussianWeight D (B / n) : ℂ)) *
        (lemma23NuArithmeticFunction χ n * ψ (n : ZMod N) *
          Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))) =
      (lemma23NuArithmeticFunction χ n * ψ (n : ZMod N)) *
        (Complex.exp ((lemma23PaperCenter D - s) * (Real.log (n : ℝ) : ℂ)) *
          Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))) *
            (zhangGaussianWeight D (B / n) : ℂ) by ring, ← Complex.exp_add]
  rw [show (lemma23PaperCenter D - s) * (Real.log (n : ℝ) : ℂ) +
    -lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ) =
      -s * (Real.log (n : ℝ) : ℂ) by ring]

theorem lemma44AbelPowerWeight_hasDerivAt (z : ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (lemma23AbelPowerWeight z)
      (z * lemma23AbelPowerWeight z t * ((t⁻¹ : ℝ) : ℂ)) t := by
  have hlog := (Real.hasDerivAt_log ht).ofReal_comp
  have h := (hlog.const_mul z).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp (z * (Real.log x : ℂ)))
    (z * Complex.exp (z * (Real.log t : ℂ)) * ((t⁻¹ : ℝ) : ℂ)) t
  convert h using 1
  ring

/-- Gaussian smoothing incurs an additive `L^15` derivative cost, with no new
good-set hypothesis. The cutoff scale can be any positive real number. -/
theorem lemma44_gaussian_long_sum_bound {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    {B : ℝ} (hB : 0 < B) :
    ‖lemma44GaussianLongDirichletSum χ ψ s B‖ ≤
      Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) *
        (1 + ‖lemma23PaperCenter D - s‖ + lemma23PaperL D ^ 15) *
          lemma23PaperL D ^ (-585 : ℤ) := by
  let R := lemma23PaperP D ^ 2
  let K : ℕ := ⌊R⌋₊
  let c := lemma44X3CenteredCoefficient χ ψ
  let z := lemma23PaperCenter D - s
  let A := Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re))
  let f : ℝ → ℂ := fun t => lemma23AbelPowerWeight z t * lemma44GaussianCutoff D B t
  have hD : 1 < D := by
    by_contra h
    have hD1 : D = 1 := by have hp := χ.modulus_pos; omega
    norm_num [lemma23PaperL, hD1] at hL
  have hR : 1 ≤ R := by
    have hP : 1 ≤ lemma23PaperP D := by
      apply Real.one_le_exp_iff.mpr
      positivity
    exact one_le_pow₀ hP
  have hK1 : 1 ≤ K := (Nat.le_floor_iff (by linarith : 0 ≤ R)).mpr (by simpa using hR)
  have hKR : (K : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hweight {t : ℝ} (ht : 1 ≤ t) (htR : t ≤ R) :
      ‖lemma23AbelPowerWeight z t‖ ≤ A := by
    have hlog : Real.log t ≤ 2 * lemma23PaperL D ^ 9 := by
      have h := Real.log_le_log (by linarith : 0 < t) htR
      simpa [R, Real.log_pow, lemma23PaperP, Real.log_exp] using h
    apply (lemma23AbelPowerWeight_norm_le_exp ht (by
      change 1 / 2 - s.re ≤ max 0 (1 / 2 - s.re)
      exact le_max_right _ _)).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog (le_max_left 0 (1 / 2 - s.re))]
  have hfd {t : ℝ} (ht : t ≠ 0) : HasDerivAt f
      ((z * lemma23AbelPowerWeight z t * ((t⁻¹ : ℝ) : ℂ)) * lemma44GaussianCutoff D B t +
        lemma23AbelPowerWeight z t *
          ((-t⁻¹) • lemma57GaussianLogDensity D (Real.log B - Real.log t))) t :=
    (lemma44AbelPowerWeight_hasDerivAt z ht).mul (lemma44GaussianCutoff_hasDerivAt hD B ht)
  have hfInt : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) K) := by
    have hc : ContinuousOn
        (fun t : ℝ => (z * lemma23AbelPowerWeight z t * ((t⁻¹ : ℝ) : ℂ)) *
          lemma44GaussianCutoff D B t + lemma23AbelPowerWeight z t *
            ((-t⁻¹) • lemma57GaussianLogDensity D (Real.log B - Real.log t)))
        (Set.Icc (1 : ℝ) K) := by
      intro t ht
      have htne : t ≠ 0 := by linarith [ht.1]
      have hcut := (lemma44GaussianCutoff_hasDerivAt hD B htne).continuousAt
      have hpow := (lemma44AbelPowerWeight_hasDerivAt z htne).continuousAt
      have hinv : ContinuousAt (fun x : ℝ => x⁻¹) t := continuousAt_id.inv₀ htne
      have hcinv : ContinuousAt (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) t :=
        Complex.continuous_ofReal.continuousAt.comp hinv
      have hden : Continuous (lemma57GaussianLogDensity D) := by
        unfold lemma57GaussianLogDensity
        fun_prop
      have hdenc : ContinuousAt
          (fun x : ℝ => lemma57GaussianLogDensity D (Real.log B - Real.log x)) t :=
        hden.continuousAt.comp (continuousAt_const.sub (Real.continuousAt_log htne))
      exact (((continuousAt_const.mul hpow).mul hcinv).mul hcut).add
        (hpow.mul (hinv.neg.smul hdenc)) |>.continuousWithinAt
    exact (hc.congr (fun t ht => (hfd (by linarith [ht.1])).deriv)).integrableOn_Icc
  have hder {t : ℝ} (ht : t ∈ Set.Ioc (1 : ℝ) K) :
      ‖deriv f t‖ ≤ ((‖z‖ + lemma23PaperL D ^ 15) * A) / t := by
    have htpos : 0 < t := by linarith [ht.1]
    have hp := lemma23AbelPowerWeight_norm_deriv_le htpos
      (mul_le_mul_of_nonneg_left (hweight ht.1.le (ht.2.trans hKR)) (norm_nonneg z))
    have hg := lemma44GaussianCutoff_norm_deriv_le hD hL B htpos
    have heq : deriv f t = deriv (lemma23AbelPowerWeight z) t * lemma44GaussianCutoff D B t +
        lemma23AbelPowerWeight z t * deriv (lemma44GaussianCutoff D B) t := by
      rw [(lemma44AbelPowerWeight_hasDerivAt z htpos.ne').deriv,
        (lemma44GaussianCutoff_hasDerivAt hD B htpos.ne').deriv]
      exact (hfd htpos.ne').deriv
    rw [heq]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    have h₁ := mul_le_mul hp (lemma44GaussianCutoff_norm_le_one hD B t)
      (norm_nonneg _) (by positivity : 0 ≤ (‖z‖ * A) / t)
    have h₂ := mul_le_mul (hweight ht.1.le (ht.2.trans hKR)) hg
      (norm_nonneg _) (by dsimp [A]; positivity)
    calc
      _ ≤ (‖z‖ * A / t) * 1 + A * (lemma23PaperL D ^ 15 / t) := add_le_add h₁ h₂
      _ = _ := by ring
  have hb := hgood.x3_bounds hL
  have hEndpoint : ‖∑ k ∈ Finset.Icc 0 K, c k‖ ≤ lemma23PaperL D ^ (-585 : ℤ) := by
    simpa only [K, c, ← lemma44_X3_eq_centered_partial_sum] using hb.1
  have hIntegral : (∫ t in Set.Ioc (1 : ℝ) K,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t) ≤ lemma23PaperL D ^ (-585 : ℤ) := by
    simp only [c, ← lemma44_X3_eq_centered_partial_sum]
    apply le_trans _ hb.2
    apply setIntegral_mono_set (lemma44_X3_div_integrable χ ψ)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact div_nonneg (norm_nonneg _) (by linarith [ht.1])
    · exact (Set.Ioc_subset_Ioc_right hKR).eventuallyLE
  have hbase := lemma23_abel_partial_sum_norm_bound_of_derivative (c := c) (f := f)
    (N := K) (A := A) (B := lemma23PaperL D ^ (-585 : ℤ))
    (K := (‖z‖ + lemma23PaperL D ^ 15) * A) (M := lemma23PaperL D ^ (-585 : ℤ))
    (by simp [c]) (fun t ht => (hfd (by linarith [ht.1])).differentiableAt) hfInt
    (by
      rw [show f K = lemma23AbelPowerWeight z K * lemma44GaussianCutoff D B K from rfl,
        norm_mul]
      have hm := mul_le_mul (hweight (by exact_mod_cast hK1) hKR)
        (lemma44GaussianCutoff_norm_le_one hD B K) (norm_nonneg _) (by dsimp [A]; positivity)
      simpa only [mul_one] using hm)
    hEndpoint (by dsimp [A]; positivity) (fun t ht => hder ht)
    (lemma23_partial_sum_div_integrableOn_Ioc c) hIntegral
  change ‖∑ k ∈ Finset.Icc 0 K,
    (lemma23AbelPowerWeight z k * lemma44GaussianCutoff D B k) * c k‖ ≤ _ at hbase
  rw [← lemma44_gaussian_long_sum_eq_centered_abel_sum χ ψ s hB] at hbase
  exact hbase.trans_eq (by dsimp [A, z]; ring)

/-- The extra Gaussian derivative fits in the displacement budget. -/
theorem lemma44_gaussian_long_sum_L180_of_displacement {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hL : 3 ≤ lemma23PaperL D) (hgood : Lemma23GoodPartialSums χ ψ)
    (hdisp : ‖lemma23PaperCenter D - s‖ ≤ 3 * lemma23PaperL D ^ 405)
    {B : ℝ} (hB : 0 < B) :
    ‖lemma44GaussianLongDirichletSum χ ψ s B‖ ≤
      5 * Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) *
        lemma23PaperL D ^ (-180 : ℤ) := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hpow : 1 ≤ lemma23PaperL D ^ 405 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hpow15 : lemma23PaperL D ^ 15 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  have hprod : lemma23PaperL D ^ 405 * lemma23PaperL D ^ (-585 : ℤ) =
      lemma23PaperL D ^ (-180 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLpos.ne']
    norm_num
  have hcoef : (1 + ‖lemma23PaperCenter D - s‖ + lemma23PaperL D ^ 15) *
      lemma23PaperL D ^ (-585 : ℤ) ≤ 5 * lemma23PaperL D ^ (-180 : ℤ) := by
    calc
      _ ≤ (5 * lemma23PaperL D ^ 405) * lemma23PaperL D ^ (-585 : ℤ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [mul_assoc, hprod]
  have hb := lemma44_gaussian_long_sum_bound χ ψ s hL hgood hB
  have he := mul_le_mul_of_nonneg_left hcoef
    (Real.exp_nonneg (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)))
  exact hb.trans (by nlinarith only [he])

/-- The actual Gaussian-smoothed long sum is uniformly `O(L^-180)` on `Ω₃`. -/
theorem lemma44_gaussian_long_sum_on_omega3 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {B : ℝ} (hB : 0 < B) :
    ‖lemma44GaussianLongDirichletSum χ ψ s B‖ ≤
      5 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have ha := lemma44_alpha_pos_le_one hL
  have hmax : max 0 (1 / 2 - s.re) ≤ lemma44PaperAlpha D :=
    max_le ha.1.le (by linarith [hs.1])
  have halpha : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have hexp : Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) ≤
      Real.exp (2 * Real.pi) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmax (pow_pos hLpos 9).le
    rw [halpha] at h
    linarith
  have hb := lemma44_gaussian_long_sum_L180_of_displacement χ ψ s hL hψ.2
    (lemma44_omega3_displacement hL hs) hB
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- The paper uses `P^(9/5)` in the Gaussian Mellin cutoff. -/
noncomputable def lemma44PaperGaussianScale (D : ℕ) : ℝ :=
  lemma23PaperP D ^ (9 / 5 : ℝ)

theorem lemma44_paper_gaussian_long_sum_on_omega3 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D)‖ ≤
      5 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) :=
  lemma44_gaussian_long_sum_on_omega3 χ ψ hL hψ hs
    (Real.rpow_pos_of_pos (Real.exp_pos _) _)

end ZhangLS.Spec
