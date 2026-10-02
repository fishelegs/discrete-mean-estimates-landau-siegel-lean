import ZhangLS.Spec.Lemma57GaussianMellinKernel

/-!
# The Gaussian Mellin transform in Zhang's Lemma 5.7

This module proves the scalar transform left as an explicit obligation in
`Lemma57GaussianMellinKernel`.  In logarithmic coordinates the cumulative
Gaussian has a normalized Gaussian derivative.  Its bilateral complex Laplace
transform is evaluated by `integral_cexp_quadratic`; an integration by parts
then yields `M[x ↦ g_D(x⁻¹)](s) = ω₁(s)/s` for `Re(s) > 0`.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped Real FourierTransform

noncomputable def lemma57GaussianLogScale (D : ℕ) : ℝ :=
  Real.log (D : ℝ) ^ 15

noncomputable def lemma57GaussianLogDensity (D : ℕ) (u : ℝ) : ℂ :=
  ((lemma57GaussianLogScale D / Real.sqrt Real.pi : ℝ) : ℂ) *
    Complex.exp (-((lemma57GaussianLogScale D : ℂ) ^ 2) * (u : ℂ) ^ 2)

theorem lemma57GaussianLogDensity_integral {D : ℕ} (hD : 1 < D) (s : ℂ) :
    (∫ u : ℝ, Complex.exp (-s * (u : ℂ)) * lemma57GaussianLogDensity D u) =
      lemma57OmegaOne D s := by
  let c : ℝ := lemma57GaussianLogScale D
  have hc : 0 < c := by
    dsimp [c, lemma57GaussianLogScale]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have hb : (-((c : ℂ) ^ 2)).re < 0 := by
    rw [Complex.neg_re, pow_two, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact neg_lt_zero.mpr (mul_pos hc hc)
  have hquad := integral_cexp_quadratic hb (-s) 0
  have hintegrand : ∀ u : ℝ,
      Complex.exp (-s * (u : ℂ)) * lemma57GaussianLogDensity D u =
        ((c / Real.sqrt Real.pi : ℝ) : ℂ) *
          Complex.exp (-((c : ℂ) ^ 2) * u ^ 2 + (-s) * u + 0) := by
    intro u
    dsimp [lemma57GaussianLogDensity, c]
    calc
      _ = ((lemma57GaussianLogScale D / Real.sqrt Real.pi : ℝ) : ℂ) *
          (Complex.exp (-s * (u : ℂ)) *
            Complex.exp (-((lemma57GaussianLogScale D : ℂ) ^ 2) * (u : ℂ) ^ 2)) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        ring
  simp_rw [hintegrand, MeasureTheory.integral_const_mul, hquad]
  dsimp [lemma57OmegaOne]
  simp only [neg_neg, zero_sub, neg_sq]
  have hroot :
      ((Real.pi : ℂ) / (c : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
        ((Real.sqrt Real.pi / c : ℝ) : ℂ) := by
    have hq : 0 ≤ Real.pi / c ^ 2 := by positivity
    have hbase :
        (Real.pi : ℂ) / (c : ℂ) ^ 2 = ((Real.pi / c ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    calc
      ((Real.pi : ℂ) / (c : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
          (((Real.pi / c ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
            rw [hbase]
            symm
            convert Complex.ofReal_cpow hq (1 / 2 : ℝ) using 1 <;> norm_num
      _ = (Real.sqrt (Real.pi / c ^ 2) : ℂ) := by
        rw [Real.sqrt_eq_rpow]
      _ = ((Real.sqrt Real.pi / c : ℝ) : ℂ) := by
        rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hc.le]
  have hc30 :
      (c : ℂ) ^ 2 = (Real.log (D : ℝ) : ℂ) ^ 30 := by
    dsimp [c, lemma57GaussianLogScale]
    norm_cast
    ring
  have hexponent :
      -(s ^ 2 / (4 * -((c : ℂ) ^ 2))) =
        s ^ 2 / (4 * (Real.log (D : ℝ) : ℂ) ^ 30) := by
    rw [hc30]
    ring
  rw [hroot, hexponent]
  push_cast
  field_simp [hc.ne', (Real.sqrt_pos.2 Real.pi_pos).ne']

theorem lemma57GaussianLogDensity_laplace_integrable
    {D : ℕ} (hD : 1 < D) (s : ℂ) :
    Integrable (fun u : ℝ =>
      Complex.exp (-s * (u : ℂ)) * lemma57GaussianLogDensity D u) := by
  let c : ℝ := lemma57GaussianLogScale D
  have hc : 0 < c := by
    dsimp [c, lemma57GaussianLogScale]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have hb : (-((c : ℂ) ^ 2)).re < 0 := by
    rw [Complex.neg_re, pow_two, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact neg_lt_zero.mpr (mul_pos hc hc)
  have hquad : Integrable (fun u : ℝ =>
      Complex.exp (-((c : ℂ) ^ 2) * u ^ 2 + (-s) * u + 0)) :=
    integrable_cexp_quadratic' hb (-s) 0
  have hintegrand : (fun u : ℝ =>
      Complex.exp (-s * (u : ℂ)) * lemma57GaussianLogDensity D u) =
      (fun u : ℝ => ((c / Real.sqrt Real.pi : ℝ) : ℂ) *
        Complex.exp (-((c : ℂ) ^ 2) * u ^ 2 + (-s) * u + 0)) := by
    funext u
    dsimp [lemma57GaussianLogDensity, c]
    calc
      _ = ((lemma57GaussianLogScale D / Real.sqrt Real.pi : ℝ) : ℂ) *
          (Complex.exp (-s * (u : ℂ)) *
            Complex.exp (-((lemma57GaussianLogScale D : ℂ) ^ 2) * (u : ℂ) ^ 2)) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        ring
  rw [hintegrand]
  exact hquad.const_mul _

noncomputable def lemma57GaussianLogWeight (D : ℕ) (u : ℝ) : ℂ :=
  (zhangGaussianWeight D (Real.exp u) : ℂ)

theorem lemma57GaussianLogWeight_hasDerivAt
    {D : ℕ} (hD : 1 < D) (u : ℝ) :
    HasDerivAt (lemma57GaussianLogWeight D) (lemma57GaussianLogDensity D u) u := by
  let c : ℝ := lemma57GaussianLogScale D
  have hc : 0 < c := by
    dsimp [c, lemma57GaussianLogScale]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have hlogexp : Real.log (Real.exp u) = u := Real.log_exp u
  have hendpoint : zhangGaussianEndpoint D (Real.exp u) = c * u := by
    simp [zhangGaussianEndpoint, c, lemma57GaussianLogScale]
  have hgauss : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    fun_prop
  have hFTC : HasDerivAt
      (fun y : ℝ => ∫ t : ℝ in (0 : ℝ)..y, Real.exp (-(t ^ 2)))
      (Real.exp (-(c * u) ^ 2)) (c * u) :=
    hgauss.integral_hasStrictDerivAt 0 (c * u) |>.hasDerivAt
  have hinner : HasDerivAt (fun y : ℝ => c * y) c u := by
    simpa using (hasDerivAt_id (x := u)).const_mul c
  have hcomp := hFTC.comp u hinner
  have hreal : HasDerivAt
      (fun y : ℝ => (1 : ℝ) / 2 + (Real.sqrt Real.pi)⁻¹ *
        ∫ t : ℝ in (0 : ℝ)..c * y, Real.exp (-(t ^ 2)))
      ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(c * u) ^ 2) * c) u := by
    convert (hasDerivAt_const (x := u) ((1 : ℝ) / 2)).add
      (hcomp.const_mul (Real.sqrt Real.pi)⁻¹) using 1 <;> ring
  have hcomplex := hreal.ofReal_comp
  convert hcomplex using 1
  · ext y
    simp [lemma57GaussianLogWeight, zhangGaussianWeight, zhangGaussianEndpoint,
      c, lemma57GaussianLogScale]
  · dsimp [lemma57GaussianLogDensity, c]
    push_cast
    rw [div_eq_mul_inv]
    ring_nf

theorem zhangGaussianWeight_exp_add_neg {D : ℕ} (u : ℝ) :
    zhangGaussianWeight D (Real.exp u) +
      zhangGaussianWeight D (Real.exp (-u)) = 1 := by
  have hend1 : zhangGaussianEndpoint D (Real.exp u) =
      (Real.log (D : ℝ)) ^ 15 * u := by
    simp [zhangGaussianEndpoint]
  have hend2 : zhangGaussianEndpoint D (Real.exp (-u)) =
      -((Real.log (D : ℝ)) ^ 15 * u) := by
    simp [zhangGaussianEndpoint]
  unfold zhangGaussianWeight
  rw [hend1, hend2]
  have hsymm := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => Real.exp (-(t ^ 2)))
    (a := (0 : ℝ)) (b := (Real.log (D : ℝ)) ^ 15 * u)
  simp only [neg_zero, neg_sq] at hsymm
  have hneg :
      (∫ t : ℝ in (0 : ℝ)..-((Real.log (D : ℝ)) ^ 15 * u),
        Real.exp (-(t ^ 2))) =
      -(∫ t : ℝ in (0 : ℝ)..(Real.log (D : ℝ)) ^ 15 * u,
        Real.exp (-(t ^ 2))) := by
    calc
      _ = -(∫ t : ℝ in -((Real.log (D : ℝ)) ^ 15 * u)..(0 : ℝ),
          Real.exp (-(t ^ 2))) := intervalIntegral.integral_symm _ _
      _ = _ := congrArg Neg.neg hsymm.symm
  rw [hneg]
  ring

theorem lemma57GaussianLogWeight_norm_le_one {D : ℕ} (hD : 1 < D) (u : ℝ) :
    ‖lemma57GaussianLogWeight D u‖ ≤ 1 := by
  rw [lemma57GaussianLogWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zhangGaussianWeight_nonneg hD (Real.exp_pos u))]
  have hnonneg := zhangGaussianWeight_nonneg hD (Real.exp_pos (-u))
  linarith [zhangGaussianWeight_exp_add_neg (D := D) u]

noncomputable def lemma57GaussianLaplaceWeight (D : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-s * (u : ℂ)) * lemma57GaussianLogWeight D u

theorem lemma57GaussianLaplaceWeight_integrableOn_Ici
    {D : ℕ} (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (lemma57GaussianLaplaceWeight D s) (Set.Ici 0) := by
  have hmajor : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    unfold lemma57GaussianLaplaceWeight
    apply Continuous.mul
    · fun_prop
    · exact continuous_iff_continuousAt.mpr fun u =>
        (lemma57GaussianLogWeight_hasDerivAt hD u).continuousAt
  · filter_upwards [] with u
    rw [lemma57GaussianLaplaceWeight, norm_mul, norm_exp]
    have hexpre : (-s * (u : ℂ)).re = -s.re * u := by
      rw [Complex.mul_re]
      simp
    rw [hexpre]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (lemma57GaussianLogWeight_norm_le_one hD u)

theorem lemma57GaussianLaplaceWeight_integrableOn_Iic
    {D : ℕ} (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (lemma57GaussianLaplaceWeight D s) (Set.Iic 0) := by
  let c : ℝ := lemma57GaussianLogScale D
  have hc : 0 < c := by
    dsimp [c, lemma57GaussianLogScale]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  let K : ℝ := 2 * s.re / c
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let a : ℝ := -K / c
  have ha : a < 0 := by
    dsimp [a]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hK) hc
  let C : ℝ := (Real.sqrt Real.pi)⁻¹ / K
  have hmajor : IntegrableOn (fun u : ℝ => C * Real.exp (s.re * u))
      (Set.Iic a) := by
    exact (integrableOn_exp_mul_Iic hs a).const_mul C
  have htail : IntegrableOn (lemma57GaussianLaplaceWeight D s) (Set.Iic a) := by
    apply hmajor.mono'
    · apply Continuous.aestronglyMeasurable
      unfold lemma57GaussianLaplaceWeight
      apply Continuous.mul
      · fun_prop
      · exact continuous_iff_continuousAt.mpr fun u =>
          (lemma57GaussianLogWeight_hasDerivAt hD u).continuousAt
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
      have hu0 : u ≤ 0 := hu.trans ha.le
      have hend : zhangGaussianEndpoint D (Real.exp u) = c * u := by
        simp [zhangGaussianEndpoint, c, lemma57GaussianLogScale]
      have hendnonpos : zhangGaussianEndpoint D (Real.exp u) ≤ 0 := by
        rw [hend]
        exact mul_nonpos_of_nonneg_of_nonpos hc.le hu0
      have hthreshold : K ≤ -zhangGaussianEndpoint D (Real.exp u) := by
        rw [hend]
        dsimp [a] at hu
        apply (le_div_iff₀ hc).mp at hu
        linarith
      have htailbound := zhangGaussianTail_le_exp_linear hK hthreshold
      have hweight := zhangGaussianWeight_eq_tail_of_endpoint_nonpos hendnonpos
      have hweight_nonneg := zhangGaussianWeight_nonneg hD (Real.exp_pos u)
      rw [lemma57GaussianLaplaceWeight, norm_mul, norm_exp, lemma57GaussianLogWeight,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hweight_nonneg,
        hweight]
      have hexpre : (-s * (u : ℂ)).re = -s.re * u := by
        rw [Complex.mul_re]
        simp
      rw [hexpre]
      have hsqrt : 0 ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
      calc
        Real.exp (-s.re * u) *
              ((Real.sqrt Real.pi)⁻¹ *
                ∫ t : ℝ in Set.Ioi (-zhangGaussianEndpoint D (Real.exp u)),
                  Real.exp (-t ^ 2))
            ≤ Real.exp (-s.re * u) *
              ((Real.sqrt Real.pi)⁻¹ *
                (Real.exp (-K * (-zhangGaussianEndpoint D (Real.exp u))) / K)) := by
                  gcongr
        _ = C * Real.exp (s.re * u) := by
          rw [hend]
          have hexponent :
              -s.re * u + (-(K) * -(c * u)) = s.re * u := by
            dsimp [K]
            field_simp
            ring
          calc
            Real.exp (-s.re * u) *
                ((Real.sqrt Real.pi)⁻¹ *
                  (Real.exp (-K * -(c * u)) / K)) =
                C * (Real.exp (-s.re * u) *
                  Real.exp (-K * -(c * u))) := by
                    dsimp [C]
                    ring
            _ = C * Real.exp (-s.re * u + (-(K) * -(c * u))) := by
              rw [Real.exp_add]
            _ = C * Real.exp (s.re * u) := by rw [hexponent]
  have hcompact : IntegrableOn (lemma57GaussianLaplaceWeight D s) (Set.Icc a 0) := by
    have hcontinuous : Continuous (lemma57GaussianLaplaceWeight D s) :=
      continuous_iff_continuousAt.mpr fun u => by
      unfold lemma57GaussianLaplaceWeight
      apply ContinuousAt.mul
      · fun_prop
      · exact (lemma57GaussianLogWeight_hasDerivAt hD u).continuousAt
    exact hcontinuous.continuousOn.integrableOn_Icc
  have hunion : Set.Iic a ∪ Set.Icc a 0 = Set.Iic 0 := by
    ext u
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro (hu | hu)
      · exact hu.trans ha.le
      · exact hu.2
    · intro hu
      exact le_total u a |>.elim Or.inl (fun hau => Or.inr ⟨hau, hu⟩)
  rw [← hunion, integrableOn_union]
  exact ⟨htail, hcompact⟩

theorem lemma57GaussianLaplaceWeight_integrable
    {D : ℕ} (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    Integrable (lemma57GaussianLaplaceWeight D s) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ici_of_le (show (0 : ℝ) ≤ 0 by rfl),
    integrableOn_union]
  exact ⟨lemma57GaussianLaplaceWeight_integrableOn_Iic hD hs,
    lemma57GaussianLaplaceWeight_integrableOn_Ici hD hs⟩

theorem lemma57GaussianLaplaceWeight_integral
    {D : ℕ} (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    (∫ u : ℝ, lemma57GaussianLaplaceWeight D s u) = lemma57OmegaOne D s / s := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    simpa using hs
  let U : ℝ → ℂ := fun u => Complex.exp (-s * (u : ℂ))
  let U' : ℝ → ℂ := fun u => -s * Complex.exp (-s * (u : ℂ))
  let V : ℝ → ℂ := lemma57GaussianLogWeight D
  let V' : ℝ → ℂ := lemma57GaussianLogDensity D
  have hU : ∀ u ∈ tsupport V, HasDerivAt U (U' u) u := by
    intro u _hu
    dsimp [U, U']
    have hcomplex := ((hasDerivAt_id (x := (u : ℂ))).const_mul (-s)).cexp
    simpa [id, mul_comm] using hcomplex.comp_ofReal
  have hV : ∀ u ∈ tsupport U, HasDerivAt V (V' u) u := by
    intro u _hu
    exact lemma57GaussianLogWeight_hasDerivAt hD u
  have hUV' : Integrable (U * V') := by
    apply (lemma57GaussianLogDensity_laplace_integrable hD s).congr
    filter_upwards [] with u
    rfl
  have hU'V : Integrable (U' * V) := by
    have h := (lemma57GaussianLaplaceWeight_integrable hD hs).const_mul (-s)
    apply h.congr
    filter_upwards [] with u
    dsimp [U', V, lemma57GaussianLaplaceWeight]
    ring
  have hUV : Integrable (U * V) := by
    exact lemma57GaussianLaplaceWeight_integrable hD hs
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    hU hV hUV' hU'V hUV
  have hleft : (∫ u : ℝ, U u * V' u) = lemma57OmegaOne D s := by
    simpa [U, V'] using lemma57GaussianLogDensity_integral hD s
  have hright : (∫ u : ℝ, U' u * V u) =
      -s * ∫ u : ℝ, lemma57GaussianLaplaceWeight D s u := by
    simp only [U', V, lemma57GaussianLaplaceWeight]
    conv_lhs => enter [2, u]; rw [mul_assoc]
    rw [MeasureTheory.integral_const_mul]
  rw [hleft, hright] at hibp
  apply (eq_div_iff hs0).2
  calc
    (∫ u : ℝ, lemma57GaussianLaplaceWeight D s u) * s =
        s * ∫ u : ℝ, lemma57GaussianLaplaceWeight D s u := mul_comm _ _
    _ = lemma57OmegaOne D s := by
      rw [hibp]
      ring

theorem lemma57ReciprocalGaussianWeight_mellinConvergent
    {D : ℕ} (hD : 1 < D) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (lemma57ReciprocalGaussianWeight D) s := by
  have hderiv : ∀ x ∈ Set.univ,
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have himage : (Real.exp ∘ Neg.neg) '' Set.univ = Set.Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)
  rw [MellinConvergent, ← himage,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ hderiv hinj]
  have hlaplace := lemma57GaussianLaplaceWeight_integrable hD hs
  rw [integrableOn_univ]
  apply hlaplace.congr
  filter_upwards [] with u
  simp only [Function.comp_apply, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  change lemma57GaussianLaplaceWeight D s u = Real.exp (-u) •
      (Real.exp (-u) : ℂ) ^ (s - 1) •
        lemma57ReciprocalGaussianWeight D (Real.exp (-u))
  symm
  rw [lemma57ReciprocalGaussianWeight, ← Real.exp_neg, neg_neg]
  simp only [lemma57GaussianLaplaceWeight, lemma57GaussianLogWeight, Complex.real_smul, smul_eq_mul]
  push_cast
  have hfactor : Complex.exp (-(u : ℂ)) *
      Complex.exp (-(u : ℂ)) ^ (s - 1) = Complex.exp (-s * (u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg),
      ← Complex.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hfactor]

theorem lemma57ReciprocalGaussianWeight_mellin_eq_laplace
    (D : ℕ) (s : ℂ) :
    mellin (lemma57ReciprocalGaussianWeight D) s =
      ∫ u : ℝ, lemma57GaussianLaplaceWeight D s u := by
  rw [mellin_eq_fourier, Real.fourier_real_eq_integral_exp_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  simp only [Complex.real_smul, smul_eq_mul]
  rw [lemma57ReciprocalGaussianWeight, ← Real.exp_neg, neg_neg]
  simp only [lemma57GaussianLaplaceWeight, lemma57GaussianLogWeight]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp [Real.pi_ne_zero]
  calc
    ↑u * (-((s.im : ℂ) * I) + -(s.re : ℂ)) =
        -(↑u * ((s.re : ℂ) + (s.im : ℂ) * I)) := by ring
    _ = -(↑u * s) := by rw [Complex.re_add_im]

theorem lemma57GaussianKernelTransform_proved {D : ℕ} (hD : 1 < D) :
    Lemma57GaussianKernelTransform D := by
  intro s hs
  constructor
  · exact lemma57ReciprocalGaussianWeight_mellinConvergent hD hs
  · rw [lemma57ReciprocalGaussianWeight_mellin_eq_laplace]
    exact lemma57GaussianLaplaceWeight_integral hD hs

/-- Zhang's scalar Gaussian inverse-Mellin formula, now with no transform
hypothesis remaining. -/
theorem lemma57GaussianKernelVerticalIntegral_eq_weight
    {D : ℕ} (hD : 1 < D) {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    lemma57GaussianKernelVerticalIntegral D σ x =
      (zhangGaussianWeight D x : ℂ) :=
  lemma57GaussianKernelVerticalIntegral_eq_weight_of_transform
    hD (lemma57GaussianKernelTransform_proved hD) hσ hx

end ZhangLS.Spec

