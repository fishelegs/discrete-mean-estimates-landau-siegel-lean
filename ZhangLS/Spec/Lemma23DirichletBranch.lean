import ZhangLS.Spec.Lemma23DirichletUnitModulus
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The square-root branch for Zhang's normalization

On the upper half-plane the factor `Z(s, χ)` is holomorphic and nonzero.
Since that domain is simply connected, its inverse has a continuous square
root.  This file connects the abstract branch construction to the actual
Dirichlet-character factor used in Lemma 2.3.
-/

namespace ZhangLS.Spec

open ComplexConjugate UpperHalfPlane
open Filter Set
open scoped Topology

/-- `Gammaℝ` is differentiable away from the real axis: its Gamma argument
cannot hit a pole there. -/
theorem lemma23_GammaR_differentiableAt_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) : DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hGammaR : Complex.Gammaℝ =
      fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z
    exact Complex.Gammaℝ_def z
  rw [hGammaR]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hexp : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hexp.const_cpow (Or.inl hpi)
  have hargIm : (s / 2).im ≠ 0 := by
    rw [show (s / 2).im = s.im / 2 by simp]
    exact div_ne_zero hs (by norm_num)
  have hGammaPoleFree : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n h
    have him := congrArg Complex.im h
    apply hargIm
    simpa using him
  have hGamma : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    exact (Complex.differentiableAt_Gamma (s / 2) hGammaPoleFree).comp s
      (differentiableAt_id.div_const (2 : ℂ))
  exact hpow.mul hGamma

/-- Every Dirichlet gamma factor is differentiable at non-real points. -/
theorem lemma23_gammaFactor_differentiableAt_of_im_ne_zero
    {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with heven | hodd
  · have hfactor : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z
      exact heven.gammaFactor_def z
    rw [hfactor]
    exact lemma23_GammaR_differentiableAt_of_im_ne_zero hs
  · have hfactor : DirichletCharacter.gammaFactor χ =
        fun z : ℂ => Complex.Gammaℝ (z + 1) := by
      funext z
      exact hodd.gammaFactor_def z
    rw [hfactor]
    have hshift : DifferentiableAt ℂ
        (fun z : ℂ => Complex.Gammaℝ (z + 1)) s := by
      have hGamma := lemma23_GammaR_differentiableAt_of_im_ne_zero
        (s := s + 1) (by simpa [Complex.add_im] using hs)
      have hshiftArg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s :=
        differentiableAt_id.add_const 1
      simpa only [Function.comp_apply] using hGamma.comp s hshiftArg
    exact hshift

/-- The actual Zhang factor `Z(s,χ)` is differentiable off the real axis. -/
theorem lemma23DirichletZ_differentiableAt_of_im_ne_zero
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.im ≠ 0) : DifferentiableAt ℂ (lemma23DirichletZ χ) s := by
  have hN : (N : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  have hexp : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) s := by
    fun_prop
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - z)) s :=
    hexp.const_cpow (Or.inl hN)
  have hnum : DifferentiableAt ℂ
      (fun z : ℂ => DirichletCharacter.gammaFactor χ⁻¹ (1 - z)) s := by
    have harg : (1 - s).im ≠ 0 := by
      simpa [Complex.sub_im] using neg_ne_zero.mpr hs
    exact (lemma23_gammaFactor_differentiableAt_of_im_ne_zero χ⁻¹ harg).comp s
      (differentiableAt_id.const_sub 1)
  have hden := lemma23_gammaFactor_differentiableAt_of_im_ne_zero χ hs
  have hdenNe := lemma23_gammaFactor_ne_zero_of_im_ne_zero χ hs
  have hratio : DifferentiableAt ℂ
      (fun z : ℂ => DirichletCharacter.gammaFactor χ⁻¹ (1 - z) /
        DirichletCharacter.gammaFactor χ z) s := hnum.div hden hdenNe
  simpa only [lemma23DirichletZ] using
    ((hpow.mul (differentiableAt_const _ : DifferentiableAt ℂ
      (fun _ : ℂ => DirichletCharacter.rootNumber χ) s)).mul hratio)

/-- Continuity of `Z` on the open upper half-plane, discharged from its local
analyticity rather than assumed as part of the square-root construction. -/
theorem lemma23DirichletZ_continuousOn_upperHalfPlane
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ContinuousOn (lemma23DirichletZ χ) UpperHalfPlane.upperHalfPlaneSet := by
  intro s hs
  exact (lemma23DirichletZ_differentiableAt_of_im_ne_zero χ (ne_of_gt hs)).continuousAt
    |>.continuousWithinAt

/-- The upper half-plane is simply connected, transported from the
contractible type `UpperHalfPlane` along its standard embedding into `ℂ`. -/
theorem lemma23_upperHalfPlane_isSimplyConnected :
    IsSimplyConnected UpperHalfPlane.upperHalfPlaneSet := by
  have hUniv : IsSimplyConnected (Set.univ : Set UpperHalfPlane) := by
    change SimplyConnectedSpace (Set.univ : Set UpperHalfPlane)
    exact (Homeomorph.Set.univ UpperHalfPlane).toHomotopyEquiv
      |>.simplyConnectedSpace
  have hembedded : IsSimplyConnected
      (UpperHalfPlane.coe '' (Set.univ : Set UpperHalfPlane)) :=
    (UpperHalfPlane.isEmbedding_coe.isSimplyConnected_image
      (s := Set.univ)).2 hUniv
  simpa only [Set.image_univ, UpperHalfPlane.range_coe] using hembedded

/-- For a primitive nontrivial character, Zhang's actual `Z(s,χ)` has a
continuous square-root branch of its inverse on the upper half-plane. -/
theorem lemma23_exists_continuous_actual_square_root
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1) :
    ∃ Y : ℂ → ℂ,
      ContinuousOn Y UpperHalfPlane.upperHalfPlaneSet ∧
      ∀ s ∈ UpperHalfPlane.upperHalfPlaneSet,
        Y s ^ 2 = (lemma23DirichletZ χ s)⁻¹ := by
  apply exists_continuousOn_lemma23_square_root_inverse
    lemma23_upperHalfPlane_isSimplyConnected
    UpperHalfPlane.isOpen_upperHalfPlaneSet
    (lemma23DirichletZ χ)
    (lemma23DirichletZ_continuousOn_upperHalfPlane χ)
  intro s hs
  exact lemma23DirichletZ_ne_zero_of_im_pos χ hχ hN hs

/-- The local square-root derivative remains valid when the root equation is
known only on an open domain.  The proof extends the radicand arbitrarily
outside that domain; openness makes this extension locally identical to the
analytic radicand at the point of interest. -/
theorem lemma23_hasDerivAt_square_root_on_open
    {U : Set ℂ} (hUopen : IsOpen U) {Y G : ℂ → ℂ} {a gDeriv : ℂ}
    (ha : a ∈ U) (hYcont : ContinuousOn Y U)
    (hYsquare : ∀ z ∈ U, Y z ^ 2 = G z)
    (hG : HasDerivAt G gDeriv a) (hGne : G a ≠ 0) :
    HasDerivAt Y (gDeriv / (2 * Y a)) a := by
  classical
  have hYne : Y a ≠ 0 := by
    intro hzero
    have hsq := hYsquare a ha
    rw [hzero] at hsq
    exact hGne (by simpa using hsq.symm)
  let Gext : ℂ → ℂ := fun z => if z ∈ U then G z else Y z ^ 2
  have hGextSquare : ∀ z : ℂ, Y z ^ 2 = Gext z := by
    intro z
    by_cases hz : z ∈ U
    · simp [Gext, hz, hYsquare z hz]
    · simp [Gext, hz]
  have hGextEq : Gext =ᶠ[𝓝 a] G := by
    filter_upwards [hUopen.mem_nhds ha] with z hz
    simp [Gext, hz]
  have hGext : HasDerivAt Gext gDeriv a :=
    hG.congr_of_eventuallyEq hGextEq
  exact hasDerivAt_lemma23_square_root_of_continuity
    (hYcont.continuousAt (hUopen.mem_nhds ha)) hGextSquare hYne hGext

/-- Reality of the vertical derivative can be deduced from reality on just
the right-hand side of the critical-line zero.  This is the form needed when
the square-root branch is constructed on the upper half-plane. -/
theorem lemma23_vertical_derivative_real_of_line_real_right
    {M : ℂ → ℂ} {ρ mDeriv : ℂ}
    (hM : HasDerivAt M mDeriv ρ) (hMzero : M ρ = 0)
    (hlineReal : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (M (ρ + Complex.I * (t : ℂ))).im = 0) :
    (Complex.I * mDeriv).im = 0 := by
  let g : ℝ → ℝ := fun t => (M (ρ + Complex.I * (t : ℂ))).im
  have hg : HasDerivAt g (Complex.im (Complex.I * mDeriv)) 0 := by
    simpa [g] using hasDerivAt_criticalLineImagPart hM
  have hg0 : g 0 = 0 := by simp [g, hMzero]
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * g t) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.im (Complex.I * mDeriv))) := by
    simpa [hg0, smul_eq_mul] using hg.tendsto_slope_zero_right
  have hzSlope : (fun t : ℝ => t⁻¹ * g t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ : ℝ => 0) := by
    filter_upwards [hlineReal] with t ht
    simp [g, ht]
  have hslopeZero : Tendsto (fun t : ℝ => t⁻¹ * g t) (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℝ)) := Tendsto.congr' hzSlope.symm tendsto_const_nhds
  exact tendsto_nhds_unique hslope hslopeZero

/-- Zhang's normalized function attached to an actual Dirichlet character
and a chosen square-root branch. -/
noncomputable def lemma23DirichletNormalizedM {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (Y : ℂ → ℂ) : ℂ → ℂ :=
  lemma23NormalizedM Y (DirichletCharacter.LFunction χ)

/-- With an actual upper-half-plane branch, the only additional inputs needed
for the sign argument are the simple zero and the two zero-free offset
intervals.  Functional equation, conjugation, branch regularity, and the
reality of `i M'(ρ)` are proved internally. -/
theorem lemma23_actual_dirichlet_coefficient_nonneg_of_branch
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1)
    (ρ : ℂ) (hρre : ρ.re = 1 / 2) (hρim : 0 < ρ.im)
    {b₁ b₂ b₃ : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (Y : ℂ → ℂ)
    (hYcont : ContinuousOn Y UpperHalfPlane.upperHalfPlaneSet)
    (hYsquare : ∀ s ∈ UpperHalfPlane.upperHalfPlaneSet,
      Y s ^ 2 = (lemma23DirichletZ χ s)⁻¹)
    (hLzero : DirichletCharacter.LFunction χ ρ = 0)
    (hLderivNe : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0)
    (hLnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      DirichletCharacter.LFunction χ (criticalLinePoint ρ t) ≠ 0)
    (hLnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      DirichletCharacter.LFunction χ (criticalLinePoint ρ x) ≠ 0) :
    ((lemma23ComplexCoefficient
      (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₁))
      (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₂))
      (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₃))
      (Y ρ * deriv (DirichletCharacter.LFunction χ) ρ)).im = 0) ∧
    0 ≤ (lemma23ComplexCoefficient
      (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₁))
      (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₂))
      (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₃))
      (Y ρ * deriv (DirichletCharacter.LFunction χ) ρ)).re := by
  have hχne : χ ≠ 1 := by
    intro h
    have hprimitive := (DirichletCharacter.isPrimitive_def χ).mp hχ
    rw [h, DirichletCharacter.conductor_one] at hprimitive
    exact hN hprimitive.symm
  let L : ℂ → ℂ := DirichletCharacter.LFunction χ
  let M : ℂ → ℂ := lemma23DirichletNormalizedM χ Y
  have hLdiff : Differentiable ℂ L := by
    simpa [L] using (DirichletCharacter.differentiable_LFunction hχne)
  have hLcont : Continuous L := hLdiff.continuous
  have hMcontU : ContinuousOn M UpperHalfPlane.upperHalfPlaneSet := by
    simpa [M, lemma23DirichletNormalizedM, lemma23NormalizedM, L] using
      continuousOn_lemma23NormalizedM Y (DirichletCharacter.LFunction χ)
        hYcont hLcont.continuousOn
  have himageU :
      criticalLinePoint ρ '' Set.Icc 0 b₃ ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    rintro z ⟨t, ht, rfl⟩
    change 0 < (ρ + Complex.I * (t : ℂ)).im
    have him : (ρ + Complex.I * (t : ℂ)).im = ρ.im + t := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]
    linarith [hρim, ht.1]
  have hMcont : ContinuousOn M
      (criticalLinePoint ρ '' Set.Icc 0 b₃) := hMcontU.mono himageU
  have hZρne : lemma23DirichletZ χ ρ ≠ 0 :=
    lemma23DirichletZ_ne_zero_of_im_pos χ hχ hN hρim
  have hYρne : Y ρ ≠ 0 :=
    lemma23_square_root_ne_zero (hYsquare ρ hρim) hZρne
  have hZderiv : HasDerivAt (lemma23DirichletZ χ)
      (deriv (lemma23DirichletZ χ) ρ) ρ :=
    (lemma23DirichletZ_differentiableAt_of_im_ne_zero χ hρim.ne').hasDerivAt
  have hZinvDeriv := hZderiv.inv hZρne
  have hYderiv :=
    lemma23_hasDerivAt_square_root_on_open UpperHalfPlane.isOpen_upperHalfPlaneSet
      hρim hYcont hYsquare hZinvDeriv (inv_ne_zero hZρne)
  have hLderiv : HasDerivAt L (deriv L ρ) ρ := by
    exact (hLdiff ρ).hasDerivAt
  have hMzero : M ρ = 0 := by
    simp only [M, lemma23DirichletNormalizedM, lemma23NormalizedM]
    rw [hLzero]
    simp
  have hMderiv : HasDerivAt M (Y ρ * deriv L ρ) ρ := by
    simpa [M, lemma23DirichletNormalizedM, lemma23NormalizedM, L] using
      hasDerivAt_lemma23NormalizedM_of_zero Y
        (DirichletCharacter.LFunction χ) hYderiv
        ((hLdiff ρ).hasDerivAt) hLzero
  have hMderivNe : Y ρ * deriv L ρ ≠ 0 := mul_ne_zero hYρne hLderivNe
  have hFE : ∀ t : ℝ,
      L (criticalLinePoint ρ t) =
        lemma23DirichletZ χ (criticalLinePoint ρ t) *
          DirichletCharacter.LFunction χ⁻¹ (1 - criticalLinePoint ρ t) := by
    intro t
    have hsRe : (criticalLinePoint ρ t).re = 1 / 2 := by
      simp [criticalLinePoint, Complex.add_re, Complex.mul_re, hρre]
    have hmirrorRe : (1 - criticalLinePoint ρ t).re = 1 / 2 := by
      rw [Complex.sub_re, Complex.one_re, hsRe]
      norm_num
    exact lemma23_dirichletLFunction_functional_equation χ hχ hN
      (lemma23_gammaFactor_ne_zero_of_re_pos χ (by rw [hsRe]; norm_num))
      (lemma23_gammaFactor_ne_zero_of_re_pos χ⁻¹ (by rw [hmirrorRe]; norm_num))
  have hZnorm : ∀ t : ℝ,
      ‖lemma23DirichletZ χ (criticalLinePoint ρ t)‖ = 1 := by
    intro t
    exact lemma23DirichletZ_norm_eq_one_on_critical_line χ hχ hN (by
      simp [criticalLinePoint, Complex.add_re, Complex.mul_re, hρre])
  have hconj : ∀ t : ℝ,
      DirichletCharacter.LFunction χ⁻¹ (1 - criticalLinePoint ρ t) =
        conj (L (criticalLinePoint ρ t)) := by
    intro t
    simpa [L] using dirichletLFunction_inv_eq_conj_reflection_critical χ
      hχne ρ hρre t
  have hlineReal : ∀ t : ℝ, 0 ≤ t → (M (criticalLinePoint ρ t)).im = 0 := by
    intro t ht
    have him : (criticalLinePoint ρ t).im = ρ.im + t := by
      simp [criticalLinePoint, Complex.add_im, Complex.mul_im]
    have htUpper : criticalLinePoint ρ t ∈ UpperHalfPlane.upperHalfPlaneSet := by
      change 0 < (criticalLinePoint ρ t).im
      rw [him]
      linarith [hρim, ht]
    have hZne := lemma23DirichletZ_ne_zero_of_im_pos χ hχ hN (by
      rw [him]
      linarith [hρim, ht])
    have hfactor : M (criticalLinePoint ρ t) =
        Y (criticalLinePoint ρ t) * L (criticalLinePoint ρ t) := by
      simp [M, lemma23DirichletNormalizedM, lemma23NormalizedM, L]
    have hnormalized := lemma23_normalized_functional_equation hfactor
      (hFE t) (hYsquare (criticalLinePoint ρ t) htUpper) hZne
    have hYnorm := lemma23_Y_norm_eq_one_of_sq_eq_inv
      (hYsquare (criticalLinePoint ρ t) htUpper) (hZnorm t)
    exact lemma23_M_value_real_of_functional_equation hfactor hnormalized
      (hconj t) hYnorm
  have hlineRealRight : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (M (ρ + Complex.I * (t : ℂ))).im = 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    simpa [criticalLinePoint] using hlineReal t ht.le
  have hlineDerivReal := lemma23_vertical_derivative_real_of_line_real_right
    hMderiv hMzero hlineRealRight
  have hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      M (criticalLinePoint ρ t) ≠ 0 := by
    intro t ht ht₁
    have him : (criticalLinePoint ρ t).im = ρ.im + t := by
      simp [criticalLinePoint, Complex.add_im, Complex.mul_im]
    have htUpper : criticalLinePoint ρ t ∈ UpperHalfPlane.upperHalfPlaneSet := by
      change 0 < (criticalLinePoint ρ t).im
      rw [him]
      linarith [hρim, ht]
    have hYne := lemma23_square_root_ne_zero
      (hYsquare (criticalLinePoint ρ t) htUpper)
      (lemma23DirichletZ_ne_zero_of_im_pos χ hχ hN (by rw [him]; linarith [hρim, ht]))
    simpa [M, lemma23DirichletNormalizedM, lemma23NormalizedM, L] using
      (mul_ne_zero hYne (hLnozero₁ ht ht₁))
  have hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      M (criticalLinePoint ρ x) ≠ 0 := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le horder.1 (le_trans horder.2.1 hx.1)
    have him : (criticalLinePoint ρ x).im = ρ.im + x := by
      simp [criticalLinePoint, Complex.add_im, Complex.mul_im]
    have htUpper : criticalLinePoint ρ x ∈ UpperHalfPlane.upperHalfPlaneSet := by
      change 0 < (criticalLinePoint ρ x).im
      rw [him]
      linarith [hρim, hxpos]
    have hYne := lemma23_square_root_ne_zero
      (hYsquare (criticalLinePoint ρ x) htUpper)
      (lemma23DirichletZ_ne_zero_of_im_pos χ hχ hN (by rw [him]; linarith [hρim, hxpos]))
    simpa [M, lemma23DirichletNormalizedM, lemma23NormalizedM, L] using
      (mul_ne_zero hYne (hLnozero₂ x hx))
  have hlineRealIcc : ∀ t ∈ Set.Icc 0 b₃,
      (M (criticalLinePoint ρ t)).im = 0 := by
    intro t ht
    exact hlineReal t ht.1
  exact lemma23_verticalLine_coefficient_nonneg M horder hMcont hMderiv
    hMderivNe hMzero hlineRealIcc hlineDerivReal hnozero₁ hnozero₂

/-- Existential form: the actual analytic square-root branch can be chosen,
and then the coefficient in Zhang's Lemma 2.3 is real and nonnegative under
the zero-spacing conclusions needed from Proposition 2.2. -/
theorem lemma23_actual_dirichlet_coefficient_nonneg
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : DirichletCharacter.IsPrimitive χ) (hN : N ≠ 1)
    (ρ : ℂ) (hρre : ρ.re = 1 / 2) (hρim : 0 < ρ.im)
    {b₁ b₂ b₃ : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (hLzero : DirichletCharacter.LFunction χ ρ = 0)
    (hLderivNe : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0)
    (hLnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      DirichletCharacter.LFunction χ (criticalLinePoint ρ t) ≠ 0)
    (hLnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      DirichletCharacter.LFunction χ (criticalLinePoint ρ x) ≠ 0) :
    ∃ Y : ℂ → ℂ,
      ((lemma23ComplexCoefficient
        (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₁))
        (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₂))
        (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₃))
        (Y ρ * deriv (DirichletCharacter.LFunction χ) ρ)).im = 0) ∧
      0 ≤ (lemma23ComplexCoefficient
        (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₁))
        (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₂))
        (lemma23DirichletNormalizedM χ Y (criticalLinePoint ρ b₃))
        (Y ρ * deriv (DirichletCharacter.LFunction χ) ρ)).re := by
  obtain ⟨Y, hYcont, hYsquare⟩ := lemma23_exists_continuous_actual_square_root χ hχ hN
  exact ⟨Y, lemma23_actual_dirichlet_coefficient_nonneg_of_branch
    χ hχ hN ρ hρre hρim horder Y hYcont hYsquare hLzero hLderivNe
    hLnozero₁ hLnozero₂⟩

end ZhangLS.Spec
