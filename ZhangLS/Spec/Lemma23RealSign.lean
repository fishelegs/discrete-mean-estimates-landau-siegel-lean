import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp

/-!
# Real-variable sign lemmas for Zhang's Lemma 2.3

The proof of Lemma 2.3 reduces to a real-valued continuous function on the
critical line.  This file isolates the two real-analysis steps used there:
nonvanishing on an interval prevents endpoint sign changes, and a positive
right-hand quotient remains nonnegative in the derivative limit.

These are auxiliary results only; they do not yet formalize the arithmetic,
zero-free intervals, or the full complex-valued statement of Lemma 2.3.
-/

namespace ZhangLS.Spec

open scoped Topology
open Filter Set ComplexConjugate

/-- A continuous real function that never vanishes on a closed interval has
endpoint values with the same strict sign.  This packages the sign-change
contrapositive (an endpoint sign change would produce a zero by IVT). -/
theorem endpoint_mul_pos_of_continuousOn_nonzero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hnonzero : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    0 < f a * f b := by
  have hfa : f a ≠ 0 := hnonzero a ⟨le_rfl, hab⟩
  have hfb : f b ≠ 0 := hnonzero b ⟨hab, le_rfl⟩
  rcases lt_or_gt_of_ne hfa with hfa | hfa
  · have hfb' : f b < 0 := by
      rcases lt_or_gt_of_ne hfb with hfb | hfb
      · exact hfb
      · have hzeroMem : 0 ∈ Set.Icc (f a) (f b) := ⟨hfa.le, hfb.le⟩
        obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hf hzeroMem
        exfalso
        exact (hnonzero x hx) (by simpa using hfx)
    exact mul_pos_of_neg_of_neg hfa hfb'
  · have hfb' : 0 < f b := by
      rcases lt_or_gt_of_ne hfb with hfb | hfb
      · have hzeroMem : 0 ∈ Set.Icc (f b) (f a) := ⟨hfb.le, hfa.le⟩
        obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hf hzeroMem
        exfalso
        exact (hnonzero x hx) (by simpa using hfx)
      · exact hfb
    exact mul_pos hfa hfb'

/-- Under the same no-zero hypothesis, the quotient of the endpoint values is
positive.  The interval orientation gives the form needed for `[t,a]` in the
one-sided argument: `f b / f a > 0`. -/
theorem endpoint_div_pos_of_continuousOn_nonzero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hnonzero : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    0 < f b / f a := by
  have hmul := endpoint_mul_pos_of_continuousOn_nonzero hab hf hnonzero
  have hfa : f a ≠ 0 := hnonzero a ⟨le_rfl, hab⟩
  have hsq : 0 < f a * f a := by
    simpa [pow_two] using sq_pos_of_ne_zero hfa
  have hquot : 0 < (f a * f b) / (f a * f a) := div_pos hmul hsq
  have heq : f b / f a = (f a * f b) / (f a * f a) := by
    field_simp [hfa]
  rw [heq]
  exact hquot

/-- If the quotients `f a / f t` stay positive immediately to the right of a
simple zero at `0`, their derivative-limit quotient cannot be negative.

This is the real one-sided limit/sign step in Zhang's proof of Lemma 2.3. -/
theorem derivative_ratio_nonneg_of_nonzero_right_interval
    (f : ℝ → ℝ) {a d : ℝ} (ha : 0 < a) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (Set.Icc 0 a))
    (hderiv : HasDerivAt f d 0) (hd : d ≠ 0)
    (hnonzero : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ a → f t ≠ 0) :
    0 ≤ f a / d := by
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * f t) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa [hf0, smul_eq_mul] using hderiv.tendsto_slope_zero_right
  have hlimit : Tendsto (fun t : ℝ => f a / (t⁻¹ * f t))
      (𝓝[>] (0 : ℝ)) (𝓝 (f a / d)) := by
    simpa using tendsto_const_nhds.div hslope hd
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < a := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds ha] with t ht _
    exact ht
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 < f a / (t⁻¹ * f t) := by
    filter_upwards [hsmall, eventually_mem_nhdsWithin] with t hta ht
    have htpos : 0 < t := ht
    have hquot : 0 < f a / f t := by
      apply endpoint_div_pos_of_continuousOn_nonzero (f := f) (a := t) (b := a)
        hta.le
      · exact hf.mono (by
          intro x hx
          exact ⟨(le_of_lt htpos).trans hx.1, hx.2⟩)
      · intro x hx
        exact hnonzero (htpos.trans_le hx.1) hx.2
    have hft : f t ≠ 0 := by
      intro hzero
      simp [hzero] at hquot
    have heq : f a / (t⁻¹ * f t) = t * (f a / f t) := by
      field_simp [ne_of_gt htpos, hft]
    rw [heq]
    exact mul_pos htpos hquot
  have hnonnegEventually : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      f a / (t⁻¹ * f t) ∈ Set.Ici (0 : ℝ) :=
    hpositive.mono (fun _ ht => ht.le)
  have hnonneg : f a / d ∈ Set.Ici (0 : ℝ) :=
    isClosed_Ici.mem_of_tendsto hlimit hnonnegEventually
  exact hnonneg

/-- The real sign core of Lemma 2.3.

For ordered positive offsets `b₁ ≤ b₂ ≤ b₃`, assume there are no zeros on
`(0,b₁]` and `[b₂,b₃]`.  The derivative quotient at the simple zero is
nonnegative, the two later values have positive product, and hence the real
coefficient corresponding to Zhang's `𝓒*` is nonnegative.  The analytic
construction of the critical-line function and the zero-free interval facts
are deliberately left as inputs for the next formalization step. -/
theorem lemma23_real_sign_core
    (f : ℝ → ℝ) {b₁ b₂ b₃ d : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (hf0 : f 0 = 0)
    (hf : ContinuousOn f (Set.Icc 0 b₃))
    (hderiv : HasDerivAt f d 0) (hd : d ≠ 0)
    (hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ → f t ≠ 0)
    (hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃, f x ≠ 0) :
    0 ≤ (f b₁ / d) * (f b₂ * f b₃) := by
  rcases horder with ⟨hb₁, hb₁₂, hb₂₃⟩
  have hb₁₃ : b₁ ≤ b₃ := le_trans hb₁₂ hb₂₃
  have hcont₁ : ContinuousOn f (Set.Icc 0 b₁) :=
    hf.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hb₁₃⟩)
  have hderivSign := derivative_ratio_nonneg_of_nonzero_right_interval
    (f := f) hb₁ hf0 hcont₁ hderiv hd hnozero₁
  have hcont₂ : ContinuousOn f (Set.Icc b₂ b₃) := hf.mono (by
    intro x hx
    exact ⟨(le_trans hb₁.le (le_trans hb₁₂ hx.1)), hx.2⟩)
  have htailSign := endpoint_mul_pos_of_continuousOn_nonzero hb₂₃ hcont₂ hnozero₂
  exact mul_nonneg hderivSign htailSign.le

/-- Zhang's complex coefficient in the notation of Lemma 2.3. -/
noncomputable def lemma23ComplexCoefficient (m₁ m₂ m₃ mDeriv : ℂ) : ℂ :=
  -Complex.I * m₁ * m₂ * m₃ / mDeriv

/-- When the three critical-line values are real and `i M'(ρ)` is the real
derivative along the line, the complex expression `𝓒*` is exactly the real
factorization used by `lemma23_real_sign_core`. -/
theorem lemma23_complex_coefficient_eq_real
    {r₁ r₂ r₃ d : ℝ} {m₁ m₂ m₃ mDeriv : ℂ}
    (hm₁ : m₁ = (r₁ : ℂ)) (hm₂ : m₂ = (r₂ : ℂ)) (hm₃ : m₃ = (r₃ : ℂ))
    (hlineDeriv : Complex.I * mDeriv = (d : ℂ)) (hd : d ≠ 0) :
    lemma23ComplexCoefficient m₁ m₂ m₃ mDeriv =
      (((r₁ / d) * (r₂ * r₃)) : ℂ) := by
  have hmDeriv : mDeriv ≠ 0 := by
    intro hzero
    rw [hzero] at hlineDeriv
    simp at hlineDeriv
    exact hd (Complex.ofReal_eq_zero.mp hlineDeriv.symm)
  have hderivRewrite : mDeriv = -Complex.I * (d : ℂ) := by
    calc
      mDeriv = ((-Complex.I) * Complex.I) * mDeriv := by simp
      _ = (-Complex.I) * (Complex.I * mDeriv) := by rw [← mul_assoc]
      _ = -Complex.I * (d : ℂ) := by rw [hlineDeriv]
  have hcomplex : lemma23ComplexCoefficient m₁ m₂ m₃ mDeriv =
      (((r₁ / d) * (r₂ * r₃)) : ℝ) := by
    rw [lemma23ComplexCoefficient, hm₁, hm₂, hm₃, hderivRewrite]
    push_cast
    field_simp [hd, hmDeriv]
  simpa using hcomplex

/-- The preceding equality also records explicitly that the complex
coefficient is real. -/
theorem lemma23_complex_coefficient_re_eq_real
    {r₁ r₂ r₃ d : ℝ} {m₁ m₂ m₃ mDeriv : ℂ}
    (hm₁ : m₁ = (r₁ : ℂ)) (hm₂ : m₂ = (r₂ : ℂ)) (hm₃ : m₃ = (r₃ : ℂ))
    (hlineDeriv : Complex.I * mDeriv = (d : ℂ)) (hd : d ≠ 0) :
    (lemma23ComplexCoefficient m₁ m₂ m₃ mDeriv).re =
      (r₁ / d) * (r₂ * r₃) := by
  rw [lemma23_complex_coefficient_eq_real hm₁ hm₂ hm₃ hlineDeriv hd]
  simp

/-- Conditional complex form of Lemma 2.3: once the analytic construction
identifies the critical-line values with a real function and identifies
`i M'(ρ)` with its real derivative, the real sign core proves `𝓒* ≥ 0`. -/
theorem lemma23_complex_coefficient_nonneg
    (f : ℝ → ℝ) {b₁ b₂ b₃ d : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (hf0 : f 0 = 0)
    (hf : ContinuousOn f (Set.Icc 0 b₃))
    (hderiv : HasDerivAt f d 0) (hd : d ≠ 0)
    (hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ → f t ≠ 0)
    (hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃, f x ≠ 0)
    {m₁ m₂ m₃ mDeriv : ℂ}
    (hm₁ : m₁ = (f b₁ : ℂ)) (hm₂ : m₂ = (f b₂ : ℂ))
    (hm₃ : m₃ = (f b₃ : ℂ))
    (hlineDeriv : Complex.I * mDeriv = (d : ℂ)) :
    0 ≤ (lemma23ComplexCoefficient m₁ m₂ m₃ mDeriv).re := by
  have hreal := lemma23_real_sign_core f horder hf0 hf hderiv hd hnozero₁ hnozero₂
  rw [lemma23_complex_coefficient_re_eq_real hm₁ hm₂ hm₃ hlineDeriv hd]
  exact hreal

/-- The point on the vertical line through `ρ` with real offset `t`. -/
noncomputable def criticalLinePoint (ρ : ℂ) (t : ℝ) : ℂ :=
  ρ + Complex.I * (t : ℂ)

/-- The real-valued function obtained by restricting a complex function to a
vertical line and taking its real part. -/
noncomputable def criticalLineRealPart (M : ℂ → ℂ) (ρ : ℂ) (t : ℝ) : ℝ :=
  (M (criticalLinePoint ρ t)).re

/-- A complex number with zero imaginary part is the real cast of its real
part. -/
theorem complex_eq_real_of_im_zero (z : ℂ) (hreal : z.im = 0) :
    z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hreal]

/-- A value known to be real on the vertical line is exactly the cast of the
real-part restriction. -/
theorem criticalLineValue_eq_realCast
    (M : ℂ → ℂ) (ρ : ℂ) (t : ℝ)
    (hreal : (M (ρ + Complex.I * (t : ℂ))).im = 0) :
    M (ρ + Complex.I * (t : ℂ)) = (criticalLineRealPart M ρ t : ℂ) := by
  exact complex_eq_real_of_im_zero _ hreal

/-- Continuity of the real-part restriction follows from continuity of `M`. -/
theorem continuousOn_criticalLineRealPart
    (M : ℂ → ℂ) (ρ : ℂ) {s : Set ℝ}
    (hM : ContinuousOn M (criticalLinePoint ρ '' s)) :
    ContinuousOn (criticalLineRealPart M ρ) s := by
  have hpath : ContinuousOn (criticalLinePoint ρ) s := by
    change ContinuousOn (fun t : ℝ => ρ + Complex.I * (t : ℂ)) s
    exact (continuous_const.add
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  have hcomp : ContinuousOn (fun t : ℝ => M (criticalLinePoint ρ t)) s :=
    hM.comp hpath (by
      intro t ht
      exact ⟨t, ht, rfl⟩)
  exact Complex.continuous_re.comp_continuousOn hcomp

/-- The derivative of the real-part restriction in the vertical direction is
`Re(i M'(ρ))`.  This is the chain-rule bridge used to interpret (2.12) as a
real derivative. -/
theorem hasDerivAt_criticalLineRealPart
    {M : ℂ → ℂ} {ρ mDeriv : ℂ} (hM : HasDerivAt M mDeriv ρ) :
    HasDerivAt (criticalLineRealPart M ρ)
      (Complex.re (Complex.I * mDeriv)) 0 := by
  let lineArg : ℂ → ℂ := fun z => ρ + Complex.I * z
  have hlineArg : HasDerivAt lineArg Complex.I 0 := by
    have hbase : HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
    simpa [lineArg] using hbase.const_add ρ
  have hM' : HasDerivAt M mDeriv (lineArg 0) := by
    simpa [lineArg] using hM
  have hline : HasDerivAt (M ∘ lineArg) (mDeriv * Complex.I) 0 := by
    exact hM'.comp 0 hlineArg
  have hreal := HasDerivAt.real_of_complex (z := 0) hline
  simpa [criticalLineRealPart, lineArg, Function.comp_def, mul_comm] using hreal

/-- On a vertical line, the derivative of the imaginary part is the imaginary
part of `i M'`.  This is the companion to
`hasDerivAt_criticalLineRealPart`. -/
theorem hasDerivAt_criticalLineImagPart
    {M : ℂ → ℂ} {ρ mDeriv : ℂ} (hM : HasDerivAt M mDeriv ρ) :
    HasDerivAt (fun t : ℝ => (M (ρ + Complex.I * (t : ℂ))).im)
      (Complex.im (Complex.I * mDeriv)) 0 := by
  let lineArg : ℂ → ℂ := fun z => ρ + Complex.I * z
  have hlineArg : HasDerivAt lineArg Complex.I 0 := by
    have hbase : HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
    simpa [lineArg] using hbase.const_add ρ
  have hM' : HasDerivAt M mDeriv (lineArg 0) := by
    simpa [lineArg] using hM
  have hline : HasDerivAt (M ∘ lineArg) (mDeriv * Complex.I) 0 := by
    exact hM'.comp 0 hlineArg
  have hscaled : HasDerivAt (fun z : ℂ => -Complex.I * (M ∘ lineArg) z)
      ((-Complex.I) * (mDeriv * Complex.I)) 0 := by
    simpa [Function.comp_def] using hline.const_mul (-Complex.I)
  have hreal := HasDerivAt.real_of_complex hscaled
  have hderiv : ((-Complex.I) * (mDeriv * Complex.I)).re =
      (Complex.I * mDeriv).im := by
    rw [show (-Complex.I) * (mDeriv * Complex.I) =
      -(Complex.I ^ 2 * mDeriv) by ring, Complex.I_sq]
    simp
  simpa [lineArg, Function.comp_def, Complex.mul_re, hderiv] using hreal

/-- If `M` is real-valued on the vertical line in a neighborhood of the zero,
then the vertical derivative `i M'` is real.  Thus the derivative-reality
claim (2.12) follows from (2.11) plus complex differentiability; it need not be
an independent analytic input. -/
theorem lemma23_vertical_derivative_real_of_line_real_near
    {M : ℂ → ℂ} {ρ mDeriv : ℂ} (hM : HasDerivAt M mDeriv ρ)
    (hlineReal : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (M (ρ + Complex.I * (t : ℂ))).im = 0) :
    (Complex.I * mDeriv).im = 0 := by
  have him := hasDerivAt_criticalLineImagPart hM
  have hzero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (M (ρ + Complex.I * (t : ℂ))).im) := by
    filter_upwards [hlineReal] with t ht
    exact ht.symm
  have hconst : HasDerivAt
      (fun t : ℝ => (M (ρ + Complex.I * (t : ℂ))).im) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero.symm
  exact him.unique hconst

/-- A unit-modulus complex number has conjugate equal to its inverse. -/
theorem lemma23_conj_eq_inv_of_norm_eq_one {y : ℂ} (hy : ‖y‖ = 1) :
    conj y = y⁻¹ := by
  have hyne : y ≠ 0 := by
    intro hy0
    simp [hy0] at hy
  have hprod : conj y * y = (1 : ℂ) := by
    calc
      conj y * y = (Complex.normSq y : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      _ = ((‖y‖ : ℂ) ^ 2) := by exact_mod_cast Complex.normSq_eq_norm_sq y
      _ = 1 := by simp [hy]
  calc
    conj y = conj y * 1 := by simp
    _ = conj y * (y * y⁻¹) := by rw [mul_inv_cancel₀ hyne]
    _ = (conj y * y) * y⁻¹ := by ring
    _ = y⁻¹ := by rw [hprod]; simp

/-- Pointwise algebraic realness of Zhang's normalized L-function.  The four
inputs are precisely the factorization `M=YL`, functional equation
`M=Y⁻¹ L̄(1-s)`, conjugation symmetry of the L-functions, and `|Y|=1`. -/
theorem lemma23_M_value_real_of_functional_equation
    {m y l lbar : ℂ}
    (hm : m = y * l)
    (hfe : m = y⁻¹ * lbar)
    (hconj : lbar = conj l)
    (hy : ‖y‖ = 1) :
    m.im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    conj m = conj (y * l) := congrArg conj hm
    _ = conj y * conj l := map_mul conj y l
    _ = y⁻¹ * lbar := by rw [lemma23_conj_eq_inv_of_norm_eq_one hy, hconj]
    _ = m := hfe.symm

/-- The paper's normalized L-function `M=YL`. -/
def lemma23NormalizedM (Y L : ℂ → ℂ) (s : ℂ) : ℂ := Y s * L s

/-- Continuity of `M` follows from continuity of its two factors. -/
theorem continuousOn_lemma23NormalizedM (Y L : ℂ → ℂ) {U : Set ℂ}
    (hY : ContinuousOn Y U) (hL : ContinuousOn L U) :
    ContinuousOn (lemma23NormalizedM Y L) U := by
  simpa [lemma23NormalizedM] using hY.mul hL

/-- At a zero of `L`, the normalized function has derivative `Y(ρ)L'(ρ)`;
the derivative of the square-root factor drops out. -/
theorem hasDerivAt_lemma23NormalizedM_of_zero
    (Y L : ℂ → ℂ) {ρ yDeriv lDeriv : ℂ}
    (hY : HasDerivAt Y yDeriv ρ) (hL : HasDerivAt L lDeriv ρ)
    (hLzero : L ρ = 0) :
    HasDerivAt (lemma23NormalizedM Y L) (Y ρ * lDeriv) ρ := by
  simpa [lemma23NormalizedM, hLzero] using hY.mul hL

/-- A nonzero normalization factor preserves nonvanishing of the L-function. -/
theorem lemma23NormalizedM_ne_zero
    (Y L : ℂ → ℂ) {s : ℂ} (hY : Y s ≠ 0) (hL : L s ≠ 0) :
    lemma23NormalizedM Y L s ≠ 0 := by
  exact mul_ne_zero hY hL

/-- If `Y` is nonzero, then `M=YL` and `L` have exactly the same zeros. -/
theorem lemma23NormalizedM_ne_zero_iff
    (Y L : ℂ → ℂ) {s : ℂ} (hY : Y s ≠ 0) :
    lemma23NormalizedM Y L s ≠ 0 ↔ L s ≠ 0 := by
  simp [lemma23NormalizedM, hY]

/-- The square-root normalization turns the original functional equation
`L(s)=Z(s)L̄(1-s)` into the normalized equation for `M=YL`. -/
theorem lemma23_normalized_functional_equation
    {m y l lbar z : ℂ}
    (hm : m = y * l)
    (hLfe : l = z * lbar)
    (hYsq : y ^ 2 = z⁻¹)
    (hz : z ≠ 0) :
    m = y⁻¹ * lbar := by
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hYsq
    have hzero : z⁻¹ = 0 := by simpa using hYsq.symm
    exact (inv_ne_zero hz) hzero
  have hzinv : z = (y ^ 2)⁻¹ := by
    calc
      z = (z⁻¹)⁻¹ := by simp
      _ = (y ^ 2)⁻¹ := by rw [← hYsq]
  have hyz : y * z = y⁻¹ := by
    rw [hzinv]
    field_simp [hy]
  calc
    m = y * l := hm
    _ = y * (z * lbar) := by rw [hLfe]
    _ = (y * z) * lbar := by ring
    _ = y⁻¹ * lbar := by rw [hyz]

/-- If `Y²=Z⁻¹` and `|Z|=1`, then the chosen square root has unit modulus. -/
theorem lemma23_Y_norm_eq_one_of_sq_eq_inv
    {y z : ℂ} (hYsq : y ^ 2 = z⁻¹) (hz : ‖z‖ = 1) :
    ‖y‖ = 1 := by
  have hyNormSq : ‖y‖ ^ 2 = 1 := by
    calc
      ‖y‖ ^ 2 = ‖y ^ 2‖ := by rw [norm_pow]
      _ = ‖z⁻¹‖ := by rw [hYsq]
      _ = 1 := by simp [hz]
  nlinarith [norm_nonneg y]

/-- A continuous choice of square root of a differentiable function is itself
differentiable at every point where the chosen root is nonzero.  This supplies
the local analytic step needed to use a topological branch in `M=YL`. -/
theorem hasDerivAt_lemma23_square_root_of_continuity
    {Y G : ℂ → ℂ} {a gDeriv : ℂ}
    (hYcont : ContinuousAt Y a)
    (hYsq : ∀ z : ℂ, Y z ^ 2 = G z)
    (hYne : Y a ≠ 0)
    (hG : HasDerivAt G gDeriv a) :
    HasDerivAt Y (gDeriv / (2 * Y a)) a := by
  have hYtendsto : Tendsto Y (𝓝[≠] a) (𝓝 (Y a)) :=
    hYcont.tendsto.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun z : ℂ => Y z + Y a) (𝓝[≠] a)
      (𝓝 (2 * Y a)) := by
    simpa [two_mul] using hYtendsto.add tendsto_const_nhds
  have hdenNe : 2 * Y a ≠ 0 := by
    exact mul_ne_zero (by norm_num) hYne
  have hdenEventuallyNe : ∀ᶠ z : ℂ in 𝓝[≠] a, Y z + Y a ≠ 0 :=
    hden.eventually_ne hdenNe
  have hquotient : Tendsto
      (fun z : ℂ => slope G a z / (Y z + Y a)) (𝓝[≠] a)
      (𝓝 (gDeriv / (2 * Y a))) :=
    hG.tendsto_slope.div hden hdenNe
  have hzNe : ∀ᶠ z : ℂ in 𝓝[≠] a, z ≠ a := by
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    exact hz
  have hslopes : (fun z : ℂ => slope Y a z) =ᶠ[𝓝[≠] a]
      (fun z : ℂ => slope G a z / (Y z + Y a)) := by
    filter_upwards [hzNe, hdenEventuallyNe] with z hza hsum
    rw [slope_def_field, slope_def_field, ← hYsq z, ← hYsq a]
    field_simp [sub_ne_zero.mpr hza, hsum]
    ring
  apply (hasDerivAt_iff_tendsto_slope).2
  exact Tendsto.congr' hslopes.symm hquotient

/-- On an open simply connected domain, a continuous nonvanishing factor `Z`
admits a continuous square-root branch of `Z⁻¹`.  Mathlib supplies the
topological branch; analytic regularity is a separate local step. -/
theorem exists_continuousOn_lemma23_square_root_inverse
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (Z : ℂ → ℂ) (hZcont : ContinuousOn Z U)
    (hZne : ∀ s ∈ U, Z s ≠ 0) :
    ∃ Y : ℂ → ℂ, ContinuousOn Y U ∧
      ∀ s ∈ U, Y s ^ 2 = (Z s)⁻¹ := by
  have hInv : ContinuousOn (fun s : ℂ => (Z s)⁻¹) U := hZcont.inv₀ hZne
  have hInvNe : ∀ s ∈ U, (Z s)⁻¹ ≠ 0 := fun s hs => inv_ne_zero (hZne s hs)
  have hnozero : 0 ∉ (fun s : ℂ => (Z s)⁻¹) '' U := by
    intro hmem
    rcases hmem with ⟨s, hs, hzero⟩
    exact hInvNe s hs hzero
  obtain ⟨Y, hYcont, hYpow⟩ :=
    Complex.exists_continuousOn_pow_eq hUc hUo hInv hnozero
      (n := 2) (by norm_num)
  exact ⟨Y, hYcont, fun s hs => hYpow s⟩

/-- A square-root branch of the inverse of a nonzero function never vanishes. -/
theorem lemma23_square_root_ne_zero {y z : ℂ}
    (hYsq : y ^ 2 = z⁻¹) (hz : z ≠ 0) : y ≠ 0 := by
  intro hy
  rw [hy] at hYsq
  have hzero : z⁻¹ = 0 := by simpa using hYsq.symm
  exact (inv_ne_zero hz) hzero

/-- At a simple zero of `L`, the continuous square-root normalization has a
derivative and the product `M=YL` inherits the simple-zero derivative. -/
theorem hasDerivAt_lemma23NormalizedM_of_square_root
    {U : Set ℂ} (hUopen : IsOpen U) (Y Z L : ℂ → ℂ) {ρ zDer lDeriv : ℂ}
    (hρ : ρ ∈ U) (hYcont : ContinuousOn Y U)
    (hYsquare : ∀ s : ℂ, Y s ^ 2 = (Z s)⁻¹)
    (hZ : HasDerivAt Z zDer ρ) (hZne : Z ρ ≠ 0)
    (hL : HasDerivAt L lDeriv ρ) (hLzero : L ρ = 0) :
    HasDerivAt (lemma23NormalizedM Y L) (Y ρ * lDeriv) ρ := by
  have hYne : Y ρ ≠ 0 := lemma23_square_root_ne_zero (hYsquare ρ) hZne
  have hYderiv := hasDerivAt_lemma23_square_root_of_continuity
    (hYcont.continuousAt (hUopen.mem_nhds hρ)) hYsquare hYne (hZ.inv hZne)
  exact hasDerivAt_lemma23NormalizedM_of_zero Y L hYderiv hL hLzero

/-- Functional-equation hypotheses imply that the normalized function is
real-valued along the chosen vertical line.  In a concrete application,
`hconj` is the conjugation law for Dirichlet L-functions, while `hfe` is the
paper's equation (2.2) after taking the square-root normalization. -/
theorem lemma23_M_real_on_critical_line
    (M Y L Lbar : ℂ → ℂ) (ρ : ℂ)
    (hfactor : ∀ s : ℂ, M s = Y s * L s)
    (hfunctional : ∀ s : ℂ, M s = (Y s)⁻¹ * Lbar (1 - s))
    (hconj : ∀ t : ℝ,
      Lbar (1 - (ρ + Complex.I * (t : ℂ))) =
      conj (L (ρ + Complex.I * (t : ℂ))))
    (hYnorm : ∀ t : ℝ, ‖Y (ρ + Complex.I * (t : ℂ))‖ = 1) :
    ∀ t : ℝ, (M (ρ + Complex.I * (t : ℂ))).im = 0 := by
  intro t
  exact lemma23_M_value_real_of_functional_equation
    (hfactor (ρ + Complex.I * (t : ℂ)))
    (hfunctional (ρ + Complex.I * (t : ℂ)))
    (hconj t) (hYnorm t)

/-- The paper's raw functional equation and square-root definition imply the
critical-line reality of `M`.  This derives both the normalized equation and
the unit-modulus property of `Y` from `L=ZL̄` and `Y²=Z⁻¹`. -/
theorem lemma23_M_real_on_critical_line_of_square_root
    (M Y L Lbar Z : ℂ → ℂ) (ρ : ℂ)
    (hfactor : ∀ t : ℝ,
      M (ρ + Complex.I * (t : ℂ)) =
        Y (ρ + Complex.I * (t : ℂ)) * L (ρ + Complex.I * (t : ℂ)))
    (hLfunctional : ∀ t : ℝ,
      L (ρ + Complex.I * (t : ℂ)) =
        Z (ρ + Complex.I * (t : ℂ)) * Lbar (1 - (ρ + Complex.I * (t : ℂ))))
    (hYsquare : ∀ t : ℝ,
      (Y (ρ + Complex.I * (t : ℂ))) ^ 2 =
        (Z (ρ + Complex.I * (t : ℂ)))⁻¹)
    (hZnorm : ∀ t : ℝ, ‖Z (ρ + Complex.I * (t : ℂ))‖ = 1)
    (hconj : ∀ t : ℝ,
      Lbar (1 - (ρ + Complex.I * (t : ℂ))) =
        conj (L (ρ + Complex.I * (t : ℂ)))) :
    ∀ t : ℝ, (M (ρ + Complex.I * (t : ℂ))).im = 0 := by
  intro t
  have hnorm := hZnorm t
  have hz : Z (ρ + Complex.I * (t : ℂ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    norm_num at hnorm
  have hfunctional := lemma23_normalized_functional_equation
    (hfactor t) (hLfunctional t) (hYsquare t) hz
  have hYnorm := lemma23_Y_norm_eq_one_of_sq_eq_inv (hYsquare t) (hZnorm t)
  exact lemma23_M_value_real_of_functional_equation (hfactor t)
    hfunctional (hconj t) hYnorm

/-- Conditional application of the real sign core to a complex function on a
vertical line.  The remaining analytic obligations are explicit: `M` must be
continuous, real-valued on the line, have a simple zero at `ρ`, and have no
other zeros on the two offset intervals. -/
theorem lemma23_verticalLine_coefficient_nonneg
    (M : ℂ → ℂ) {ρ mDeriv : ℂ} {b₁ b₂ b₃ : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (hMcont : ContinuousOn M
      (criticalLinePoint ρ '' Set.Icc 0 b₃))
    (hMderiv : HasDerivAt M mDeriv ρ) (hMderivNe : mDeriv ≠ 0)
    (hMzero : M ρ = 0)
    (hlineReal : ∀ t ∈ Set.Icc 0 b₃,
      (M (ρ + Complex.I * (t : ℂ))).im = 0)
    (hlineDerivReal : (Complex.I * mDeriv).im = 0)
    (hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      M (criticalLinePoint ρ t) ≠ 0)
    (hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      M (criticalLinePoint ρ x) ≠ 0) :
    ((lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).im = 0) ∧
    0 ≤ (lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).re := by
  rcases horder with ⟨hb₁pos, hb₁₂, hb₂₃⟩
  have hb₁₃ : b₁ ≤ b₃ := le_trans hb₁₂ hb₂₃
  have hb₁mem : b₁ ∈ Set.Icc 0 b₃ := ⟨hb₁pos.le, hb₁₃⟩
  have hb₂mem : b₂ ∈ Set.Icc 0 b₃ :=
    ⟨le_trans hb₁pos.le hb₁₂, hb₂₃⟩
  have hb₃mem : b₃ ∈ Set.Icc 0 b₃ := ⟨le_trans hb₁pos.le hb₁₃, le_rfl⟩
  let f : ℝ → ℝ := criticalLineRealPart M ρ
  let d : ℝ := (Complex.I * mDeriv).re
  have hf0 : f 0 = 0 := by
    simp [f, criticalLineRealPart, criticalLinePoint, hMzero]
  have hfcont : ContinuousOn f (Set.Icc 0 b₃) := by
    exact continuousOn_criticalLineRealPart M ρ hMcont
  have hfderiv : HasDerivAt f d 0 := by
    simpa [f, d] using hasDerivAt_criticalLineRealPart hMderiv
  have hd : d ≠ 0 := by
    intro hd0
    have hcomplex : Complex.I * mDeriv = (d : ℂ) :=
      complex_eq_real_of_im_zero _ hlineDerivReal
    have hmulzero : Complex.I * mDeriv = 0 := by
      simpa [d, hd0] using hcomplex
    exact hMderivNe (mul_left_cancel₀ Complex.I_ne_zero (by simpa using hmulzero))
  have hm₁ : M (ρ + Complex.I * (b₁ : ℂ)) = (f b₁ : ℂ) := by
    simpa [f, criticalLineRealPart, criticalLinePoint] using
      criticalLineValue_eq_realCast M ρ b₁ (hlineReal b₁ hb₁mem)
  have hm₂ : M (ρ + Complex.I * (b₂ : ℂ)) = (f b₂ : ℂ) := by
    simpa [f, criticalLineRealPart, criticalLinePoint] using
      criticalLineValue_eq_realCast M ρ b₂ (hlineReal b₂ hb₂mem)
  have hm₃ : M (ρ + Complex.I * (b₃ : ℂ)) = (f b₃ : ℂ) := by
    simpa [f, criticalLineRealPart, criticalLinePoint] using
      criticalLineValue_eq_realCast M ρ b₃ (hlineReal b₃ hb₃mem)
  have hnozero₁_real : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ → f t ≠ 0 := by
    intro t ht ht₁ hft
    have htmem : t ∈ Set.Icc 0 b₃ := ⟨ht.le, le_trans ht₁ hb₁₃⟩
    have hvalue : M (criticalLinePoint ρ t) = (f t : ℂ) := by
      simpa [f, criticalLineRealPart, criticalLinePoint] using
        criticalLineValue_eq_realCast M ρ t (hlineReal t htmem)
    have hzero : M (criticalLinePoint ρ t) = 0 := by
      rw [hvalue]
      simp [hft]
    exact hnozero₁ ht ht₁ hzero
  have hnozero₂_real : ∀ x ∈ Set.Icc b₂ b₃, f x ≠ 0 := by
    intro x hx hfx
    have hxmem : x ∈ Set.Icc 0 b₃ :=
      ⟨le_trans hb₁pos.le (le_trans hb₁₂ hx.1), hx.2⟩
    have hvalue : M (criticalLinePoint ρ x) = (f x : ℂ) := by
      simpa [f, criticalLineRealPart, criticalLinePoint] using
        criticalLineValue_eq_realCast M ρ x (hlineReal x hxmem)
    have hzero : M (criticalLinePoint ρ x) = 0 := by
      rw [hvalue]
      simp [hfx]
    exact hnozero₂ x hx hzero
  have hlineDeriv : Complex.I * mDeriv = (d : ℂ) :=
    complex_eq_real_of_im_zero _ hlineDerivReal
  have hrealSign := lemma23_real_sign_core f ⟨hb₁pos, hb₁₂, hb₂₃⟩ hf0 hfcont hfderiv hd
    hnozero₁_real hnozero₂_real
  constructor
  · rw [lemma23_complex_coefficient_eq_real hm₁ hm₂ hm₃ hlineDeriv hd]
    simp
  · rw [lemma23_complex_coefficient_re_eq_real hm₁ hm₂ hm₃ hlineDeriv hd]
    exact hrealSign

/-- Lemma 2.3's vertical-line sign theorem with the reality claims derived
from the functional equation instead of supplied separately.  Only the
zero-free intervals and the normalized functional-equation identities remain
as application-specific hypotheses. -/
theorem lemma23_verticalLine_coefficient_nonneg_of_functional_equation
    (M Y L Lbar : ℂ → ℂ) {ρ mDeriv : ℂ} {b₁ b₂ b₃ : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (hMcont : ContinuousOn M
      (criticalLinePoint ρ '' Set.Icc 0 b₃))
    (hMderiv : HasDerivAt M mDeriv ρ) (hMderivNe : mDeriv ≠ 0)
    (hMzero : M ρ = 0)
    (hfactor : ∀ s : ℂ, M s = Y s * L s)
    (hfunctional : ∀ s : ℂ, M s = (Y s)⁻¹ * Lbar (1 - s))
    (hconj : ∀ t : ℝ,
      Lbar (1 - (ρ + Complex.I * (t : ℂ))) =
        conj (L (ρ + Complex.I * (t : ℂ))))
    (hYnorm : ∀ t : ℝ, ‖Y (ρ + Complex.I * (t : ℂ))‖ = 1)
    (hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      M (criticalLinePoint ρ t) ≠ 0)
    (hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      M (criticalLinePoint ρ x) ≠ 0) :
    ((lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).im = 0) ∧
    0 ≤ (lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).re := by
  have hlineReal := lemma23_M_real_on_critical_line M Y L Lbar ρ
    hfactor hfunctional hconj hYnorm
  have hlineDerivReal :=
    lemma23_vertical_derivative_real_of_line_real_near hMderiv
      (Filter.Eventually.of_forall hlineReal)
  exact lemma23_verticalLine_coefficient_nonneg M horder hMcont hMderiv
    hMderivNe hMzero (fun t _ => hlineReal t) hlineDerivReal hnozero₁ hnozero₂

/-- A more literal interface for the paper's construction `M=YL`, `Y²=Z⁻¹`:
starting from the unnormalized functional equation and unit modulus of `Z` on
the line, Lean derives both (2.11) and (2.12), then proves the coefficient
nonnegative once the two zero-free intervals are supplied. -/
theorem lemma23_verticalLine_coefficient_nonneg_of_square_root
    (M Y L Lbar Z : ℂ → ℂ) {ρ mDeriv : ℂ} {b₁ b₂ b₃ : ℝ}
    (horder : 0 < b₁ ∧ b₁ ≤ b₂ ∧ b₂ ≤ b₃)
    (hMcont : ContinuousOn M
      (criticalLinePoint ρ '' Set.Icc 0 b₃))
    (hMderiv : HasDerivAt M mDeriv ρ) (hMderivNe : mDeriv ≠ 0)
    (hMzero : M ρ = 0)
    (hfactor : ∀ t : ℝ,
      M (ρ + Complex.I * (t : ℂ)) =
        Y (ρ + Complex.I * (t : ℂ)) * L (ρ + Complex.I * (t : ℂ)))
    (hLfunctional : ∀ t : ℝ,
      L (ρ + Complex.I * (t : ℂ)) =
        Z (ρ + Complex.I * (t : ℂ)) * Lbar (1 - (ρ + Complex.I * (t : ℂ))))
    (hYsquare : ∀ t : ℝ,
      (Y (ρ + Complex.I * (t : ℂ))) ^ 2 =
        (Z (ρ + Complex.I * (t : ℂ)))⁻¹)
    (hZnorm : ∀ t : ℝ, ‖Z (ρ + Complex.I * (t : ℂ))‖ = 1)
    (hconj : ∀ t : ℝ,
      Lbar (1 - (ρ + Complex.I * (t : ℂ))) =
        conj (L (ρ + Complex.I * (t : ℂ))))
    (hnozero₁ : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ b₁ →
      M (criticalLinePoint ρ t) ≠ 0)
    (hnozero₂ : ∀ x ∈ Set.Icc b₂ b₃,
      M (criticalLinePoint ρ x) ≠ 0) :
    ((lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).im = 0) ∧
    0 ≤ (lemma23ComplexCoefficient
      (M (ρ + Complex.I * (b₁ : ℂ)))
      (M (ρ + Complex.I * (b₂ : ℂ)))
      (M (ρ + Complex.I * (b₃ : ℂ))) mDeriv).re := by
  have hlineReal := lemma23_M_real_on_critical_line_of_square_root
    M Y L Lbar Z ρ hfactor hLfunctional hYsquare hZnorm hconj
  have hlineDerivReal :=
    lemma23_vertical_derivative_real_of_line_real_near hMderiv
      (Filter.Eventually.of_forall hlineReal)
  exact lemma23_verticalLine_coefficient_nonneg M horder hMcont hMderiv
    hMderivNe hMzero (fun t _ => hlineReal t) hlineDerivReal hnozero₁ hnozero₂

end ZhangLS.Spec
