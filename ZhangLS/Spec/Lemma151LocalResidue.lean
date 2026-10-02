import ZhangLS.Spec.Lemma55ZetaLocalData
import ZhangLS.Spec.Lemma57MellinContour

/-! Exact local regularization of Appendix B's actual ζ-ratio tail integrand.
This determines its residue without replacing ζ by a rational model. The
contour displacement and uniform arithmetic errors remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Filter Set
open scoped Topology

/-- Numerator in the penultimate display of Appendix B, with log P=L. -/
noncomputable def lemma151TailNumerator (L z : ℝ) (γ s : ℂ) : ℂ :=
  Complex.exp ((L : ℂ)*γ*(0.504-(z : ℂ)) + (L : ℂ)*z*s) -
    Complex.exp ((L : ℂ)*0.004*γ + (L : ℂ)*0.5*s)

/-- Actual ζ-ratio integrand, including the original Gaussian ω₁ and l₁-shift. -/
noncomputable def lemma151TailIntegrand (D : ℕ) (L z : ℝ) (β γ : ℂ)
    (l₁ : ℕ) (s : ℂ) : ℂ :=
  lemma151TailNumerator L z γ s * riemannZeta (1+s) /
    riemannZeta (1+s-β) * lemma57OmegaOne D (s-γ) *
      Complex.exp (-s*(Real.log (l₁ : ℝ) : ℂ)) / (s-γ)

noncomputable def lemma151TailRegularized (D : ℕ) (L z : ℝ) (β γ : ℂ)
    (l₁ : ℕ) (s : ℂ) : ℂ :=
  lemma151TailNumerator L z γ s * zetaPoleRemoved (1+s) /
    riemannZeta (1+s-β) * lemma57OmegaOne D (s-γ) *
      Complex.exp (-s*(Real.log (l₁ : ℝ) : ℂ)) / (s-γ)

/-- The apparent pole at γ cancels in the exponential bracket itself. -/
theorem lemma151_tail_numerator_at_gamma (L z : ℝ) (γ : ℂ) :
    lemma151TailNumerator L z γ γ = 0 := by
  unfold lemma151TailNumerator
  have he : (L : ℂ)*γ*(0.504-(z : ℂ)) + (L : ℂ)*z*γ =
      (L : ℂ)*0.004*γ + (L : ℂ)*0.5*γ := by ring
  rw [he, sub_self]

lemma lemma151_tail_numerator_differentiable (L z : ℝ) (γ : ℂ) :
    Differentiable ℂ (lemma151TailNumerator L z γ) := by
  unfold lemma151TailNumerator
  fun_prop

/-- The canceled γ denominator has a genuinely holomorphic continuation. -/
theorem lemma151_tail_gamma_quotient_differentiable (L z : ℝ) (γ : ℂ) :
    Differentiable ℂ (dslope (lemma151TailNumerator L z γ) γ) := by
  intro s
  by_cases hs : s = γ
  · subst s
    obtain ⟨p,hp⟩ := (lemma151_tail_numerator_differentiable L z γ).analyticAt γ
    exact (show AnalyticAt ℂ (dslope (lemma151TailNumerator L z γ) γ) γ from
      ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩).differentiableAt
  · exact (differentiableAt_dslope_of_ne hs).mpr
      ((lemma151_tail_numerator_differentiable L z γ) s)

lemma lemma151_tail_gamma_quotient_eq (L z : ℝ) (γ : ℂ)
    {s : ℂ} (hs : s ≠ γ) :
    dslope (lemma151TailNumerator L z γ) γ s =
      lemma151TailNumerator L z γ s / (s-γ) := by
  rw [dslope_of_ne _ hs, slope_def_module, lemma151_tail_numerator_at_gamma]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma lemma151_tail_regularized_eq (D : ℕ) (L z : ℝ) (β γ : ℂ) (l₁ : ℕ)
    {s : ℂ} (hs : s ≠ 0) (hs1 : 1+s ≠ 0) :
    lemma151TailRegularized D L z β γ l₁ s = s * lemma151TailIntegrand D L z β γ l₁ s := by
  have h1 : 1+s ≠ 1 := by intro he; apply hs; linear_combination he
  unfold lemma151TailRegularized lemma151TailIntegrand
  rw [zetaPoleRemoved_eq_mul_riemannZeta hs1 h1]
  simp only [add_sub_cancel_left]
  ring

/-- Exact residue before the small-β and Gaussian approximations. In particular,
1/ζ(1−β) cannot be replaced by −β as an exact finite-D equality. -/
noncomputable def lemma151ExactTailResidue (D : ℕ) (L z : ℝ) (β γ : ℂ) : ℂ :=
  -(lemma151TailNumerator L z γ 0) * lemma57OmegaOne D (-γ) /
    (γ * riemannZeta (1-β))

lemma lemma151_tail_regularized_at_zero (D : ℕ) (L z : ℝ) (β γ : ℂ) (l₁ : ℕ) :
    lemma151TailRegularized D L z β γ l₁ 0 = lemma151ExactTailResidue D L z β γ := by
  unfold lemma151TailRegularized lemma151ExactTailResidue
  simp only [add_zero, lemma55_actual_zeta_pole_removed_at_one, mul_one,
    zero_sub, neg_zero, zero_mul, Complex.exp_zero, div_neg]
  ring

lemma lemma151_tail_regularized_continuousAt_zero
    (D : ℕ) (L z : ℝ) {β γ : ℂ} (l₁ : ℕ)
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hζ : riemannZeta (1-β) ≠ 0) :
    ContinuousAt (lemma151TailRegularized D L z β γ l₁) 0 := by
  have hn : Continuous (lemma151TailNumerator L z γ) := by
    unfold lemma151TailNumerator
    fun_prop
  have hzbase : ContinuousAt zetaPoleRemoved (1+(0 : ℂ)) := by
    simpa using (lemma55_actual_zeta_pole_removed_analyticAt (z := (1 : ℂ)) (by norm_num)).continuousAt
  have hz : ContinuousAt (fun s : ℂ => zetaPoleRemoved (1+s)) 0 :=
    hzbase.comp (f := fun s : ℂ => 1+s) (x := 0) (by fun_prop : ContinuousAt (fun s : ℂ => 1+s) 0)
  have h1 : 1-β ≠ 1 := by intro he; apply hβ; linear_combination -he
  have hdbase : ContinuousAt riemannZeta (1+(0 : ℂ)-β) := by
    simpa using (differentiableAt_riemannZeta h1).continuousAt
  have hd : ContinuousAt (fun s : ℂ => riemannZeta (1+s-β)) 0 :=
    hdbase.comp (f := fun s : ℂ => 1+s-β) (x := 0) (by fun_prop : ContinuousAt (fun s : ℂ => 1+s-β) 0)
  have ho : Continuous (fun s : ℂ => lemma57OmegaOne D (s-γ)) := by
    unfold lemma57OmegaOne
    fun_prop
  have he : Continuous (fun s : ℂ => Complex.exp (-s*(Real.log (l₁ : ℝ) : ℂ))) := by
    fun_prop
  exact (((hn.continuousAt.mul hz).div hd (by simpa using hζ)).mul ho.continuousAt).mul
    he.continuousAt |>.div (by fun_prop) (by simpa using hγ)

/-- A genuine punctured-neighborhood residue identity for the actual zeta
integrand. Its hypotheses are nonvanishing/regularity conditions, not the
arithmetic asymptotic being sought. -/
theorem lemma151_actual_tail_residue_limit
    (D : ℕ) (L z : ℝ) {β γ : ℂ} (l₁ : ℕ)
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hζ : riemannZeta (1-β) ≠ 0) :
    Tendsto (fun s : ℂ => s * lemma151TailIntegrand D L z β γ l₁ s)
      (𝓝[≠] 0) (𝓝 (lemma151ExactTailResidue D L z β γ)) := by
  have hc := (lemma151_tail_regularized_continuousAt_zero D L z l₁ hβ hγ hζ).tendsto
  rw [lemma151_tail_regularized_at_zero] at hc
  apply (hc.mono_left nhdsWithin_le_nhds).congr'
  have hn : ∀ᶠ s : ℂ in 𝓝 0, 1+s ≠ 0 :=
    (by fun_prop : Continuous (fun s : ℂ => 1+s)).continuousAt.eventually_ne
      (by norm_num : (1 : ℂ)+0 ≠ 0)
  filter_upwards [self_mem_nhdsWithin, hn.filter_mono nhdsWithin_le_nhds] with s hs hs1
  exact lemma151_tail_regularized_eq D L z β γ l₁ (by simpa using hs) hs1

/-- The normalized exact reciprocal factor: the source of β/γ in the last display. -/
theorem lemma151_reciprocal_zeta_factor {β : ℂ}
    (hβ : β ≠ 0) (h1 : 1-β ≠ 0) :
    (riemannZeta (1-β))⁻¹ = -β / zetaPoleRemoved (1-β) := by
  have hn : 1-β ≠ 1 := by intro he; apply hβ; linear_combination -he
  rw [zetaPoleRemoved_eq_mul_riemannZeta h1 hn]
  have he : (1-β)-1 = -β := by ring
  rw [he, div_mul_eq_div_div, div_self (neg_ne_zero.mpr hβ), one_div]

/-- Nonvanishing at the actual purely imaginary shifts is unconditional. -/
theorem lemma151_actual_imaginary_tail_residue_limit
    (D : ℕ) (L z : ℝ) {β γ : ℂ} (l₁ : ℕ)
    (hβ : β ≠ 0) (hβre : β.re = 0) (hγ : γ ≠ 0) :
    Tendsto (fun s : ℂ => s * lemma151TailIntegrand D L z β γ l₁ s)
      (𝓝[≠] 0) (𝓝 (lemma151ExactTailResidue D L z β γ)) :=
  lemma151_actual_tail_residue_limit D L z l₁ hβ hγ
    (riemannZeta_ne_zero_of_one_le_re (by simp [hβre]))

/-- Exact multiplicative form exposing both analytic corrections omitted by the
terminal paper display: ω₁(−γ) and the pole-removed ζ value. -/
theorem lemma151_exact_tail_residue_factorization
    (D : ℕ) (L z : ℝ) {β γ : ℂ}
    (hβ : β ≠ 0) (h1 : 1-β ≠ 0) :
    lemma151ExactTailResidue D L z β γ =
      (β/γ) * lemma151TailNumerator L z γ 0 *
        (lemma57OmegaOne D (-γ) / zetaPoleRemoved (1-β)) := by
  unfold lemma151ExactTailResidue
  rw [div_mul_eq_div_div, div_eq_mul_inv _ (riemannZeta (1-β)),
    lemma151_reciprocal_zeta_factor hβ h1]
  ring

/-- Explicit local error, not an assumed O(α₁). The two deviations on the right
are the actual analytic functions, and can be estimated separately. -/
theorem lemma151_exact_tail_residue_error
    (D : ℕ) (L z : ℝ) {β γ : ℂ}
    (hβ : β ≠ 0) (h1 : 1-β ≠ 0)
    (hR : ‖zetaPoleRemoved (1-β)-1‖ < 1) :
    ‖lemma151ExactTailResidue D L z β γ -
      (β/γ) * lemma151TailNumerator L z γ 0‖ ≤
      ‖β/γ‖ * ‖lemma151TailNumerator L z γ 0‖ *
        (‖lemma57OmegaOne D (-γ)-1‖ + ‖zetaPoleRemoved (1-β)-1‖) /
          (1-‖zetaPoleRemoved (1-β)-1‖) := by
  let R := zetaPoleRemoved (1-β)
  let w := lemma57OmegaOne D (-γ)
  let A := (β/γ) * lemma151TailNumerator L z γ 0
  have hlow : 1-‖R-1‖ ≤ ‖R‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) R
    rw [norm_one, norm_sub_rev] at hh
    dsimp [R]
    linarith only [hh]
  have hpos : 0 < 1-‖R-1‖ := by dsimp [R]; linarith
  have hRn : R ≠ 0 := norm_pos_iff.mp (hpos.trans_le hlow)
  have hwr : ‖w-R‖ ≤ ‖w-1‖+‖R-1‖ := by
    calc
      _ = ‖(w-1)-(R-1)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  rw [lemma151_exact_tail_residue_factorization D L z hβ h1]
  change ‖A*(w/R)-A‖ ≤ _
  have he : A*(w/R)-A = A*(w-R)/R := by field_simp [hRn]
  rw [he, norm_div, norm_mul]
  calc
    _ ≤ ‖A‖*(‖w-1‖+‖R-1‖)/‖R‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwr (norm_nonneg _)) (norm_nonneg _)
    _ ≤ ‖A‖*(‖w-1‖+‖R-1‖)/(1-‖R-1‖) :=
      div_le_div_of_nonneg_left (by positivity) hpos hlow
    _ = _ := by simp only [A, R, w, norm_mul]

end ZhangLS.Spec
