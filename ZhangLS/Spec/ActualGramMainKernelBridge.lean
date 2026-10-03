import ZhangLS.Spec.ActualGramOriginalScaling
import ZhangLS.Spec.ActualGramOneSidedSuperposition

/-! Exact evaluation of the literal first and second smoothing main kernels
under profile superposition. The original beta shifts are retained, and the
second expression retains the plus sign on the complex Volterra term. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical Interval

lemma actualGram_log_ratio_scale {B q : ℝ} (hB : 0<B) (hq : 0<q) (v : ℝ) :
    Real.log (Real.exp (B*v)/q)=B*(v-Real.log q/B) := by
  rw [Real.log_div (Real.exp_ne_zero _) hq.ne',Real.log_exp]
  field_simp [hB.ne'] <;> ring

lemma actualGram_positive_cutoff_cpow (gamma : ℂ) {B q : ℝ} (hB : 0<B) (hq : 0<q) (v : ℝ) :
    ((Real.exp (B*v)/q : ℝ) : ℂ)^gamma =
      Complex.exp (((B : ℂ)*gamma)*(v-Real.log q/B : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)),
    ← Complex.ofReal_log (by positivity),actualGram_log_ratio_scale hB hq v]
  push_cast
  congr 1
  ring

lemma actualGram_first_main_kernel (D : ℕ) (c : ℝ) (j : Fin 3) (μ : ℕ)
    {B q : ℝ} (hB : 0<B) (hq : 0<q) (v : ℝ) :
    lemma82MainTerm D c j μ (Real.exp (B*v)/q) =
      (1+((B : ℂ)*lemma82SmoothingBeta D μ-(B : ℂ)*lemma83PaperBeta D c j)*
        (v-Real.log q/B : ℝ))*
      Complex.exp (((B : ℂ)*lemma82SmoothingBeta D μ)*(v-Real.log q/B : ℝ)) := by
  have hb : lemma82PaperBeta D c j=lemma83PaperBeta D c j := rfl
  rw [lemma82MainTerm,hb,actualGram_positive_cutoff_cpow _ hB hq v,
    actualGram_log_ratio_scale hB hq v]
  push_cast
  ring

lemma actualGram_mu6_nonzero {D : ℕ} (hD : 1<D) : lemma84SmoothingBeta D 6≠0 := by
  have he := actualGram_original_mu6_scaled hD
  have hc : 3*I*(Real.pi : ℂ)/2≠0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · norm_num
  intro hz
  change (Real.log (lemma23PaperP D) : ℂ)*lemma84SmoothingBeta D 6=3*I*(Real.pi : ℂ)/2 at he
  rw [hz,mul_zero] at he
  exact hc he.symm

lemma actualGram_second_main_kernel (D : ℕ) (c : ℝ) (j : Fin 3) (μ : ℕ)
    (hm : lemma84SmoothingBeta D μ≠0) {B q : ℝ} (hB : 0<B) (hq : 0<q) (v : ℝ) :
    lemma84MainTerm D c j μ (Real.exp (B*v)/q) =
      let ell := (B : ℂ)*(-lemma84SmoothingBeta D μ)
      let a₁ := (B : ℂ)*lemma83PaperBeta D c (j+1)
      let a₂ := (B : ℂ)*lemma83PaperBeta D c (j+2)
      a₁*a₂/ell^2+(1-a₁*a₂/ell^2+(a₁+ell)*(a₂+ell)/ell*
        (v-Real.log q/B : ℝ))*Complex.exp (ell*(v-Real.log q/B : ℝ)) := by
  have hBC : (B : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  dsimp only
  rw [lemma84MainTerm,actualGram_log_ratio_scale hB hq v,
    actualGram_positive_cutoff_cpow _ hB hq v]
  push_cast
  field_simp [hBC,hm] <;> ring

/-- Exact first main expression, before any replacement of b_j=B beta_j. -/
theorem actualGram_first_main_superposition (D : ℕ) (c : ℝ) (j : Fin 3) (μ : ℕ)
    (f f' f'' : ℝ → ℂ) {B q b : ℝ} (hB : 0<B) (hq : 0<q)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (hfb : f b=0) (hfpb : f' b=0) :
    (∫ v in (Real.log q/B)..b,
      actualGramRampDensity ((B : ℂ)*lemma82SmoothingBeta D μ) f f' f'' v*
        lemma82MainTerm D c j μ (Real.exp (B*v)/q)) =
      -f' (Real.log q/B)-(B : ℂ)*lemma83PaperBeta D c j*f (Real.log q/B) := by
  let ell : ℂ := (B : ℂ)*lemma82SmoothingBeta D μ
  let t : ℝ := Real.log q/B
  have hc := actualGram_ramp_density_continuous ell f f' f'' hf hf' hf''
  have h0 : Continuous (fun v : ℝ => actualGramRampDensity ell f f' f'' v*Complex.exp (ell*(v-t : ℝ))) := by fun_prop
  have h1 : Continuous (fun v : ℝ => actualGramRampDensity ell f f' f'' v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ))) := by fun_prop
  simp_rw [actualGram_first_main_kernel D c j μ hB hq]
  simpa only [ell,t,mul_assoc] using
    actualGram_first_main_identity ell ((B : ℂ)*lemma83PaperBeta D c j) f f' f'' t b
      (fun v _ => hf v) (fun v _ => hf' v) (h0.intervalIntegrable t b) (h1.intervalIntegrable t b) hfb hfpb

/-- Exact second main expression with the original negative smoothing shift.
The Volterra term has a plus sign and the full scaled beta_k beta_l factor.
No nonnegativity of this complex term is asserted. -/
theorem actualGram_second_main_superposition {D : ℕ} (hD : 1<D)
    (c : ℝ) (j : Fin 3) (g g' g'' : ℝ → ℂ) {B q b : ℝ} (hB : 0<B) (hq : 0<q)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : Continuous g'') (hgb : g b=0) (hgpb : g' b=0) :
    (∫ v in (Real.log q/B)..b,
      actualGramRampDensity ((B : ℂ)*(-lemma84SmoothingBeta D 6)) g g' g'' v*
        lemma84MainTerm D c j 6 (Real.exp (B*v)/q)) =
      -g' (Real.log q/B)+
      ((B : ℂ)*lemma83PaperBeta D c (j+1)+(B : ℂ)*lemma83PaperBeta D c (j+2))*g (Real.log q/B)+
      ((B : ℂ)*lemma83PaperBeta D c (j+1))*((B : ℂ)*lemma83PaperBeta D c (j+2))*
        (∫ u in (Real.log q/B)..b, g u) := by
  let ell : ℂ := (B : ℂ)*(-lemma84SmoothingBeta D 6)
  let t : ℝ := Real.log q/B
  have hell : ell≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hB.ne')
    (neg_ne_zero.mpr (actualGram_mu6_nonzero hD))
  have hc := actualGram_ramp_density_continuous ell g g' g'' hg hg' hg''
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have h0 : Continuous (fun v : ℝ => actualGramRampDensity ell g g' g'' v*Complex.exp (ell*(v-t : ℝ))) := by fun_prop
  have h1 : Continuous (fun v : ℝ => actualGramRampDensity ell g g' g'' v*(v-t : ℝ)*Complex.exp (ell*(v-t : ℝ))) := by fun_prop
  simp_rw [actualGram_second_main_kernel D c j 6 (actualGram_mu6_nonzero hD) hB hq]
  exact actualGram_second_main_identity ell ((B : ℂ)*lemma83PaperBeta D c (j+1))
    ((B : ℂ)*lemma83PaperBeta D c (j+2)) hell g g' g'' t b (fun v _ => hg v)
    (fun v _ => hg' v) (hc.intervalIntegrable t b) (hgc.intervalIntegrable t b) (h0.intervalIntegrable t b)
    (h1.intervalIntegrable t b) hgb hgpb

/-- Extending the Volterra endpoint to 1 is exact when the profile vanishes
after b; no upstream Volterra tail is removed. -/
lemma actualGram_volterra_terminal_extension (g : ℝ → ℂ) (hg : Continuous g)
    {b : ℝ} (hb : b≤1) (hz : ∀ v, b≤v → g v=0) (t : ℝ) :
    (∫ v in t..b, g v)=(∫ v in t..1, g v) := by
  have he : (∫ v in b..1, g v)=0 := by
    calc
      _ = ∫ _v in b..1, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        exact hz v (by simpa only [Set.uIcc_of_le hb] using hv : v ∈ Set.Icc b 1).1
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := t) (b := b) (c := 1) (hg.intervalIntegrable t b) (hg.intervalIntegrable b 1)
  simpa only [he,add_zero] using h

end ZhangLS.Spec
