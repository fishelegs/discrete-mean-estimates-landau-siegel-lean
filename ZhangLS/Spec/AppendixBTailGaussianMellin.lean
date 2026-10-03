import ZhangLS.Spec.AppendixBTailRamp
import ZhangLS.Spec.Lemma44ProductMellin
import ZhangLS.Spec.Lemma151LocalResidue

/-! Genuine infinite rho-series/Gaussian Mellin interchange. The series,
Gaussian, finite-D shifts, and zeta ratio are the actual analytic objects. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical

noncomputable def appendixBRhoGaussianSeries (D : ℕ) (B : ℝ) (β γ : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (lemma151Rho β) (1+γ) n *
    (zhangGaussianWeight D (B/n) : ℂ)

noncomputable def appendixBRhoGaussianIntegrand (D : ℕ) (B σ : ℝ)
    (β γ : ℂ) (t : ℝ) : ℂ :=
  let w := (σ : ℂ)+(t : ℂ)*I
  (riemannZeta (1+γ+w)/riemannZeta (1+γ+w-β))*
    exp (w*(Real.log B : ℂ))*lemma57OmegaOne D w/w

lemma appendixB_rho_gaussian_integrand_tsum (D : ℕ) (B : ℝ) {σ : ℝ}
    (hσ : 0<σ) {β γ : ℂ} (hβ : β.re=0) (hγ : γ.re=0) (t : ℝ) :
    appendixBRhoGaussianIntegrand D B σ β γ t*I =
      ∑' n : ℕ, lemma44MellinSeriesTerm D (lemma151Rho β) (1+γ) B σ n t := by
  have hs : 1<(1+γ+((σ : ℂ)+(t : ℂ)*I)).re := by simpa [hγ] using hσ
  rw [appendixBRhoGaussianIntegrand,←(appendixB_rho_dirichlet_series hβ hs).2]
  unfold LSeries lemma44MellinSeriesTerm
  simp_rw [div_eq_mul_inv,mul_assoc]
  rw [tsum_mul_right]

/-- Includes actual summability and integrability, excluding Bochner default-value shortcuts. -/
theorem appendixB_rho_gaussian_mellin {D : ℕ} (hD : 1<D)
    {B σ : ℝ} (hB : 0<B) (hσ : 0<σ) {β γ : ℂ}
    (hβ : β.re=0) (hγ : γ.re=0) :
    Integrable (appendixBRhoGaussianIntegrand D B σ β γ) ∧
    Summable (fun n : ℕ => LSeries.term (lemma151Rho β) (1+γ) n *
      (zhangGaussianWeight D (B/n) : ℂ)) ∧
    (2*(Real.pi : ℂ)*I)⁻¹*(∫ t : ℝ,
      appendixBRhoGaussianIntegrand D B σ β γ t*I)=
        appendixBRhoGaussianSeries D B β γ := by
  have hs : LSeriesSummable (lemma151Rho β) ((((1+γ).re+σ : ℝ) : ℂ)) :=
    (appendixB_rho_dirichlet_series hβ (by simpa [hγ] using hσ)).1
  have ht := lemma44MellinSeriesTerm_tsum_integrable hD (lemma151Rho β)
    (1+γ) B hσ.ne' hs
  have hti : Integrable (fun t : ℝ =>
      appendixBRhoGaussianIntegrand D B σ β γ t*I) := by
    apply ht.congr
    filter_upwards [] with t
    exact (appendixB_rho_gaussian_integrand_tsum D B hσ hβ hγ t).symm
  have hi : Integrable (appendixBRhoGaussianIntegrand D B σ β γ) := by
    simpa only [mul_assoc,I_mul_I,mul_neg,mul_one,neg_neg] using hti.mul_const (-I)
  refine ⟨hi,(lemma44_full_series_gaussian_mellin hD (lemma151Rho β) (1+γ) hB hσ hs).1,?_⟩
  simp_rw [appendixB_rho_gaussian_integrand_tsum D B hσ hβ hγ]
  exact (lemma44_full_series_gaussian_mellin hD (lemma151Rho β) (1+γ) hB hσ hs).2

lemma appendixB_monomial_LSeries_term {X : ℝ} (hX : 0<X) (β γ : ℂ) (n : ℕ) :
    (X : ℂ)^γ*LSeries.term (lemma151Rho β) (1+γ) n=
      lemma151Rho β n/n*((X/n : ℝ) : ℂ)^γ := by
  by_cases hn : n=0
  · simp [hn]
  have hnp : 0<n := Nat.pos_of_ne_zero hn
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hnp
  have hnC : (n : ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  have hp : ((X/n : ℝ) : ℂ)^γ*(n : ℂ)^γ=(X : ℂ)^γ := by
    simpa using appendixB_positive_cpow_split hX hnr (show 0<(1 : ℕ) by norm_num) γ
  have hpow : (n : ℂ)^γ≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  rw [LSeries.term_of_ne_zero hn,Complex.cpow_add 1 γ hnC,Complex.cpow_one,←hp]
  field_simp
  <;> ring

noncomputable def appendixBSourceGaussianSlice (D : ℕ) (L z : ℝ)
    (β γ : ℂ) (l₁ : ℕ) : ℂ :=
  ((Real.exp (0.504*L)/(l₁ : ℝ) : ℝ) : ℂ)^γ *
    (appendixBRhoGaussianSeries D (Real.exp (z*L)/l₁) β γ-
      appendixBRhoGaussianSeries D (Real.exp (0.5*L)/l₁) β γ)

/-- The series side is exactly the original rho/n weighted Gaussian difference. -/
theorem appendixB_source_gaussian_slice_eq_sum {D : ℕ} (hD : 1<D)
    (L z : ℝ) {β γ : ℂ} (hβ : β.re=0) (hγ : γ.re=0)
    {l₁ : ℕ} (hl : 0<l₁) :
    appendixBSourceGaussianSlice D L z β γ l₁=
      ∑' n : ℕ, lemma151Rho β n/n*
        (((Real.exp (0.504*L)/(l₁ : ℝ)/n : ℝ) : ℂ)^γ)*
        ((zhangGaussianWeight D (Real.exp (z*L)/(l₁ : ℝ)/n)-
          zhangGaussianWeight D (Real.exp (0.5*L)/(l₁ : ℝ)/n) : ℝ) : ℂ) := by
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  have hx := div_pos (Real.exp_pos (z*L)) hlr
  have hy := div_pos (Real.exp_pos (0.5*L)) hlr
  have hX := div_pos (Real.exp_pos (0.504*L)) hlr
  have hsx := (appendixB_rho_gaussian_mellin hD hx (show (0 : ℝ)<1 by norm_num) hβ hγ).2.1
  have hsy := (appendixB_rho_gaussian_mellin hD hy (show (0 : ℝ)<1 by norm_num) hβ hγ).2.1
  unfold appendixBSourceGaussianSlice appendixBRhoGaussianSeries
  rw [←hsx.tsum_sub hsy,←tsum_mul_left]
  apply tsum_congr
  intro n
  rw [←mul_sub,←mul_assoc,appendixB_monomial_LSeries_term hX β γ n,Complex.ofReal_sub]

lemma appendixB_source_gaussian_numerator {L z : ℝ} (γ w : ℂ)
    {l₁ : ℕ} (hl : 0<l₁) :
    ((Real.exp (0.504*L)/(l₁ : ℝ) : ℝ) : ℂ)^γ *
      (exp (w*(Real.log (Real.exp (z*L)/(l₁ : ℝ)) : ℂ))-
        exp (w*(Real.log (Real.exp (0.5*L)/(l₁ : ℝ)) : ℂ))) =
      lemma151TailNumerator L z γ (γ+w)*
        exp (-(γ+w)*(Real.log (l₁ : ℝ) : ℂ)) := by
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  rw [lemma84_positive_cpow_eq_exp (div_pos (Real.exp_pos _) hlr)]
  simp only [Real.log_div (Real.exp_pos _).ne' hlr.ne',Real.log_exp]
  unfold lemma151TailNumerator
  rw [mul_sub,sub_mul,←exp_add,←exp_add,←exp_add,←exp_add]
  apply congrArg₂ (fun a b : ℂ => exp a-exp b)
  all_goals push_cast; ring

lemma appendixB_source_gaussian_integrand {D : ℕ} {L z σ : ℝ} (β γ : ℂ)
    {l₁ : ℕ} (hl : 0<l₁) (t : ℝ) :
    ((Real.exp (0.504*L)/(l₁ : ℝ) : ℝ) : ℂ)^γ *
      (appendixBRhoGaussianIntegrand D (Real.exp (z*L)/l₁) σ β γ t-
        appendixBRhoGaussianIntegrand D (Real.exp (0.5*L)/l₁) σ β γ t) =
      lemma151TailIntegrand D L z β γ l₁ (γ+((σ : ℂ)+(t : ℂ)*I)) := by
  let w : ℂ := (σ : ℂ)+(t : ℂ)*I
  have hnum := appendixB_source_gaussian_numerator (L := L) (z := z) γ w hl
  have hz : 1+γ+w=1+(γ+w) := by ring
  have hd : γ+w-γ=w := by ring
  unfold appendixBRhoGaussianIntegrand lemma151TailIntegrand
  change _ = lemma151TailNumerator L z γ (γ+w)*riemannZeta (1+(γ+w))/
    riemannZeta (1+(γ+w)-β)*lemma57OmegaOne D (γ+w-γ)*
      exp (-(γ+w)*(Real.log (l₁ : ℝ) : ℂ))/(γ+w-γ)
  rw [hd,←hz]
  linear_combination (riemannZeta (1+γ+w)/riemannZeta (1+γ+w-β))*
    lemma57OmegaOne D w/w * hnum

/-- The actual source slice equals a genuinely integrable zeta contour.
The line is parametrized by s=γ+σ+it, the same geometric right vertical line
because Re γ=0. No movement across a pole occurs in this parametrization. -/
theorem appendixB_source_gaussian_slice_mellin {D : ℕ} (hD : 1<D)
    (L z : ℝ) {σ : ℝ} (hσ : 0<σ) {β γ : ℂ}
    (hβ : β.re=0) (hγ : γ.re=0) {l₁ : ℕ} (hl : 0<l₁) :
    Integrable (fun t : ℝ =>
      lemma151TailIntegrand D L z β γ l₁ (γ+((σ : ℂ)+(t : ℂ)*I))) ∧
    (2*(Real.pi : ℂ)*I)⁻¹*(∫ t : ℝ,
      lemma151TailIntegrand D L z β γ l₁ (γ+((σ : ℂ)+(t : ℂ)*I))*I)=
        appendixBSourceGaussianSlice D L z β γ l₁ := by
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  have hx := div_pos (Real.exp_pos (z*L)) hlr
  have hy := div_pos (Real.exp_pos (0.5*L)) hlr
  obtain ⟨hiX,hsX,heX⟩ := appendixB_rho_gaussian_mellin hD hx hσ hβ hγ
  obtain ⟨hiY,hsY,heY⟩ := appendixB_rho_gaussian_mellin hD hy hσ hβ hγ
  have hi := (hiX.sub hiY).const_mul
    (((Real.exp (0.504*L)/(l₁ : ℝ) : ℝ) : ℂ)^γ)
  constructor
  · apply hi.congr
    filter_upwards [] with t
    exact appendixB_source_gaussian_integrand β γ hl t
  · simp_rw [←appendixB_source_gaussian_integrand β γ hl]
    simp_rw [mul_assoc _ _ I,sub_mul]
    rw [integral_const_mul,integral_sub (hiX.mul_const I) (hiY.mul_const I)]
    unfold appendixBSourceGaussianSlice
    rw [←heX,←heY]
    ring

end ZhangLS.Spec
