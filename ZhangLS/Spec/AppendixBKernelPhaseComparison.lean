import ZhangLS.Spec.AppendixBKernelOriginalUniform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Explicit original-phase and normalization corrections. The logarithm of l1,
P2's T^-10 factor, and the finite-D beta perturbations all remain accounted for. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex

lemma appendixB_imaginary_exp_norm {γ : ℂ} (hγ : γ.re=0) (t : ℝ) :
    ‖exp (γ*(t : ℂ))‖=1 := by
  rw [norm_exp]
  simp [mul_re,hγ]

lemma appendixB_imaginary_exp_lipschitz {γ : ℂ} (hγ : γ.re=0) (u v : ℝ) :
    ‖exp (γ*(u : ℂ))-exp (γ*(v : ℂ))‖≤‖γ‖*|u-v| := by
  have he : exp (γ*(u : ℂ))-exp (γ*(v : ℂ)) =
      exp (γ*(v : ℂ))*(exp (I*((γ.im*(u-v) : ℝ) : ℂ))-1) := by
    have hγeq : γ=I*(γ.im : ℂ) := by apply Complex.ext <;> simp [hγ]
    rw [mul_sub,mul_one,←exp_add,hγeq]
    congr 2
    simp only [mul_im,I_re,ofReal_im,mul_zero,I_im,ofReal_re,one_mul,zero_add]
    push_cast
    ring
  rw [he,norm_mul,appendixB_imaginary_exp_norm hγ,one_mul]
  calc
    _ ≤ |γ.im*(u-v)| := by simpa [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := γ.im*(u-v)))
    _ = |γ.im| * |u-v| := abs_mul _ _
    _ ≤ ‖γ‖*|u-v| := mul_le_mul_of_nonneg_right (abs_im_le_norm γ) (abs_nonneg _)

noncomputable def appendixBLogModel (u v : ℝ) (β γ : ℂ) : ℂ :=
  exp (γ*((u-v : ℝ) : ℂ))*((1-β/γ)*(1-(v/u : ℝ))+β/γ^2/(u : ℂ))-
    β/γ^2/(u : ℂ)

lemma appendixB_model_as_log_model {X : ℝ} (hX : 0<X) (hlog : Real.log X≠0) (β γ : ℂ)
    {l : ℕ} (hl : 0<l) :
    appendixBModelLeading X (X/l) β γ =
      appendixBLogModel (Real.log X) (Real.log (l : ℝ)) β γ := by
  have hlr : 0<(l : ℝ) := Nat.cast_pos.mpr hl
  rw [appendixBModelLeading,lemma84_positive_cpow_eq_exp (div_pos hX hlr),
    Real.log_div hX.ne' hlr.ne']
  unfold appendixBLogModel
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hlog]
  <;> ring

noncomputable def appendixBPhaseBudget (α q δ h : ℝ) : ℝ :=
  δ/α+4*h/q+2*(δ/(α^2*q)+(3*α/α^2)*(10*h)/(q^2))+
    (33*α*h)*(4+3*α/(α^2*q))

/-- Quantitative stability of the rational residue under all three source
corrections. Every input is an elementary bound, not a contour hypothesis. -/
theorem appendixB_log_model_stability {α q δ h u u₀ v : ℝ} {β β₀ γ : ℂ}
    (hα : 0<α) (hq : 0<q) (hδ : 0≤δ) (hh : 0≤h)
    (hγre : γ.re=0) (hγlo : α≤‖γ‖) (hγhi : ‖γ‖≤3*α)
    (hβ : ‖β‖≤3*α) (hβ₀ : ‖β₀‖≤3*α) (hdβ : ‖β-β₀‖≤δ)
    (hu : q≤u) (hu₀ : q≤u₀) (hv : 0≤v) (hvh : v≤h)
    (hdu : |u-u₀|≤10*h) :
    ‖appendixBLogModel u v β γ-appendixBLogModel u₀ 0 β₀ γ‖≤
      appendixBPhaseBudget α q δ h := by
  have hup : 0<u := hq.trans_le hu
  have hu₀p : 0<u₀ := hq.trans_le hu₀
  have hg : 0<‖γ‖ := hα.trans_le hγlo
  have hg0 : γ≠0 := norm_pos_iff.mp hg
  have huC : (u : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hup.ne'
  have hu₀C : (u₀ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hu₀p.ne'
  let A := (1-β/γ)*(1-(v/u : ℝ) : ℂ)
  let A₀ := 1-β₀/γ
  let B := β/γ^2/(u : ℂ)
  let B₀ := β₀/γ^2/(u₀ : ℂ)
  let E := exp (γ*((u-v : ℝ) : ℂ))
  let E₀ := exp (γ*(u₀ : ℂ))
  have hquot : ‖β/γ‖≤3 := by
    rw [norm_div]
    apply (div_le_iff₀ hg).mpr
    linarith
  have hquot₀ : ‖β₀/γ‖≤3 := by
    rw [norm_div]
    apply (div_le_iff₀ hg).mpr
    linarith
  have hA' : ‖1-β/γ‖≤4 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith only [hquot])
  have hA₀ : ‖A₀‖≤4 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith only [hquot₀])
  have hdq : ‖(β-β₀)/γ‖≤δ/α := by
    rw [norm_div]
    exact div_le_div₀ hδ hdβ hα hγlo
  have hvq : ‖((v/u : ℝ) : ℂ)‖≤h/q := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hv hup.le)]
    exact div_le_div₀ hh hvh hq hu
  have hA : ‖A-A₀‖≤δ/α+4*h/q := by
    have he : A-A₀ = -(β-β₀)/γ-(1-β/γ)*((v/u : ℝ) : ℂ) := by dsimp [A,A₀]; ring
    rw [he]
    calc
      _ ≤ ‖-(β-β₀)/γ‖+‖(1-β/γ)*((v/u : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = ‖(β-β₀)/γ‖+‖1-β/γ‖*‖((v/u : ℝ) : ℂ)‖ := by rw [neg_div,norm_neg,norm_mul]
      _ ≤ δ/α+4*(h/q) := add_le_add hdq (mul_le_mul hA' hvq (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hden : α^2*q≤‖γ‖^2*u := mul_le_mul (pow_le_pow_left₀ hα.le hγlo 2) hu hq.le (sq_nonneg _)
  have hB₀ : ‖B₀‖≤3*α/(α^2*q) := by
    dsimp [B₀]
    rw [norm_div,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu₀p,div_div]
    exact div_le_div₀ (by positivity) hβ₀ (by positivity)
      (mul_le_mul (pow_le_pow_left₀ hα.le hγlo 2) hu₀ hq.le (sq_nonneg _))
  have hB : ‖B-B₀‖≤δ/(α^2*q)+(3*α/α^2)*(10*h)/(q^2) := by
    have he : B-B₀=(β-β₀)/γ^2/(u : ℂ)+
        (β₀/γ^2)*(((u₀-u)/(u*u₀) : ℝ) : ℂ) := by
      dsimp [B,B₀]
      push_cast
      field_simp
      <;> ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_div,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hup,div_div]
      exact div_le_div₀ hδ hdβ (by positivity) hden
    · rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,
        abs_of_pos hup,abs_of_pos hu₀p,abs_sub_comm]
      have h₁ : ‖β₀‖/‖γ‖^2≤3*α/α^2 :=
        div_le_div₀ (by positivity) hβ₀ (by positivity) (pow_le_pow_left₀ hα.le hγlo 2)
      have h₂ : |u-u₀|/(u*u₀)≤10*h/q^2 :=
        div_le_div₀ (by positivity) hdu (by positivity)
          (by simpa [pow_two] using mul_le_mul hu hu₀ hq.le hup.le)
      have hm := mul_le_mul h₁ h₂ (by positivity) (by positivity : 0≤3*α/α^2)
      simpa only [mul_div_assoc] using hm
  have hE : ‖E-E₀‖≤33*α*h := by
    have ht : |u-v-u₀|≤11*h := by
      calc
        _ = |(u-u₀)-v| := by congr 1; ring
        _ ≤ |u-u₀|+|v| := abs_sub _ _
        _ ≤ 10*h+h := add_le_add hdu (by simpa [abs_of_nonneg hv] using hvh)
        _ = _ := by ring
    exact (appendixB_imaginary_exp_lipschitz hγre (u-v) u₀).trans
      (by nlinarith only [mul_le_mul hγhi ht (abs_nonneg (u-v-u₀)) (by positivity : 0≤3*α)])
  have hE1 : ‖E‖=1 := appendixB_imaginary_exp_norm hγre (u-v)
  have he : appendixBLogModel u v β γ-appendixBLogModel u₀ 0 β₀ γ=
      E*(A-A₀)+E*(B-B₀)+(E-E₀)*(A₀+B₀)-(B-B₀) := by
    dsimp [appendixBLogModel,A,A₀,B,B₀,E,E₀]
    simp only [sub_zero,zero_div,Complex.ofReal_zero]
    ring
  rw [he]
  calc
    _ ≤ ‖E*(A-A₀)+E*(B-B₀)+(E-E₀)*(A₀+B₀)‖+‖B-B₀‖ := norm_sub_le _ _
    _ ≤ (‖E*(A-A₀)‖+‖E*(B-B₀)‖+‖(E-E₀)*(A₀+B₀)‖)+‖B-B₀‖ :=
      by
        have hn₁ := norm_add_le (E*(A-A₀)+E*(B-B₀)) ((E-E₀)*(A₀+B₀))
        have hn₂ := norm_add_le (E*(A-A₀)) (E*(B-B₀))
        linarith only [hn₁,hn₂]
    _ ≤ (δ/α+4*h/q)+2*(δ/(α^2*q)+(3*α/α^2)*(10*h)/q^2)+
        (33*α*h)*(4+3*α/(α^2*q)) := by
      simp only [norm_mul,hE1,one_mul]
      have hAB : ‖A₀+B₀‖≤4+3*α/(α^2*q) := (norm_add_le _ _).trans (add_le_add hA₀ hB₀)
      have hm := mul_le_mul hE hAB (norm_nonneg _) (by positivity : 0≤33*α*h)
      linarith only [hA,hB,hm]
    _ = _ := rfl

end ZhangLS.Spec
