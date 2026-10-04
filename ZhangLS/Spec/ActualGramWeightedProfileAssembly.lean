import ZhangLS.Spec.ActualGramBoxAttachment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact actual P7 main/error assembly for continuous profile values.
The main keeps the literal L'(1,chi)^2 and Pi(d,r), and only the proved Pi
collapse removes d,r from the main. Error aggregation uses the genuine
complex weight's absolute value and its proved finite mass bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical Interval

noncomputable def actualGramDifferentialFirst (D : ℕ) (c : ℝ) (j : Fin 3) (B : ℝ)
    (f f' : ℝ → ℂ) (t : ℝ) : ℂ := -f' t-(B : ℂ)*lemma83PaperBeta D c j*f t

noncomputable def actualGramDifferentialSecond (D : ℕ) (c : ℝ) (j : Fin 3) (B b : ℝ)
    (g g' : ℝ → ℂ) (t : ℝ) : ℂ :=
  -g' t+((B : ℂ)*lemma83PaperBeta D c (j+1)+(B : ℂ)*lemma83PaperBeta D c (j+2))*g t+
    ((B : ℂ)*lemma83PaperBeta D c (j+1))*((B : ℂ)*lemma83PaperBeta D c (j+2))*
      (∫ u in t..b, g u)

noncomputable def actualGramFirstProfileMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B : ℝ) (f f' : ℝ → ℂ) (q : ℕ) : ℂ :=
  (LDerivAtOne χ/(B : ℂ))*actualGramDifferentialFirst D c j B f f' (Real.log q/B)

noncomputable def actualGramSecondProfileMain {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (g g' : ℝ → ℂ) (d r : ℕ) : ℂ :=
  (LDerivAtOne χ*lemma83Pi χ d r/(B : ℂ))*
    actualGramDifferentialSecond D c j B b g g' (Real.log (d*r : ℕ)/B)

noncomputable def actualGramFiniteProfileKernel (D : ℕ) (c : ℝ) (j : Fin 3) (B b : ℝ)
    (f f' g g' : ℝ → ℂ) (n : ℕ) : ℂ :=
  actualGramDifferentialFirst D c j B f f' (Real.log n/B)*
    actualGramDifferentialSecond D c j B b g g' (Real.log n/B)

/-- The complete literal arithmetic S_j, with its exact ramified collapsed
main and the actual product residual. No evaluation of that residual is
assumed or hidden in the main definition. -/
theorem actualGram_P7_main_error_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (f f' g g' : ℝ → ℂ)
    (hK : ∀ n, n ∉ lemma81PolynomialIndices D → actualGramFiniteProfileKernel D c j B b f f' g g' n=0) :
    proposition71ArithmeticSum D c j
      (actualGramProfileSequence χ (fun n => f (Real.log n/B)))
      (actualGramProfileSequence χ (fun n => g (Real.log n/B))) -
    (LDerivAtOne χ^2/(B : ℂ)^2)*
      (∑ n ∈ lemma81PolynomialIndices D,
        (‖χ.evalNat n‖ : ℂ)*lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j)/
          (Nat.totient n : ℂ)*actualGramFiniteProfileKernel D c j B b f f' g g' n) =
    ∑ d ∈ lemma81PolynomialIndices D, ∑ r ∈ lemma81PolynomialIndices D,
      lemma84Section8Weight χ c j d r*
        (actualGramFirst χ c j (fun n => f (Real.log n/B)) (d*r)*
          (actualGramSecond χ c j (fun n => g (Real.log n/B)) d r-
            actualGramSecondProfileMain χ c j B b g g' d r) +
         (actualGramFirst χ c j (fun n => f (Real.log n/B)) (d*r)-
            actualGramFirstProfileMain χ c j B f f' (d*r))*
          actualGramSecondProfileMain χ c j B b g g' d r) := by
  rw [actualGram_P7_profile_factorization]
  rw [← actualGram_P7_box_main_attachment χ c j (actualGramFiniteProfileKernel D c j B b f f' g g') hK]
  simp_rw [mul_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro r hr
  unfold actualGramFirstProfileMain actualGramSecondProfileMain actualGramFiniteProfileKernel
  ring

/-- Quantitative residual bound on any genuine finite positive support set.
The four scalar pointwise inputs are supplied by the actual profile/kernel
bounds; the outer lambda/mu/chi/totient mass is proved internally. -/
theorem actualGram_weighted_profile_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (f f' g g' : ℝ → ℂ)
    (S : Finset (ℕ×ℕ)) (N : ℕ) (hS : S ⊆ (Icc 1 N)×ˢ(Icc 1 N))
    {y A E_F E_G M_G : ℝ} (hy : 1<y) (hA : 0≤A) (hEF : 0≤E_F)
    (hEG : 0≤E_G) (hMG : 0≤M_G)
    (hlog : ∀ dr ∈ S, Real.log (dr.1*dr.2 : ℕ)≤y)
    (hF : ∀ dr ∈ S, ‖actualGramFirst χ c j (fun n => f (Real.log n/B)) (dr.1*dr.2)‖≤A)
    (hFerr : ∀ dr ∈ S, ‖actualGramFirst χ c j (fun n => f (Real.log n/B)) (dr.1*dr.2)-
      actualGramFirstProfileMain χ c j B f f' (dr.1*dr.2)‖≤E_F)
    (hGerr : ∀ dr ∈ S, ‖actualGramSecond χ c j (fun n => g (Real.log n/B)) dr.1 dr.2-
      actualGramSecondProfileMain χ c j B b g g' dr.1 dr.2‖≤E_G)
    (hGmain : ∀ dr ∈ S, ‖actualGramSecondProfileMain χ c j B b g g' dr.1 dr.2‖≤M_G) :
    ‖∑ dr ∈ S, lemma84Section8Weight χ c j dr.1 dr.2*
      (actualGramFirst χ c j (fun n => f (Real.log n/B)) (dr.1*dr.2)*
        actualGramSecond χ c j (fun n => g (Real.log n/B)) dr.1 dr.2-
       actualGramFirstProfileMain χ c j B f f' (dr.1*dr.2)*
        actualGramSecondProfileMain χ c j B b g g' dr.1 dr.2)‖ ≤
      (2*lemma84WeightScale y*(harmonic N : ℝ))*(A*E_G+E_F*M_G) := by
  have hmass := lemma84_actual_weight_mass χ c j S N hS hy hlog
  have herr (dr : ℕ×ℕ) (hdr : dr ∈ S) :
      ‖actualGramFirst χ c j (fun n => f (Real.log n/B)) (dr.1*dr.2)*
        actualGramSecond χ c j (fun n => g (Real.log n/B)) dr.1 dr.2-
       actualGramFirstProfileMain χ c j B f f' (dr.1*dr.2)*
        actualGramSecondProfileMain χ c j B b g g' dr.1 dr.2‖≤A*E_G+E_F*M_G := by
    let F := actualGramFirst χ c j (fun n => f (Real.log n/B)) (dr.1*dr.2)
    let G := actualGramSecond χ c j (fun n => g (Real.log n/B)) dr.1 dr.2
    let F₀ := actualGramFirstProfileMain χ c j B f f' (dr.1*dr.2)
    let G₀ := actualGramSecondProfileMain χ c j B b g g' dr.1 dr.2
    change ‖F*G-F₀*G₀‖≤_
    rw [show F*G-F₀*G₀=F*(G-G₀)+(F-F₀)*G₀ by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    exact add_le_add (mul_le_mul (hF dr hdr) (hGerr dr hdr) (norm_nonneg _) hA)
      (mul_le_mul (hFerr dr hdr) (hGmain dr hdr) (norm_nonneg _) hEF)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ dr ∈ S, ‖lemma84Section8Weight χ c j dr.1 dr.2‖*(A*E_G+E_F*M_G) := by
      apply sum_le_sum
      intro dr hdr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (herr dr hdr) (norm_nonneg _)
    _ = (∑ dr ∈ S, ‖lemma84Section8Weight χ c j dr.1 dr.2‖)*(A*E_G+E_F*M_G) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass (by positivity)

/-- The literal first arithmetic sum vanishes beyond the profile ceiling.
Every positive original index m has log(q*m)/B >= log(q)/B. This is the
support restriction needed before invoking any interior xi estimate. -/
lemma actualGram_first_zero_past_profile {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (f : ℝ → ℂ) {B b : ℝ} (hB : 0<B)
    (q : ℕ) (hq : 0<q) (hqb : b≤Real.log q/B)
    (hf : ∀ t, b≤t → f t=0) :
    actualGramFirst χ c j (fun n => f (Real.log n/B)) q=0 := by
  unfold actualGramFirst
  apply sum_eq_zero
  intro m hm
  have hm0 := ((proposition71_mem_indices D m).mp hm).1
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hprod : (q : ℝ)≤(q*m : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_right q hm0
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hqR hprod) hB.le
  simp only [hf _ (hqb.trans hlog),mul_zero]

lemma actualGram_first_profile_main_zero_past {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (f f' : ℝ → ℂ) {B b : ℝ} (q : ℕ)
    (hqb : b≤Real.log q/B) (hf : ∀ t, b≤t → f t=0)
    (hfp : ∀ t, b≤t → f' t=0) :
    actualGramFirstProfileMain χ c j B f f' q=0 := by
  simp [actualGramFirstProfileMain,actualGramDifferentialFirst,hf _ hqb,hfp _ hqb]

noncomputable def actualGramProfileProductResidual {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (f f' g g' : ℝ → ℂ) (d r : ℕ) : ℂ :=
  actualGramFirst χ c j (fun n => f (Real.log n/B)) (d*r)*
    actualGramSecond χ c j (fun n => g (Real.log n/B)) d r-
  actualGramFirstProfileMain χ c j B f f' (d*r)*
    actualGramSecondProfileMain χ c j B b g g' d r

/-- Outside the true first-profile ceiling the whole actual product residual
is zero. No estimate for G or its Pi-dependent error is required there. -/
lemma actualGram_profile_product_residual_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (f f' g g' : ℝ → ℂ) (d r : ℕ)
    (hB : 0<B) (hd : 0<d) (hr : 0<r)
    (hqb : b≤Real.log (d*r : ℕ)/B) (hf : ∀ t, b≤t → f t=0)
    (hfp : ∀ t, b≤t → f' t=0) :
    actualGramProfileProductResidual χ c j B b f f' g g' d r=0 := by
  unfold actualGramProfileProductResidual
  rw [actualGram_first_zero_past_profile χ c j f hB (d*r) (Nat.mul_pos hd hr) hqb hf,
    actualGram_first_profile_main_zero_past χ c j f f' (d*r) hqb hf hfp]
  simp

/-- Restrict the full original positive P7 box to its genuine profile support
before using the real-x K2 range. Both sides are literal finite residuals
with the original complex Section 8 weight. -/
theorem actualGram_profile_residual_restrict {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (f f' g g' : ℝ → ℂ) (hB : 0<B)
    (hf : ∀ t, b≤t → f t=0) (hfp : ∀ t, b≤t → f' t=0) :
    (∑ dr ∈ (lemma81PolynomialIndices D)×ˢ(lemma81PolynomialIndices D),
      lemma84Section8Weight χ c j dr.1 dr.2*
        actualGramProfileProductResidual χ c j B b f f' g g' dr.1 dr.2) =
    ∑ dr ∈ ((lemma81PolynomialIndices D)×ˢ(lemma81PolynomialIndices D)).filter
        (fun dr : ℕ×ℕ => Real.log (dr.1*dr.2 : ℕ)/B≤b),
      lemma84Section8Weight χ c j dr.1 dr.2*
        actualGramProfileProductResidual χ c j B b f f' g g' dr.1 dr.2 := by
  rw [sum_filter]
  apply sum_congr rfl
  intro dr hdr
  by_cases hh : Real.log (dr.1*dr.2 : ℕ)/B≤b
  · rw [if_pos hh]
  · rw [if_neg hh]
    have hmem := mem_product.mp hdr
    have hd := ((proposition71_mem_indices D dr.1).mp hmem.1).1
    have hr := ((proposition71_mem_indices D dr.2).mp hmem.2).1
    rw [actualGram_profile_product_residual_zero χ c j B b f f' g g' dr.1 dr.2 hB hd hr
      (lt_of_not_ge hh).le hf hfp,mul_zero]

/-- The collapsed differential kernel inherits genuine original strict
support from the first profile, including the exceptional index n=0. This
removes a support predicate from the eventual P7 main attachment. -/
lemma actualGram_finite_profile_kernel_strict_support (D : ℕ) (c : ℝ) (j : Fin 3)
    (B b : ℝ) (f f' g g' : ℝ → ℂ) (hB : 0<B)
    (hceil : Real.exp (B*b)<lemma81Cutoff D) (hf0 : f 0=0) (hfp0 : f' 0=0)
    (hf : ∀ t, b≤t → f t=0) (hfp : ∀ t, b≤t → f' t=0) :
    ∀ n, n ∉ lemma81PolynomialIndices D → actualGramFiniteProfileKernel D c j B b f f' g g' n=0 := by
  intro n hn
  by_cases hn0 : n=0
  · subst n
    simp [actualGramFiniteProfileKernel,actualGramDifferentialFirst,hf0,hfp0]
  have hnp : 0<n := Nat.pos_of_ne_zero hn0
  have hnc : lemma81Cutoff D≤(n : ℝ) := by
    by_contra! hh
    exact hn ((proposition71_mem_indices D n).mpr ⟨hnp,hh⟩)
  have hlog := Real.log_le_log (Real.exp_pos (B*b)) (hceil.le.trans hnc)
  rw [Real.log_exp] at hlog
  have ht : b≤Real.log n/B := (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hlog)
  simp [actualGramFiniteProfileKernel,actualGramDifferentialFirst,hf _ ht,hfp _ ht]

/-- Literal original P7 minus its ramified collapsed main equals the actual
product residual only over the true profile ceiling. The displayed support
premises concern fixed profile values and original cutoff geometry; there
is no assumed arithmetic asymptotic or model Gram equality. -/
theorem actualGram_P7_main_error_supported {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (B b : ℝ) (f f' g g' : ℝ → ℂ) (hB : 0<B)
    (hceil : Real.exp (B*b)<lemma81Cutoff D) (hf0 : f 0=0) (hfp0 : f' 0=0)
    (hf : ∀ t, b≤t → f t=0) (hfp : ∀ t, b≤t → f' t=0) :
    proposition71ArithmeticSum D c j
      (actualGramProfileSequence χ (fun n => f (Real.log n/B)))
      (actualGramProfileSequence χ (fun n => g (Real.log n/B))) -
      (LDerivAtOne χ^2/(B : ℂ)^2)*
        (∑ n ∈ lemma81PolynomialIndices D,
          (‖χ.evalNat n‖ : ℂ)*lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j)/
            (Nat.totient n : ℂ)*actualGramFiniteProfileKernel D c j B b f f' g g' n) =
    ∑ dr ∈ ((lemma81PolynomialIndices D)×ˢ(lemma81PolynomialIndices D)).filter
        (fun dr : ℕ×ℕ => Real.log (dr.1*dr.2 : ℕ)/B≤b),
      lemma84Section8Weight χ c j dr.1 dr.2*
        actualGramProfileProductResidual χ c j B b f f' g g' dr.1 dr.2 := by
  have hK := actualGram_finite_profile_kernel_strict_support D c j B b f f' g g'
    hB hceil hf0 hfp0 hf hfp
  rw [actualGram_P7_main_error_identity χ c j B b f f' g g' hK]
  rw [← actualGram_profile_residual_restrict χ c j B b f f' g g' hB hf hfp]
  rw [← sum_product']
  apply sum_congr rfl
  intro dr hdr
  unfold actualGramProfileProductResidual
  ring

/-- The fixed profile ceiling discharges both actual analytic range
conditions on every active positive product: q is inside the original cutoff,
and every intermediate real x=exp(Bv)/q lies in [1,cutoff). -/
lemma actualGram_profile_inner_cutoffs (D : ℕ) {B b : ℝ} (hB : 0<B)
    (hceil : Real.exp (B*b)<lemma81Cutoff D) (q : ℕ) (hq : 0<q)
    (ht : Real.log q/B≤b) :
    (q : ℝ)<lemma81Cutoff D ∧
      ∀ v ∈ Set.Icc (Real.log q/B) b,
        1≤Real.exp (B*v)/(q : ℝ) ∧ Real.exp (B*v)/(q : ℝ)<lemma81Cutoff D := by
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast hq
  have hlogb : Real.log (q : ℝ)≤B*b := by
    simpa only [mul_comm] using (div_le_iff₀ hB).mp ht
  have hqe : (q : ℝ)≤Real.exp (B*b) := by
    simpa only [Real.exp_log hqR] using Real.exp_le_exp.mpr hlogb
  refine ⟨hqe.trans_lt hceil,?_⟩
  intro v hv
  have hlogv : Real.log (q : ℝ)≤B*v := by
    simpa only [mul_comm] using (div_le_iff₀ hB).mp hv.1
  have hx1 : 1≤Real.exp (B*v)/(q : ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    simpa only [one_mul,Real.exp_log hqR] using Real.exp_le_exp.mpr hlogv
  have hupper : Real.exp (B*v)/(q : ℝ)≤Real.exp (B*b) := by
    apply (div_le_iff₀ hqR).mpr
    calc
      _ ≤ Real.exp (B*b) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv.2 hB.le)
      _ ≤ Real.exp (B*b)*(q : ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 (Real.exp_pos (B*b)).le
  exact ⟨hx1,hupper.trans_lt hceil⟩

end ZhangLS.Spec
