import ZhangLS.Spec.ActualGramFiniteSuperposition
import ZhangLS.Spec.ActualGramArithmeticAttachment
import ZhangLS.Spec.Lemma82Definitions
import ZhangLS.Spec.Lemma84Definitions

/-! Exact logarithmic scaling between clipped ramps and the original real-x
smoothed kernels. Strict cutoffs and their zero logarithmic endpoints are
retained. This bridges the fixed-interval calculus to the actual finite
arithmetic sums, before any analytic approximation is applied. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset Complex MeasureTheory
open scoped Classical Interval

noncomputable def actualGramLogSmoothedSum (coeff : ℕ → ℂ) (gamma : ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ lemma82StrictCutoff x, coeff m*((x/(m : ℝ) : ℝ) : ℂ)^gamma*
    (Real.log (x/(m : ℝ)) : ℂ)

/-- The exact B factor and the strict moving endpoint, including equality. -/
lemma actualGram_log_smoothing_term (gamma : ℂ) {B q : ℝ} (hB : 0<B) (hq : 0<q)
    {m : ℕ} (hm : 0<m) (v : ℝ) :
    (B : ℂ)*actualGramClippedRamp ((B : ℂ)*gamma) (Real.log (q*(m : ℝ))/B) v =
      if (m : ℝ)<Real.exp (B*v)/q then
        (((Real.exp (B*v)/q)/(m : ℝ) : ℝ) : ℂ)^gamma*
          (Real.log ((Real.exp (B*v)/q)/(m : ℝ)) : ℂ) else 0 := by
  let t : ℝ := Real.log (q*(m : ℝ))/B
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr hm
  have hraw : (m : ℝ)<Real.exp (B*v)/q ↔ Real.log (q*(m : ℝ))<B*v := by
    rw [lt_div_iff₀ hq]
    have h := (Real.log_lt_log_iff (mul_pos hq hmR) (Real.exp_pos (B*v))).symm
    simpa only [Real.log_exp,mul_comm] using h
  have hcut : (m : ℝ)<Real.exp (B*v)/q ↔ t<v := by
    dsimp [t]
    rw [div_lt_iff₀ hB]
    simpa only [mul_comm] using hraw
  have hlog : Real.log ((Real.exp (B*v)/q)/(m : ℝ))=B*(v-t) := by
    rw [div_div,Real.log_div (Real.exp_ne_zero _) (mul_ne_zero hq.ne' hmR.ne'),Real.log_exp]
    dsimp [t]
    field_simp [hB.ne'] <;> ring
  by_cases hc : (m : ℝ)<Real.exp (B*v)/q
  · rw [if_pos hc,actualGram_clipped_ramp_of_le ((B : ℂ)*gamma) (by exact (hcut.mp hc).le)]
    have hp : ((((Real.exp (B*v)/q)/(m : ℝ) : ℝ) : ℂ)^gamma) =
        Complex.exp (((B : ℂ)*gamma)*((v-t : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)),
        ← Complex.ofReal_log (by positivity),hlog]
      push_cast
      congr 1
      ring
    rw [hp,hlog]
    change (B : ℂ)*(((v-t : ℝ) : ℂ)*Complex.exp (((B : ℂ)*gamma)*((v-t : ℝ) : ℂ))) = _
    push_cast
    ring
  · rw [if_neg hc]
    have ht : v≤t := not_lt.mp (fun h => hc (hcut.mpr h))
    rw [actualGram_clipped_ramp_of_ge ((B : ℂ)*gamma) ht,mul_zero]

lemma actualGram_smoothing_cutoff_inside_original {D : ℕ} {x : ℝ}
    (hx : 0≤x) (hcut : x≤lemma81Cutoff D) :
    (lemma81PolynomialIndices D).filter (fun m : ℕ => (m : ℝ)<x)=lemma82StrictCutoff x := by
  ext m
  rw [mem_filter,proposition71_mem_indices,lemma82_mem_strictCutoff hx]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2.trans_le hcut⟩,h.2⟩

/-- The whole original finite index set produces exactly the strict original
smoothed sum, with an explicit B^-1 factor. -/
theorem actualGram_clipped_sum_eq_smoothed (D : ℕ) (coeff : ℕ → ℂ) (gamma : ℂ)
    {B q : ℝ} (hB : 0<B) (hq : 0<q) (v : ℝ)
    (hcut : Real.exp (B*v)/q≤lemma81Cutoff D) :
    (∑ m ∈ lemma81PolynomialIndices D, coeff m*
      actualGramClippedRamp ((B : ℂ)*gamma) (Real.log (q*(m : ℝ))/B) v) =
      (B : ℂ)⁻¹*actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q) := by
  have hx : 0<Real.exp (B*v)/q := by positivity
  have he : (B : ℂ)*(∑ m ∈ lemma81PolynomialIndices D, coeff m*
      actualGramClippedRamp ((B : ℂ)*gamma) (Real.log (q*(m : ℝ))/B) v) =
      actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q) := by
    rw [mul_sum]
    calc
      _ = ∑ m ∈ lemma81PolynomialIndices D,
          if (m : ℝ)<Real.exp (B*v)/q then coeff m*
            ((((Real.exp (B*v)/q)/(m : ℝ) : ℝ) : ℂ)^gamma)*
              (Real.log ((Real.exp (B*v)/q)/(m : ℝ)) : ℂ) else 0 := by
        apply sum_congr rfl
        intro m hm
        have hm0 := ((proposition71_mem_indices D m).mp hm).1
        rw [mul_left_comm,actualGram_log_smoothing_term gamma hB hq hm0 v]
        split_ifs <;> ring
      _ = _ := by
        rw [← sum_filter,actualGram_smoothing_cutoff_inside_original hx.le hcut]
        rfl
  have hBC : (B : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  apply mul_left_cancel₀ hBC
  rw [he]
  simp [← mul_assoc,hBC]

/-- Exact superposition on the fixed profile interval into the real-x kernel.
The cutoff condition is checked at each v and is not extended by fiat. -/
theorem actualGram_log_smoothed_superposition (D : ℕ) (coeff : ℕ → ℂ) (gamma : ℂ)
    (f f' f'' : ℝ → ℂ) {a b B q : ℝ} (hab : a≤b) (hB : 0<B) (hq : 0<q)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hzleft : ∀ v≤a, actualGramRampDensity ((B : ℂ)*gamma) f f' f'' v=0)
    (hzright : ∀ v, b≤v → f v=0) (hfpb : f' b=0)
    (hcut : ∀ v ∈ Set.Icc a b, Real.exp (B*v)/q≤lemma81Cutoff D) :
    (∑ m ∈ lemma81PolynomialIndices D, coeff m*f (Real.log (q*(m : ℝ))/B)) =
      (B : ℂ)⁻¹*(∫ v in a..b, actualGramRampDensity ((B : ℂ)*gamma) f f' f'' v*
        actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q)) := by
  rw [actualGram_finite_ramp_superposition (lemma81PolynomialIndices D) coeff
    (fun m => Real.log (q*(m : ℝ))/B) ((B : ℂ)*gamma) f f' f'' hab hf hf' hf'' hzleft hzright hfpb]
  calc
    _ = ∫ v in a..b, (B : ℂ)⁻¹*(actualGramRampDensity ((B : ℂ)*gamma) f f' f'' v*
        actualGramLogSmoothedSum coeff gamma (Real.exp (B*v)/q)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      have hv' : v ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hv
      rw [actualGram_clipped_sum_eq_smoothed D coeff gamma hB hq v (hcut v hv')]
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The generic finite kernel is definitionally the actual original K1. -/
lemma actualGram_log_kernel_first {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ : ℕ) (x : ℝ) :
    actualGramLogSmoothedSum
      (fun n => χ.evalNat n/(n : ℂ)^(1-lemma83PaperBeta D c j))
      (lemma82SmoothingBeta D μ) x = lemma82ShiftedSum χ c j μ x := by
  rfl

/-- The actual xi and the opposite smoothing shift are retained in K2. -/
lemma actualGram_log_kernel_second {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (x : ℝ) :
    actualGramLogSmoothedSum
      (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n : ℂ))
      (-lemma84SmoothingBeta D μ) x = lemma84XiSum χ c j μ d r x := by
  rfl

/-- Literal first arithmetic inner sum attached to the original real-x K1. -/
theorem actualGram_first_smoothed_superposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ q : ℕ) (hq : 0<q) (f f' f'' : ℝ → ℂ)
    {a b B : ℝ} (hab : a≤b) (hB : 0<B)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hzleft : ∀ v≤a, actualGramRampDensity ((B : ℂ)*lemma82SmoothingBeta D μ) f f' f'' v=0)
    (hzright : ∀ v, b≤v → f v=0) (hfpb : f' b=0)
    (hcut : ∀ v ∈ Set.Icc a b, Real.exp (B*v)/(q : ℝ)≤lemma81Cutoff D) :
    actualGramFirst χ c j (fun n => f (Real.log n/B)) q =
      (B : ℂ)⁻¹*(∫ v in a..b,
        actualGramRampDensity ((B : ℂ)*lemma82SmoothingBeta D μ) f f' f'' v*
          lemma82ShiftedSum χ c j μ (Real.exp (B*v)/(q : ℝ))) := by
  have h := actualGram_log_smoothed_superposition D
    (fun n => χ.evalNat n/(n : ℂ)^(1-lemma83PaperBeta D c j))
    (lemma82SmoothingBeta D μ) f f' f'' hab hB (Nat.cast_pos.mpr hq)
      hf hf' hf'' hzleft hzright hfpb hcut
  simpa only [actualGramFirst,Nat.cast_mul,actualGram_log_kernel_first] using h

/-- Literal xi inner sum, retaining d,r and using the opposite smoothing
shift. Apply this to the conjugate second profile for a Hermitian entry. -/
theorem actualGram_second_smoothed_superposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (hd : 0<d) (hr : 0<r) (g g' g'' : ℝ → ℂ)
    {a b B : ℝ} (hab : a≤b) (hB : 0<B)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : Continuous g'')
    (hzleft : ∀ v≤a, actualGramRampDensity ((B : ℂ)*(-lemma84SmoothingBeta D μ)) g g' g'' v=0)
    (hzright : ∀ v, b≤v → g v=0) (hgpb : g' b=0)
    (hcut : ∀ v ∈ Set.Icc a b, Real.exp (B*v)/(d*r : ℕ)≤lemma81Cutoff D) :
    actualGramSecond χ c j (fun n => g (Real.log n/B)) d r =
      (B : ℂ)⁻¹*(∫ v in a..b,
        actualGramRampDensity ((B : ℂ)*(-lemma84SmoothingBeta D μ)) g g' g'' v*
          lemma84XiSum χ c j μ d r (Real.exp (B*v)/(d*r : ℕ))) := by
  have h := actualGram_log_smoothed_superposition D
    (fun n => χ.evalNat n*lemma83Xi (lemma83PaperBeta D c) j n d r/(n : ℂ))
    (-lemma84SmoothingBeta D μ) g g' g'' hab hB (Nat.cast_pos.mpr (Nat.mul_pos hd hr))
      hg hg' hg'' hzleft hzright hgpb hcut
  simpa only [actualGramSecond,Nat.cast_mul,actualGram_log_kernel_second] using h

end ZhangLS.Spec
