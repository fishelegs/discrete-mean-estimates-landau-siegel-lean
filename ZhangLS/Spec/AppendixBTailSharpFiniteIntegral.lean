import ZhangLS.Spec.AppendixBTailSharpKernel

/-! Exact finite sharp-source assembly. The only sum/integral exchange here is
finite, and every interval-integrability witness is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical

noncomputable def appendixBSharpSourceTerm (D : ℕ) (β γ : ℂ) (l₁ n : ℕ) (z : ℝ) : ℂ :=
  appendixBRhoMonomialCoefficient (lemma151P1 D/(l₁ : ℝ)) β γ n*
    (((if (n : ℝ)<Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ) then 1 else 0)-
      (if (n : ℝ)<Real.exp (0.5*lemma23PaperL D^9)/(l₁ : ℝ) then 1 else 0) : ℝ) : ℂ)

noncomputable def appendixBSharpSourceSlice (D : ℕ) (β γ : ℂ) (l₁ N : ℕ) (z : ℝ) : ℂ :=
  ∑ n∈Finset.Icc 1 N, appendixBSharpSourceTerm D β γ l₁ n z

lemma appendixB_affine_log_step_intervalIntegrable {L : ℝ} (hL : 0<L)
    (a b v : ℝ) : IntervalIntegrable (fun z : ℝ =>
      appendixBStrictLogStep (L*z-v)-appendixBStrictLogStep (L*a-v)) volume a b := by
  let u := v/L
  have hv : v=u*L := by dsimp [u]; exact (div_mul_cancel₀ _ hL.ne').symm
  have he (z : ℝ) : L*z-v=L*(z-u) := by rw [hv]; ring
  simp_rw [he,appendixB_scaled_log_step hL]
  exact (appendixB_strict_step_intervalIntegrable a b u).sub intervalIntegrable_const

lemma appendixB_sharp_source_term_eq_log (D : ℕ) (β γ : ℂ)
    {l₁ n : ℕ} (hl : 0<l₁) (hn : 0<n) (z : ℝ) :
    appendixBSharpSourceTerm D β γ l₁ n z=
      (lemma151Rho β n/n)*((lemma151P1 D/((l₁*n : ℕ) : ℝ) : ℝ) : ℂ)^γ*
        ((appendixBStrictLogStep (lemma23PaperL D^9*z-Real.log ((l₁*n : ℕ) : ℝ))-
          appendixBStrictLogStep (lemma23PaperL D^9*0.5-Real.log ((l₁*n : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv : lemma151P1 D/(l₁ : ℝ)/(n : ℝ)=lemma151P1 D/((l₁*n : ℕ) : ℝ) := by
    rw [Nat.cast_mul,div_div]
  have hlog (t : ℝ) : Real.log (Real.exp (t*lemma23PaperL D^9)/(l₁ : ℝ)/(n : ℝ))=
      lemma23PaperL D^9*t-Real.log ((l₁*n : ℕ) : ℝ) := by
    rw [Real.log_div (div_pos (Real.exp_pos _) hlr).ne' hnr.ne',
      Real.log_div (Real.exp_pos _).ne' hlr.ne',Real.log_exp,Nat.cast_mul,
      Real.log_mul hlr.ne' hnr.ne']
    ring
  have hstep (t : ℝ) : appendixBStrictLogStep
      (lemma23PaperL D^9*t-Real.log ((l₁*n : ℕ) : ℝ))=
      if (n : ℝ)<Real.exp (t*lemma23PaperL D^9)/(l₁ : ℝ) then 1 else 0 := by
    have hh := appendixB_log_ratio_step (div_pos (Real.exp_pos (t*lemma23PaperL D^9)) hlr) hn
    rw [hlog] at hh
    exact hh
  unfold appendixBSharpSourceTerm appendixBRhoMonomialCoefficient
  rw [hdiv,←hstep z,←hstep (0.5 : ℝ)]

lemma appendixB_sharp_source_term_intervalIntegrable {D : ℕ}
    (hL : 0<lemma23PaperL D) (β γ : ℂ)
    {l₁ n : ℕ} (hl : 0<l₁) (hn : 0<n) :
    IntervalIntegrable (appendixBSharpSourceTerm D β γ l₁ n) volume (0.5 : ℝ) 0.504 := by
  have hS : 0<lemma23PaperL D^9 := by positivity
  have hs := appendixB_affine_log_step_intervalIntegrable hS (0.5 : ℝ) (0.504 : ℝ)
    (Real.log ((l₁*n : ℕ) : ℝ))
  have hc : IntervalIntegrable (fun z : ℝ =>
      ((appendixBStrictLogStep (lemma23PaperL D^9*z-Real.log ((l₁*n : ℕ) : ℝ))-
        appendixBStrictLogStep (lemma23PaperL D^9*0.5-Real.log ((l₁*n : ℕ) : ℝ)) : ℝ) : ℂ))
      volume (0.5 : ℝ) 0.504 := ⟨hs.1.ofReal,hs.2.ofReal⟩
  have hm := hc.const_mul ((lemma151Rho β n/n)*
    ((lemma151P1 D/((l₁*n : ℕ) : ℝ) : ℝ) : ℂ)^γ)
  have he : appendixBSharpSourceTerm D β γ l₁ n=(fun z : ℝ =>
      (lemma151Rho β n/n)*((lemma151P1 D/((l₁*n : ℕ) : ℝ) : ℝ) : ℂ)^γ*
        ((appendixBStrictLogStep (lemma23PaperL D^9*z-Real.log ((l₁*n : ℕ) : ℝ))-
          appendixBStrictLogStep (lemma23PaperL D^9*0.5-Real.log ((l₁*n : ℕ) : ℝ)) : ℝ) : ℂ)) := by
    funext z
    exact appendixB_sharp_source_term_eq_log D β γ hl hn z
  rw [he]
  exact hm

lemma appendixB_sharp_source_term_integral {D : ℕ}
    (hL : 0<lemma23PaperL D) (β γ : ℂ)
    {l₁ n : ℕ} (hl : 0<l₁) (hn : 0<n) :
    (1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504,
      appendixBSharpSourceTerm D β γ l₁ n z)=
    appendixBComplementKernel (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ)) γ (l₁*n)*
      lemma151Rho β n/n := by
  simp_rw [appendixB_sharp_source_term_eq_log D β γ hl hn]
  rw [appendixB_actual_complement_step_integral hL γ (Nat.mul_pos hl hn)]
  simp_rw [mul_assoc (lemma151Rho β n/(n : ℂ))]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma appendixB_sharp_source_slice_intervalIntegrable {D : ℕ}
    (hL : 0<lemma23PaperL D) (β γ : ℂ) {l₁ : ℕ} (hl : 0<l₁) (N : ℕ) :
    IntervalIntegrable (appendixBSharpSourceSlice D β γ l₁ N) volume (0.5 : ℝ) 0.504 := by
  have hh := IntervalIntegrable.sum (Finset.Icc 1 N) (fun n hn =>
    appendixB_sharp_source_term_intervalIntegrable hL β γ hl (Finset.mem_Icc.mp hn).1)
  convert hh using 1
  ext z
  simp only [appendixBSharpSourceSlice,Finset.sum_apply]

/-- Exact link to the actual sharp arithmetic tail. The n=floor(P) boundary is
retained, and sqrt(P) equality remains in the complementary kernel. -/
theorem appendixB_actual_complement_finite_integral {D : ℕ}
    (hL : 0<lemma23PaperL D) (β γ : ℂ) {l₁ : ℕ} (hl : 0<l₁) :
    appendixBComplementKernelSum (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ)) β γ l₁=
      (1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504,
        appendixBSharpSourceSlice D β γ l₁ ⌊lemma23PaperP D⌋₊ z) := by
  have hP : 1≤lemma23PaperP D := Real.one_le_exp (pow_nonneg hL.le 9)
  have hXP : lemma151P1 D≤lemma23PaperP D := by
    simpa only [lemma151P1,Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hP (show (0.504 : ℝ)≤1 by norm_num)
  rw [appendixB_complement_finite_sum β γ hl hXP]
  unfold appendixBSharpSourceSlice
  rw [intervalIntegral.integral_finsetSum (fun n hn =>
    appendixB_sharp_source_term_intervalIntegrable hL β γ hl (Finset.mem_Icc.mp hn).1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact (appendixB_sharp_source_term_integral hL β γ hl (Finset.mem_Icc.mp hn).1).symm

end ZhangLS.Spec
