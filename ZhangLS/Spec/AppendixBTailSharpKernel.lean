import ZhangLS.Spec.AppendixBTailRhoBounds
import ZhangLS.Spec.AppendixBTailSharpIntegral

/-! Exact bridge from the strict source complementary kernel to its integrated
strict steps. This is the actual kernel, including its lower endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Classical

lemma appendixB_integer_log_cutoff {L : ℝ} (hL : 0<L) (t : ℝ)
    {n : ℕ} (hn : 0<n) :
    ((n : ℝ)<Real.exp (t*L) ↔ Real.log (n : ℝ)/L<t) ∧
    (Real.exp (t*L)≤(n : ℝ) ↔ t≤Real.log (n : ℝ)/L) := by
  have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  constructor
  · rw [←Real.log_lt_log_iff hnr (Real.exp_pos _),Real.log_exp,div_lt_iff₀ hL]
  · rw [←Real.log_le_log_iff (Real.exp_pos _) hnr,Real.log_exp,le_div_iff₀ hL]

lemma appendixB_exponential_complement_ramp {L b : ℝ} (hL : 0<L) (hb : 0<b)
    (a : ℝ) (γ : ℂ) {n : ℕ} (hn : 0<n) :
    appendixBComplementKernel (Real.exp (b*L)) (Real.exp (a*L)) γ n=
      ((Real.exp (b*L)/(n : ℝ) : ℝ) : ℂ)^γ*
        (((if a≤Real.log (n : ℝ)/L then max (b-Real.log (n : ℝ)/L) 0 else 0)/b : ℝ) : ℂ) := by
  let u := Real.log (n : ℝ)/L
  have hupper := (appendixB_integer_log_cutoff hL b hn).1
  have hlower := (appendixB_integer_log_cutoff hL a hn).2
  have hlog : Real.log (n : ℝ)=u*L := by
    dsimp [u]
    exact (div_mul_cancel₀ _ hL.ne').symm
  unfold appendixBComplementKernel lemma151Kernel
  simp only [hn,true_and,hupper,hlower,Real.log_exp]
  change (if a≤u then (if u<b then (1-(Real.log (n : ℝ) : ℂ)/((b*L : ℝ) : ℂ))*
      ((Real.exp (b*L)/(n : ℝ) : ℝ) : ℂ)^γ else 0) else 0)=
    ((Real.exp (b*L)/(n : ℝ) : ℝ) : ℂ)^γ*(((if a≤u then max (b-u) 0 else 0)/b : ℝ) : ℂ)
  by_cases hlo : a≤u
  · by_cases hup : u<b
    · simp only [if_pos hlo,if_pos hup,max_eq_left (sub_nonneg.mpr hup.le)]
      rw [hlog]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hL.ne',Complex.ofReal_ne_zero.mpr hb.ne']
      <;> ring
    · simp only [if_pos hlo,if_neg hup,max_eq_right (sub_nonpos.mpr (le_of_not_gt hup)),
        zero_div,Complex.ofReal_zero,mul_zero]
  · simp only [if_neg hlo,zero_div,Complex.ofReal_zero,mul_zero]

lemma appendixB_log_step_difference_integral {L : ℝ} (hL : 0<L)
    (a b : ℝ) (hab : a≤b) {n : ℕ} (hn : 0<n) :
    (∫ z : ℝ in a..b,
      (appendixBStrictLogStep (L*z-Real.log (n : ℝ))-
        appendixBStrictLogStep (L*a-Real.log (n : ℝ))))=
      if a≤Real.log (n : ℝ)/L then max (b-Real.log (n : ℝ)/L) 0 else 0 := by
  let u := Real.log (n : ℝ)/L
  have hlog : Real.log (n : ℝ)=u*L := by
    dsimp [u]
    exact (div_mul_cancel₀ _ hL.ne').symm
  have harg (z : ℝ) : L*z-Real.log (n : ℝ)=L*(z-u) := by rw [hlog]; ring
  simp_rw [harg]
  exact appendixB_scaled_step_difference_integral hL a b u hab

/-- Honest strict-step integral formula for the complementary exponential kernel. -/
theorem appendixB_exponential_complement_integral {L b : ℝ} (hL : 0<L) (hb : 0<b)
    (a : ℝ) (hab : a≤b) (γ : ℂ) {n : ℕ} (hn : 0<n) :
    appendixBComplementKernel (Real.exp (b*L)) (Real.exp (a*L)) γ n=
      (1/(b : ℂ))*(∫ z : ℝ in a..b,
        ((Real.exp (b*L)/(n : ℝ) : ℝ) : ℂ)^γ*
          ((appendixBStrictLogStep (L*z-Real.log (n : ℝ))-
            appendixBStrictLogStep (L*a-Real.log (n : ℝ)) : ℝ) : ℂ)) := by
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,
    appendixB_log_step_difference_integral hL a b hab hn,
    appendixB_exponential_complement_ramp hL hb a γ hn]
  push_cast
  ring

lemma appendixB_paper_power_exp (D : ℕ) (r : ℝ) :
    (lemma23PaperP D)^r=Real.exp (r*lemma23PaperL D^9) := by
  rw [lemma23PaperP,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  congr 1
  ring

/-- The strict H14 complement itself, with its exact original P1 and sqrt(P). -/
theorem appendixB_actual_complement_step_integral {D : ℕ}
    (hL : 0<lemma23PaperL D) (γ : ℂ) {n : ℕ} (hn : 0<n) :
    appendixBComplementKernel (lemma151P1 D) ((lemma23PaperP D)^(1/2 : ℝ)) γ n=
      (1/0.504 : ℂ)*(∫ z : ℝ in (0.5 : ℝ)..0.504,
        ((lemma151P1 D/(n : ℝ) : ℝ) : ℂ)^γ*
          ((appendixBStrictLogStep (lemma23PaperL D^9*z-Real.log (n : ℝ))-
            appendixBStrictLogStep (lemma23PaperL D^9*0.5-Real.log (n : ℝ)) : ℝ) : ℂ)) := by
  have hS : 0<lemma23PaperL D^9 := by positivity
  rw [lemma151P1,appendixB_paper_power_exp,appendixB_paper_power_exp]
  have hh := appendixB_exponential_complement_integral hS (show (0 : ℝ)<0.504 by norm_num)
    (0.5 : ℝ) (by norm_num) γ hn
  convert hh using 1 <;> norm_num

/-- The genuinely finite representation of the complementary arithmetic tail. -/
theorem appendixB_complement_finite_sum {X Y Z : ℝ} (β γ : ℂ)
    {l₁ : ℕ} (hl : 0<l₁) (hXZ : X≤Z) :
    appendixBComplementKernelSum X Y β γ l₁=
      ∑ n∈Finset.Icc 1 ⌊Z⌋₊,
        appendixBComplementKernel X Y γ (l₁*n)*lemma151Rho β n/n := by
  unfold appendixBComplementKernelSum
  apply tsum_eq_sum
  intro n hnout
  by_cases hn : n=0
  · simp [hn]
  have hnpos : 0<n := Nat.pos_of_ne_zero hn
  have hnN : ¬n≤⌊Z⌋₊ := by
    intro h
    exact hnout (Finset.mem_Icc.mpr ⟨hnpos,h⟩)
  have hZn : Z<(n : ℝ) := Nat.lt_of_floor_lt (Nat.lt_of_not_ge hnN)
  have hprod : X≤((l₁*n : ℕ) : ℝ) :=
    hXZ.trans (hZn.le.trans (by exact_mod_cast Nat.le_mul_of_pos_left n hl))
  rw [appendixB_complement_zero_at_or_above γ hprod]
  simp

end ZhangLS.Spec
