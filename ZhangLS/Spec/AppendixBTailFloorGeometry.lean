import ZhangLS.Spec.AppendixBTailSharpKernel

/-! Original finite cutoff floor(P) dominates twice every source cutoff.
This includes exact integer P and needs no generic cutoff premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec

lemma appendixB_two_p1_le_floor_p {D : ℕ} (hL : 3≤lemma23PaperL D) :
    2*lemma151P1 D≤(⌊lemma23PaperP D⌋₊ : ℝ) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hS : 0≤lemma23PaperL D^9 := pow_nonneg hLp.le 9
  have hSbig := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤3) hL 9
  have hP1exp : lemma151P1 D=Real.exp (0.504*lemma23PaperL D^9) := by
    rw [lemma151P1,appendixB_paper_power_exp]
  have hP1pos : 0<lemma151P1 D := by rw [hP1exp]; positivity
  have hP1one : 1≤lemma151P1 D := by
    rw [hP1exp]
    exact Real.one_le_exp (by positivity)
  have he : (3 : ℝ)≤Real.exp 2 := by
    have hh := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hexp : (3 : ℝ)≤Real.exp (0.496*lemma23PaperL D^9) := by
    apply he.trans
    apply Real.exp_le_exp.mpr
    norm_num at hSbig
    linarith
  have hthree : 3*lemma151P1 D≤lemma23PaperP D := by
    calc
      _ ≤ Real.exp (0.496*lemma23PaperL D^9)*lemma151P1 D :=
        mul_le_mul_of_nonneg_right hexp hP1pos.le
      _ = lemma23PaperP D := by
        rw [hP1exp,←Real.exp_add,lemma23PaperP]
        congr 1
        ring
  have hf := Nat.sub_one_lt_floor (lemma23PaperP D)
  linarith

lemma appendixB_source_cutoff_le_p1 {D l₁ : ℕ} (hL : 0<lemma23PaperL D)
    (hl : 0<l₁) {z : ℝ} (hz : z≤0.504) :
    Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ)≤lemma151P1 D := by
  calc
    _ ≤ Real.exp (z*lemma23PaperL D^9) :=
      div_le_self (Real.exp_pos _).le (by exact_mod_cast hl)
    _ ≤ Real.exp (0.504*lemma23PaperL D^9) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz (pow_nonneg hL.le 9))
    _ = lemma151P1 D := by rw [lemma151P1,appendixB_paper_power_exp]

/-- Both original far-Gaussian hypotheses hold uniformly in l1 and source z. -/
theorem appendixB_source_floor_geometry {D l₁ : ℕ} (hL : 3≤lemma23PaperL D)
    (hl : 0<l₁) {z : ℝ} (hz : z≤0.504) :
    2*(Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))≤(⌊lemma23PaperP D⌋₊ : ℝ) ∧
      Real.log (Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ))≤2*lemma23PaperL D^9 := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hx : 0<Real.exp (z*lemma23PaperL D^9)/(l₁ : ℝ) :=
    div_pos (Real.exp_pos _) (Nat.cast_pos.mpr hl)
  have hxp := appendixB_source_cutoff_le_p1 hLp hl hz
  refine ⟨(mul_le_mul_of_nonneg_left hxp (by norm_num)).trans (appendixB_two_p1_le_floor_p hL),?_⟩
  have hh := Real.log_le_log hx hxp
  rw [lemma151P1,appendixB_paper_power_exp,Real.log_exp] at hh
  have hS : 0≤lemma23PaperL D^9 := pow_nonneg hLp.le 9
  linarith

end ZhangLS.Spec
