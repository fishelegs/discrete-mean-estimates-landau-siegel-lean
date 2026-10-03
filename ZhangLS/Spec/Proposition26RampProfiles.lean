import ZhangLS.Spec.Proposition26ProfileBV
import ZhangLS.Spec.Proposition26OriginalObjects
import ZhangLS.Spec.Lemma82OriginalBridge

/-! The actual H₂ components have monotone ramp profiles once their original
purely imaginary powers are placed in the frequency parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def proposition26Ramp (X : ℝ) (n : ℕ) : ℝ :=
  max (1-Real.log (n:ℝ)/Real.log X) 0

lemma proposition26_ramp_nonneg (X : ℝ) (n : ℕ) : 0≤proposition26Ramp X n := le_max_right _ _

lemma proposition26_ramp_le_one {X : ℝ} (hX : 1<X) (n : ℕ) :
    proposition26Ramp X n≤1 := by
  have hlog : 0<Real.log X := Real.log_pos hX
  apply max_le
  · have h := div_nonneg (Real.log_natCast_nonneg n) hlog.le
    linarith
  · norm_num

lemma proposition26_ramp_antitone_positive {X : ℝ} (hX : 1<X)
    {m n : ℕ} (hm : 0<m) (hmn : m≤n) :
    proposition26Ramp X n≤proposition26Ramp X m := by
  have hl := Real.log_le_log (by exact_mod_cast hm : (0:ℝ)<m)
    (by exact_mod_cast hmn : (m:ℝ)≤n)
  apply max_le_max_right
  exact sub_le_sub_left (div_le_div_of_nonneg_right hl (Real.log_pos hX).le) 1

lemma proposition26_ramp_zero {X : ℝ} (hX : 1<X) {n : ℕ} (hn : X≤(n:ℝ)) :
    proposition26Ramp X n=0 := by
  have hlog : 0<Real.log X := Real.log_pos hX
  have hl := Real.log_le_log (by linarith : 0<X) hn
  have hdiv : 1≤Real.log (n:ℝ)/Real.log X := (le_div_iff₀ hlog).mpr (by simpa using hl)
  exact max_eq_right (by linarith)

lemma proposition26_ramp_original {X : ℝ} (hX : 1<X) {n : ℕ}
    (hn : 0<n) (hnX : (n:ℝ)<X) :
    proposition26Ramp X n=1-Real.log (n:ℝ)/Real.log X := by
  have hlog : 0<Real.log X := Real.log_pos hX
  have hl := Real.log_le_log (by exact_mod_cast hn : (0:ℝ)<n) hnX.le
  have hdiv : Real.log (n:ℝ)/Real.log X≤1 := (div_le_one hlog).mpr hl
  exact max_eq_left (by linarith)

/-- Any nonnegative, decreasing positive-index profile bounded by one has
exact endpoint-plus-variation norm at most one on every multiplicative sample. -/
theorem proposition26_positive_antitone_variation (w : ℕ→ℝ)
    (hnon : ∀n:ℕ,0<n → 0≤w n) (hone : ∀n:ℕ,0<n → w n≤1)
    (hmono : ∀m n:ℕ,0<m → m≤n → w n≤w m) :
    Proposition26VariationBound (fun n => (w n:ℂ)) 1 := by
  refine ⟨by norm_num,?_⟩
  intro q N hq
  let f : ℕ→ℝ := fun i => w (q*(i+1))
  have hm (i : ℕ) : f (i+1)≤f i :=
    hmono _ _ (Nat.mul_pos hq (Nat.succ_pos i)) (Nat.mul_le_mul_left q (by omega))
  have he : (∑i∈range (N-1),‖(w (q*(i+2)):ℂ)-(w (q*(i+1)):ℂ)‖)=
      f 0-f (N-1) := by
    calc
      _ = ∑i∈range (N-1),(f i-f (i+1)) := by
        apply sum_congr rfl
        intro i hi
        rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        have hh : w (q*(i+2))-w (q*(i+1))≤0 := by
          simpa [f,Nat.add_assoc] using sub_nonpos.mpr (hm i)
        rw [abs_of_nonpos hh]
        simp [f,Nat.add_assoc]
      _ = _ := Finset.sum_range_sub' f (N-1)
  rw [he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (hnon _ (Nat.mul_pos hq (Nat.succ_pos (N-1))))]
  have hfirst := hone q hq
  dsimp [f]
  simp only [mul_one]
  linarith only [hfirst]

/-- The literal linear-logarithmic ramp has variation at most one. -/
theorem proposition26_ramp_variation {X : ℝ} (hX : 1<X) :
    Proposition26VariationBound (fun n => (proposition26Ramp X n:ℂ)) 1 :=
  proposition26_positive_antitone_variation (proposition26Ramp X)
    (fun n _hn => proposition26_ramp_nonneg X n)
    (fun n _hn => proposition26_ramp_le_one hX n)
    (fun _m _n hm hmn => proposition26_ramp_antitone_positive hX hm hmn)

noncomputable def proposition26Indicator (X : ℝ) (n : ℕ) : ℂ :=
  if (n:ℝ)<X then 1 else 0

lemma proposition26_indicator_variation (X : ℝ) :
    Proposition26VariationBound (proposition26Indicator X) 1 := by
  have h := proposition26_positive_antitone_variation
    (fun n => if (n:ℝ)<X then (1:ℝ) else 0)
    (fun n _hn => by dsimp only; split_ifs <;> norm_num)
    (fun n _hn => by dsimp only; split_ifs <;> norm_num)
    (fun m n hm hmn => by
      by_cases hnx : (n:ℝ)<X
      · have hmx : (m:ℝ)<X := (by exact_mod_cast hmn : (m:ℝ)≤n).trans_lt hnx
        simp [hnx,hmx]
      · simp only [if_neg hnx]
        split_ifs <;> norm_num)
  simpa only [proposition26Indicator,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h

lemma proposition26_ramp_support {D : ℕ} {X : ℝ} (hX : 1<X)
    (hcut : X≤lemma81Cutoff D) :
    ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → (proposition26Ramp X n:ℂ)=0 := by
  intro n hn
  rw [proposition26_ramp_zero hX (hcut.trans hn),Complex.ofReal_zero]

lemma proposition26_smoothing_beta_eq_imag (D μ : ℕ) :
    lemma82SmoothingBeta D μ=I*((lemma82SmoothingBeta D μ).im:ℂ) := by
  apply Complex.ext <;> simp [lemma82_smoothing_beta_re]

/-- Exact actual H-component/polynomial identity, including the original
complex phase and strict endpoint. -/
theorem proposition26_HComponent_polynomial {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    {X : ℝ} (hX : 1<X) (hcut : X≤lemma81Cutoff D) (μ : ℕ) :
    proposition26HComponent χ ψ X μ s =
      (X:ℂ)^(lemma82SmoothingBeta D μ)*
        lemma81Polynomial D
          (proposition26TwistedCoefficient χ (lemma82SmoothingBeta D μ).im
            (fun n => (proposition26Ramp X n:ℂ))) ψ s := by
  let a := proposition26TwistedCoefficient χ (lemma82SmoothingBeta D μ).im
    (fun n => (proposition26Ramp X n:ℂ))
  have hsub : lemma82StrictCutoff X⊆lemma81PolynomialIndices D := by
    intro n hn
    have hm := (lemma82_mem_strictCutoff (by linarith : 0≤X) n).mp hn
    exact (proposition71_mem_indices D n).mpr ⟨hm.1,hm.2.trans_le hcut⟩
  have he : (∑n∈lemma82StrictCutoff X,a n*ψ (n:ZMod p)/(n:ℂ)^s)=
      lemma81Polynomial D a ψ s := by
    unfold lemma81Polynomial
    apply sum_subset hsub
    intro n hn hnot
    have hp := ((proposition71_mem_indices D n).mp hn).1
    have hge : X≤(n:ℝ) := by
      by_contra h
      exact hnot ((lemma82_mem_strictCutoff (by linarith : 0≤X) n).mpr ⟨hp,lt_of_not_ge h⟩)
    simp [a,proposition26TwistedCoefficient,proposition26_ramp_zero hX hge]
  rw [←he,Finset.mul_sum]
  unfold proposition26HComponent
  apply sum_congr rfl
  intro n hn
  have hm := (lemma82_mem_strictCutoff (by linarith : 0≤X) n).mp hn
  have hramp := proposition26_ramp_original hX hm.1 hm.2
  have hratio := lemma82_positive_ratio_cpow (by linarith : 0<X)
    (by exact_mod_cast hm.1 : (0:ℝ)<n) (lemma82SmoothingBeta D μ)
  rw [hratio,Complex.ofReal_natCast]
  dsimp [a,proposition26TwistedCoefficient,lemma112Coefficient]
  rw [if_neg hm.1.ne',hramp,neg_mul,←proposition26_smoothing_beta_eq_imag]
  ring

lemma proposition26_HComponent_phase_norm {X : ℝ} (hX : 0<X) (D μ : ℕ) :
    ‖(X:ℂ)^(lemma82SmoothingBeta D μ)‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX,lemma82_smoothing_beta_re,Real.rpow_zero]

end ZhangLS.Spec
