import ZhangLS.Spec.AppendixBTailGaussianMellin
import ZhangLS.Spec.Lemma61GaussianCutoff

/-! The infinite Gaussian tail above a genuine numeric cutoff. The elementary
coefficient bound is separated so the pending global rho estimate can fill it. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory

lemma appendixB_far_gaussian_term_bound {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) {x : ℝ} (hx : 0<x)
    (hlog : Real.log x≤2*lemma23PaperL D^9) (N : ℕ)
    (hcut : 2*x≤(N : ℝ)) (a : ℕ→ℂ) (ha : ∀ n : ℕ, ‖a n‖≤1) (n : ℕ) :
    ‖if N<n then a n*(zhangGaussianWeight D (x/n) : ℂ) else 0‖≤
      Real.exp (-(lemma23PaperL D^10))*((n : ℝ)^2)⁻¹ := by
  by_cases hn : N<n
  · rw [if_pos hn,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hnp : 0<n := Nat.zero_lt_of_lt hn
    have hnr : 0<(n : ℝ) := Nat.cast_pos.mpr hnp
    have hg : 0≤zhangGaussianWeight D (x/n) :=
      zhangGaussianWeight_nonneg hD (div_pos hx hnr)
    rw [abs_of_nonneg hg]
    have hcutn : 2*x≤(n : ℝ) := hcut.trans (by exact_mod_cast hn.le)
    exact (mul_le_mul (ha n) (lemma61_cutoff_gaussian_weight_bound hL hx hlog hnp hcutn)
      hg zero_le_one).trans_eq (one_mul _)
  · rw [if_neg hn,norm_zero]
    positivity

/-- Honest summability plus a summable n^-2 envelope for the entire far tail. -/
theorem appendixB_far_gaussian_summable_bound {D : ℕ} (hD : 1<D)
    (hL : 3≤lemma23PaperL D) {x : ℝ} (hx : 0<x)
    (hlog : Real.log x≤2*lemma23PaperL D^9) (N : ℕ)
    (hcut : 2*x≤(N : ℝ)) (a : ℕ→ℂ) (ha : ∀ n : ℕ, ‖a n‖≤1) :
    Summable (fun n : ℕ => if N<n then a n*(zhangGaussianWeight D (x/n) : ℂ) else 0) ∧
    ‖∑' n : ℕ, if N<n then a n*(zhangGaussianWeight D (x/n) : ℂ) else 0‖≤
      lemma44InverseSquareMass*Real.exp (-(lemma23PaperL D^10)) := by
  have hs := lemma44_inverse_square_summable.mul_left (Real.exp (-(lemma23PaperL D^10)))
  have hn : Summable (fun n : ℕ =>
      ‖if N<n then a n*(zhangGaussianWeight D (x/n) : ℂ) else 0‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _)
      (appendixB_far_gaussian_term_bound hD hL hx hlog N hcut a ha)
  refine ⟨hn.of_norm,?_⟩
  calc
    _ ≤ ∑' n : ℕ, ‖if N<n then a n*(zhangGaussianWeight D (x/n) : ℂ) else 0‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, Real.exp (-(lemma23PaperL D^10))*((n : ℝ)^2)⁻¹ :=
      hn.tsum_le_tsum (appendixB_far_gaussian_term_bound hD hL hx hlog N hcut a ha) hs
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

end ZhangLS.Spec
