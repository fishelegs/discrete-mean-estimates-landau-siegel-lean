import ZhangLS.Spec.AppendixBKernelErrorDecay
import ZhangLS.Spec.BSourceRegressions

/-! Literal-object, endpoint and final-constant regressions. The full P1 result
is not the truncated H14 result. No character or Assumption (A) is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex Filter
open scoped Classical Topology

@[simp] theorem appendixB_original_P1 (D : ℕ) : appendixBOriginalCutoff D 0=lemma151P1 D := rfl
@[simp] theorem appendixB_original_P2 (D : ℕ) : appendixBOriginalCutoff D 1=lemma151P2 D := rfl
@[simp] theorem appendixB_original_P3 (D : ℕ) : appendixBOriginalCutoff D 2=lemma151P3 D := rfl
@[simp] theorem appendixB_original_gamma_P1 (D : ℕ) : appendixBOriginalGamma D 0=lemma151Beta6 D := rfl
@[simp] theorem appendixB_original_gamma_P2 (D : ℕ) : appendixBOriginalGamma D 1=lemma151Beta7 D := rfl
@[simp] theorem appendixB_original_gamma_P3 (D : ℕ) : appendixBOriginalGamma D 2=lemma151Beta6 D := rfl

theorem appendixB_P2_source_expanded (D : ℕ) :
    appendixBOriginalCutoff D 1=(lemma23PaperP D)^(0.5 : ℝ)*lemma56PaperT D^(-10 : ℤ) := rfl

theorem appendixB_beta_one_source (D : ℕ) (c : ℝ) :
    lemma83PaperBeta D c 0=I*((lemma44PaperAlpha D*
      (1-5*c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) := rfl

theorem appendixB_beta_two_source (D : ℕ) (c : ℝ) :
    lemma83PaperBeta D c 1=I*((2*lemma44PaperAlpha D*
      (1+c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) := rfl

theorem appendixB_beta_three_source (D : ℕ) (c : ℝ) :
    lemma83PaperBeta D c 2=I*((3*lemma44PaperAlpha D*
      (1-c*lemma44PaperAlpha D*lemma23PaperL D) : ℝ) : ℂ) := rfl

@[simp] theorem appendixB_kernel_zero_index (X : ℝ) (γ : ℂ) : lemma151Kernel X γ 0=0 := by
  simp [lemma151Kernel]

theorem appendixB_kernel_strict_endpoint {X : ℝ} (γ : ℂ) {n : ℕ}
    (hn : X≤(n : ℝ)) : lemma151Kernel X γ n=0 := by
  simp [lemma151Kernel,not_lt_of_ge hn]

theorem appendixB_full_kernel_strict_product_endpoint {X : ℝ} (β γ : ℂ) {l₁ l : ℕ}
    (hl : X≤((l₁*l : ℕ) : ℝ)) : lemma151Kernel X γ (l₁*l)*lemma151Rho β l/l=0 := by
  rw [appendixB_kernel_strict_endpoint γ hl]
  simp

/-- The original infinite notation is a genuinely finite strict-support sum. -/
theorem appendixB_full_kernel_finite_sum {X : ℝ} (β γ : ℂ) {l₁ N : ℕ}
    (hl : 0<l₁) (hN : X≤(N : ℝ)) :
    appendixBFullKernelSum X β γ l₁=
      ∑ l ∈ Finset.range N, lemma151Kernel X γ (l₁*l)*lemma151Rho β l/l := by
  apply tsum_eq_sum
  intro l hlout
  have hnl : N≤l := Nat.le_of_not_gt (by simpa using hlout)
  apply appendixB_full_kernel_strict_product_endpoint
  apply hN.trans
  exact_mod_cast (hnl.trans (Nat.le_mul_of_pos_left l hl))

/-- Equality is in the complement of H14's strict sqrt(P) support. -/
theorem appendixB_H14_endpoint_separate (D n : ℕ)
    (hn : (n : ℝ)=(lemma23PaperP D)^(1/2 : ℝ)) :
    bH14Coefficient D n=0 ∧
      lemma151First D n=lemma151Iota2*lemma151Kernel (lemma151P2 D) (lemma151Beta7 D) n := by
  constructor
  · simp [bH14Coefficient,hn]
  · simp [lemma151First,hn]

theorem appendixB_H14_complement_pointwise (D n : ℕ) :
    lemma151Kernel (lemma151P1 D) (lemma151Beta6 D) n=
      (if (n : ℝ)<(lemma23PaperP D)^(1/2 : ℝ)
        then lemma151Kernel (lemma151P1 D) (lemma151Beta6 D) n else 0)+
      (if (lemma23PaperP D)^(1/2 : ℝ)≤(n : ℝ)
        then lemma151Kernel (lemma151P1 D) (lemma151Beta6 D) n else 0) := by
  by_cases h : (n : ℝ)<(lemma23PaperP D)^(1/2 : ℝ)
  · simp only [if_pos h,if_neg (not_le.mpr h),add_zero]
  · simp only [if_neg h,if_pos (le_of_not_gt h),zero_add]

/-- The literal P^12 tail in (B.3) vanishes beyond the actual P1 support.
This source issue is recorded, not repaired by changing the cutoff. -/
theorem appendixB_literal_B3_tail_zero {P : ℝ} (hP : 1≤P) (γ : ℂ) {n : ℕ}
    (hn : P^(12 : ℝ)<(n : ℝ)) : lemma151Kernel (P^(0.504 : ℝ)) γ n=0 := by
  exact appendixB_kernel_strict_endpoint γ
    ((Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (0.504 : ℝ)≤12)).trans hn.le)

theorem appendixB_printed_e2 (j : ℕ) :
    lemma151FullKernelConstant 0.5 (5/2) j=
      (1-2*(j : ℂ)/5+8*j/(25*Real.pi*I))*exp (((5/4*Real.pi : ℝ) : ℂ)*I)-
        8*j/(25*Real.pi*I) := by
  unfold lemma151FullKernelConstant
  norm_num
  ring

theorem appendixB_printed_e3 (j : ℕ) :
    lemma151FullKernelConstant 0.498 (3/2) j=
      (1-2*(j : ℂ)/3+j/(1.1205*Real.pi*I))*exp (((0.747*Real.pi : ℝ) : ℂ)*I)-
        j/(1.1205*Real.pi*I) := by
  unfold lemma151FullKernelConstant
  norm_num
  ring

theorem appendixB_printed_e1_prime (j : ℕ) :
    lemma151FullKernelConstant 0.504 (3/2) j=
      (1-2*(j : ℂ)/3+j/(1.134*Real.pi*I))*exp (((0.756*Real.pi : ℝ) : ℂ)*I)-
        j/(1.134*Real.pi*I) := by
  unfold lemma151FullKernelConstant
  norm_num
  ring

/-- Final original P2/P3/full-P1 uniformity with a genuinely vanishing explicit
error, all three finite-D j shifts, and one threshold before l1. -/
theorem appendixB_source_full_kernel_asymptotics {c : ℝ} (hc : 0<c) :
    Tendsto (fun D : ℕ => appendixBOriginalError D c) atTop (𝓝 0) ∧
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ j : Fin 3, ∀ l₁ : ℕ, 0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBFullKernelSum (lemma151P2 D) (lemma83PaperBeta D c j) (lemma151Beta7 D) l₁-
          lemma151FullKernelConstant 0.5 (5/2) (j.val+1)‖≤appendixBOriginalError D c ∧
      ‖appendixBFullKernelSum (lemma151P3 D) (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
          lemma151FullKernelConstant 0.498 (3/2) (j.val+1)‖≤appendixBOriginalError D c ∧
      ‖appendixBFullKernelSum (lemma151P1 D) (lemma83PaperBeta D c j) (lemma151Beta6 D) l₁-
          lemma151FullKernelConstant 0.504 (3/2) (j.val+1)‖≤appendixBOriginalError D c := by
  refine ⟨appendixB_original_error_tendsto_zero hc,?_⟩
  obtain ⟨N,hN,hfull⟩ := appendixB_original_printed_constants_uniform hc
  refine ⟨N,hN,?_⟩
  intro D hD j l₁ hl hlT
  exact ⟨hfull D hD j 1 l₁ hl hlT,hfull D hD j 2 l₁ hl hlT,hfull D hD j 0 l₁ hl hlT⟩

end ZhangLS.Spec
