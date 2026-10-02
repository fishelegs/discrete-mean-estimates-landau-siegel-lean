import ZhangLS.Spec.Lemma31HyperbolaError
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
set_option maxHeartbeats 2000000

lemma lemma31_sqrt_cutoff_properties (D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N) :
    let Y := ⌈Real.sqrt ((D : ℝ)*(N : ℝ))⌉₊
    1 ≤ Y ∧ Y ≤ N ∧ (Y : ℝ) ≤ 2*Real.sqrt ((D : ℝ)*(N : ℝ)) ∧
      4*(D : ℝ)*(N : ℝ)/(Y : ℝ) ≤ 4*Real.sqrt ((D : ℝ)*(N : ℝ)) := by
  let R : ℝ := Real.sqrt ((D : ℝ)*(N : ℝ))
  let Y : ℕ := ⌈R⌉₊
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (hD.trans hDN)
  have hdn : (D : ℝ) ≤ N := by exact_mod_cast hDN
  have hp : 0 ≤ (D : ℝ)*(N : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hR : 1 ≤ R := by
    apply Real.one_le_sqrt.mpr
    nlinarith [mul_le_mul hd hn (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg D)]
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R^2 = (D : ℝ)*(N : ℝ) := Real.sq_sqrt hp
  have hY : 1 ≤ Y := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact Nat.ne_of_gt (Nat.ceil_pos.mpr (by linarith : 0 < R))
  have hYN : Y ≤ N := by
    apply Nat.ceil_le.mpr
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg _,?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hdn (Nat.cast_nonneg N)]
  have hYR : (Y : ℝ) ≤ 2*R := by
    have hh := Nat.ceil_lt_add_one hR0
    nlinarith
  have hRY : R ≤ (Y : ℝ) := Nat.le_ceil R
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hdiv : 4*(D : ℝ)*(N : ℝ)/(Y : ℝ) ≤ 4*R := by
    apply (div_le_iff₀ hY0).mpr
    have hm := mul_le_mul_of_nonneg_left hRY hR0
    nlinarith [hRsq]
  exact ⟨hY,hYN,hYR,hdiv⟩

lemma lemma31_actual_cumulative_sqrt_error_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (N : ℕ) (hDN : D ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, lemma23NuArithmeticFunction χ n) -
      (N : ℂ)*dirichletLFunction χ 1‖ ≤ 6*Real.sqrt (D : ℝ)*Real.sqrt (N : ℝ) := by
  let Y : ℕ := ⌈Real.sqrt ((D : ℝ)*(N : ℝ))⌉₊
  have hp := lemma31_sqrt_cutoff_properties D N hD.le hDN
  have he := lemma31_actual_cumulative_error_le χ hD N Y hp.1 hp.2.1
  have hb := add_le_add hp.2.2.1 hp.2.2.2
  have hf : (Y : ℝ)+4*(D : ℝ)*(N : ℝ)/(Y : ℝ) ≤
      6*Real.sqrt ((D : ℝ)*(N : ℝ)) := by nlinarith [hb]
  have hh := he.trans hf
  simpa only [Real.sqrt_mul (Nat.cast_nonneg D),mul_assoc] using hh

lemma lemma31_nu_real_cumulative_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (N : ℕ) (hDN : D ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, lemma31NuReal χ n) ≤
      (N : ℝ)*realLAtOne χ + 6*Real.sqrt (D : ℝ)*Real.sqrt (N : ℝ) := by
  have he := lemma31_actual_cumulative_sqrt_error_le χ hD N hDN
  have hr := Complex.re_le_norm
    ((∑ n ∈ Finset.Icc 1 N, lemma23NuArithmeticFunction χ n) -
      (N : ℂ)*dirichletLFunction χ 1)
  have hh := hr.trans he
  simp only [Complex.sub_re,Complex.re_sum,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero] at hh
  change (∑ n ∈ Finset.Icc 1 N, lemma31NuReal χ n) - (N : ℝ)*realLAtOne χ ≤ _ at hh
  linarith

end ZhangLS.Spec
