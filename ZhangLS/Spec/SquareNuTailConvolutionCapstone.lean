import ZhangLS.Spec.SquareNuTailConvolutionActual
import ZhangLS.Spec.SquareNuTailMajorant

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset

lemma squareNu_strict_nat_filter (D N : ℕ) :
    (Icc 1 N).filter (fun n : ℕ => (D:ℝ)^20 < n) = Ioc (D^20) N := by
  ext n
  have he : (D:ℝ)^20 < n ↔ D^20<n := by exact_mod_cast Iff.rfl
  simp only [mem_filter,mem_Icc,mem_Ioc,he]
  omega

/-- All coefficients and all cross terms of the positive convolution remain present. -/
lemma squareNu_weighted_tail_le_convolution {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q N : ℕ) :
    (∑ n ∈ Ioc (D^20) N, (lemma31NuReal χ n)^2*(lemma34Tau q n:ℝ)*(n:ℝ)⁻¹) ≤
      squareNuHarmonicTail (squareNu χ^(2*q)*squareTau (q*q-2*q)) ((D:ℝ)^20) N := by
  unfold squareNuHarmonicTail
  rw [squareNu_strict_nat_filter]
  exact sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right
    (squareNu_majorant_all χ q n) (by positivity))

/-- Actual ν²τ_q, the original normalized assumption (A), full conductor D,
strict D^20 lower endpoint, and every finite N≤P^4. -/
theorem squareNu_weighted_tail_uniform :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ q : ℕ, 1 ≤ q → q ≤ 9 → ∀ N : ℕ,
      (N:ℝ) ≤ lemma23PaperP D^4 →
      (∑ n ∈ Ioc (D^20) N, (lemma31NuReal χ n)^2*(lemma34Tau q n:ℝ)*(n:ℝ)⁻¹) ≤
        squareNuTailConstant q * lemma23PaperL D^((4*q:ℕ)-2015:ℤ) := by
  obtain ⟨D₀,hD₀,hbound⟩ := squareNu_actual_convolution_uniform
  exact ⟨D₀,hD₀,fun D hD χ hA q hq hq9 N hNP =>
    (squareNu_weighted_tail_le_convolution χ q N).trans
      (hbound D hD χ hA q hq hq9 N hNP)⟩

/-- The upper endpoint may be any real Z≤P^4; natural floor preserves it exactly. -/
theorem squareNu_weighted_real_tail_uniform :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ q : ℕ, 1 ≤ q → q ≤ 9 → ∀ Z : ℝ,
      Z ≤ lemma23PaperP D^4 →
      (∑ n ∈ Ioc (D^20) ⌊Z⌋₊, (lemma31NuReal χ n)^2*(lemma34Tau q n:ℝ)*(n:ℝ)⁻¹) ≤
        squareNuTailConstant q * lemma23PaperL D^((4*q:ℕ)-2015:ℤ) := by
  obtain ⟨D₀,hD₀,hbound⟩ := squareNu_weighted_tail_uniform
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA q hq hq9 Z hZ
  apply hbound D hD χ hA q hq hq9 ⌊Z⌋₊
  by_cases hz : 0 ≤ Z
  · exact (Nat.floor_le hz).trans hZ
  · rw [Nat.floor_eq_zero.mpr (by linarith : Z < 1)]
    simp only [Nat.cast_zero]
    exact pow_nonneg (le_of_lt (Real.exp_pos _)) _

/-- Exact endpoint interpretation, including integral endpoints. -/
lemma squareNu_real_endpoint_mem (D n : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    n ∈ Ioc (D^20) ⌊Z⌋₊ ↔ (D:ℝ)^20 < n ∧ (n:ℝ) ≤ Z := by
  rw [mem_Ioc,Nat.le_floor_iff hZ]
  have he : D^20<n ↔ (D:ℝ)^20<n := by exact_mod_cast Iff.rfl
  exact and_congr_left (fun _ => he)

lemma squareNuTailConstant_pos (q : ℕ) : 0 < squareNuTailConstant q := by
  have hm : 1 ≤ squareTauMomentConstant (q*q-2*q) := by
    have hh := squareTau_harmonic_le_moment (q*q-2*q) 1
    simpa only [Icc_self,sum_singleton,Nat.cast_one,div_one,
      (squareTau_multiplicative (q*q-2*q)).map_one] using hh
  unfold squareNuTailConstant
  exact mul_pos (by positivity) (by linarith)

/-- Explicit pre-absorption bound for the actual weighted coefficients. -/
theorem squareNu_weighted_tail_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (q N : ℕ) (hq : 1 ≤ q) (hq9 : q ≤ 9) (hNP : (N:ℝ) ≤ lemma23PaperP D^4) :
    (∑ n ∈ Ioc (D^20) N, (lemma31NuReal χ n)^2*(lemma34Tau q n:ℝ)*(n:ℝ)⁻¹) ≤
      (2*q:ℕ)*(5*lemma23PaperL D^(-2013:ℤ)+36*(D:ℝ)^(-1/40:ℝ))*
        (32*lemma23PaperL D^2)^(2*q-1)*squareTauMomentConstant (q*q-2*q) +
      (32*lemma23PaperL D^2)^(2*q)*
        ((D:ℝ)^(-1/4:ℝ)*squareTauMomentConstant (q*q-2*q)) :=
  (squareNu_weighted_tail_le_convolution χ q N).trans
    (squareNu_actual_convolution_explicit χ hD hL hA q N hq hq9 hNP)

end ZhangLS.Spec
