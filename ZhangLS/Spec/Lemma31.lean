import ZhangLS.Spec.Lemma31TotalWeight
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
set_option maxHeartbeats 2000000

def Lemma31Target : Prop := ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
  ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    (∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
      ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹) ≤ C*lemma23PaperL D^(-2011 : ℤ)

lemma lemma31_square_tail_scale_identity (L : ℝ) (hL : 0 < L) :
    L^(-2013 : ℤ)*L^2 = L^(-2011 : ℤ) := by
  simpa only [Int.reduceAdd,zpow_ofNat] using (zpow_add₀ (ne_of_gt hL) (-2013 : ℤ) 2).symm

lemma lemma31_actual_square_paper_tail_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ)) :
    (∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
      ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹) ≤ 1260*lemma23PaperL D^(-2011 : ℤ) := by
  let T : ℝ := ∑ n ∈ Finset.Ioc (D^2) (lemma31PaperCutoff D), lemma31NuReal χ n*(n : ℝ)⁻¹
  let U : ℝ := ∑ n ∈ Finset.Icc 1 (lemma31PaperCutoff D), lemma31NuReal χ n*(n : ℝ)⁻¹
  have ht : T ≤ 21*lemma23PaperL D^(-2013 : ℤ) := lemma31_nu_linear_paper_tail_le χ hD hL hA hAbs
  have hu : U ≤ 30*lemma23PaperL D^2 := lemma31_nu_total_paper_weight_le χ hD hL hA hAbs
  have hu0 : 0 ≤ U := Finset.sum_nonneg (fun n _ =>
    mul_nonneg (lemma31_nu_real_nonneg χ n) (inv_nonneg.mpr (Nat.cast_nonneg _)))
  have hl0 : 0 < lemma23PaperL D := by linarith
  have hs := lemma31_actual_square_weighted_tail_le χ (D^2) (lemma31PaperCutoff D)
  have hn : (D^2)*(D^2) = D^4 := by ring
  rw [hn] at hs
  calc
    _ ≤ 2*T*U := hs
    _ ≤ 2*(21*lemma23PaperL D^(-2013 : ℤ))*U := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by norm_num)) hu0
    _ ≤ 2*(21*lemma23PaperL D^(-2013 : ℤ))*(30*lemma23PaperL D^2) :=
      mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (zpow_pos hl0 _).le))
    _ = 1260*(lemma23PaperL D^(-2013 : ℤ)*lemma23PaperL D^2) := by ring
    _ = _ := by rw [lemma31_square_tail_scale_identity _ hl0]

lemma lemma31_actual_real_square_paper_tail_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 1 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹ ≤ lemma23PaperL D^(-2013 : ℤ)) :
    (∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
      (lemma23NuArithmeticFunction χ n).re^2*(n : ℝ)⁻¹) ≤ 1260*lemma23PaperL D^(-2011 : ℤ) := by
  have hh := lemma31_actual_square_paper_tail_le χ hD hL hA hAbs
  have he : (∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
      (lemma23NuArithmeticFunction χ n).re^2*(n : ℝ)⁻¹) =
      ∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
        ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    change (lemma31NuReal χ n)^2*(n : ℝ)⁻¹ = _
    rw [lemma31_nu_real_eq_norm]
  rwa [← he] at hh

theorem lemma31_proved : Lemma31Target := by
  obtain ⟨D₀,hD₀⟩ := lemma31_exponential_absorption_threshold
  refine ⟨1260,by norm_num,D₀,?_⟩
  intro D hD χ hA
  have hp := hD₀ D hD
  exact lemma31_actual_square_paper_tail_le χ hp.1 (by linarith [hp.2.1]) hA hp.2.2

end ZhangLS.Spec
