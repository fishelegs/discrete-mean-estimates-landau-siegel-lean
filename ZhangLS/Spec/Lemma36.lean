import ZhangLS.Spec.Lemma36Mean
import ZhangLS.Spec.Lemma36IntegralMean
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

/-- The actual characters violating the strict inequality (3.6). -/
noncomputable def lemma36ActualBadFamily {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) :=
  (lemma33ActualFamily D).filter
    (fun ψ => lemma23PaperL D^(-633 : ℤ) ≤ lemma36ActualB χ ψ.2)

/-- Original Lemma 3.6, with a common absolute constant and modulus threshold. -/
def Lemma36Target : Prop := ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
  ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ((lemma36ActualBadFamily χ).card : ℝ) ≤
      C*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ)

lemma lemma36_mem_bad_family {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : lemma33PrimeIndex D) (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ lemma36ActualBadFamily χ ↔
      Lemma23InPsi (D := D) ψ ∧
        ¬(lemma36ActualB χ ψ < lemma23PaperL D^(-633 : ℤ)) := by
  constructor
  · intro h
    have hh := Finset.mem_filter.mp h
    exact ⟨(lemma33_actual_family_mem p ψ).mp hh.1,not_lt.mpr hh.2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨(lemma33_actual_family_mem p ψ).mpr h.1,not_lt.mp h.2⟩

lemma lemma36_bad_count_times_threshold {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) :
    ((lemma36ActualBadFamily χ).card : ℝ)*(lemma23PaperL D^(-633 : ℤ))^2 ≤
      ∑ ψ ∈ lemma33ActualFamily D, (lemma36ActualB χ ψ.2)^2 := by
  have hl0 : 0 < lemma23PaperL D := by linarith
  calc
    _ = ∑ ψ ∈ lemma36ActualBadFamily χ, (lemma23PaperL D^(-633 : ℤ))^2 := by simp
    _ ≤ ∑ ψ ∈ lemma36ActualBadFamily χ, (lemma36ActualB χ ψ.2)^2 := by
      apply Finset.sum_le_sum
      intro ψ hψ
      have hh := (Finset.mem_filter.mp hψ).2
      exact pow_le_pow_left₀ (zpow_pos hl0 _).le hh 2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)

lemma lemma36_threshold_square (L : ℝ) (hL : 0 < L) :
    (L^(-633 : ℤ))^2 = L^(-1266 : ℤ) := by
  rw [pow_two, ← zpow_add₀ (ne_of_gt hL)]
  norm_num only [Int.reduceAdd]

lemma lemma36_B_mean_scale_identity (L : ℝ) (hL : 0 < L) :
    L^(-2007 : ℤ)*L^2 = L^(-2005 : ℤ) := by
  simpa only [Int.reduceAdd,zpow_ofNat] using
    (zpow_add₀ (ne_of_gt hL) (-2007 : ℤ) 2).symm

lemma lemma36_uniform_actual_B_mean_square :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      3 ≤ lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ →
          (∑ ψ ∈ lemma33ActualFamily D, (lemma36ActualB χ ψ.2)^2) ≤
            C*lemma33ActualPrimeMass D*lemma23PaperL D^(-2005 : ℤ) := by
  obtain ⟨C,hC,D₀,hD₀⟩ := lemma36_uniform_actual_X4_mean
  refine ⟨34*C,mul_pos (by norm_num) hC,D₀,?_⟩
  intro D hD
  have hp := hD₀ D hD
  refine ⟨hp.1,?_⟩
  intro χ hA
  let K : ℝ := C*lemma33ActualPrimeMass D*lemma23PaperL D^(-2007 : ℤ)
  have hM : 0 ≤ lemma33ActualPrimeMass D :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hl0 : 0 < lemma23PaperL D := by linarith [hp.1]
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC.le hM) (zpow_pos hl0 _).le
  calc
    _ ≤ 34*K*lemma23PaperL D^2 :=
      lemma36_actual_B_mean_square_le χ hp.1 K hK (hp.2 χ hA)
    _ = (34*C)*lemma33ActualPrimeMass D*
        (lemma23PaperL D^(-2007 : ℤ)*lemma23PaperL D^2) := by dsimp [K]; ring
    _ = _ := by rw [lemma36_B_mean_scale_identity _ hl0]

/-- The original X₄ exceptional-set estimate, with no mean or coefficient
bound left as an input hypothesis. -/
theorem lemma36_proved : Lemma36Target := by
  obtain ⟨C,hC,D₀,hD₀⟩ := lemma36_uniform_actual_B_mean_square
  refine ⟨C,hC,D₀,?_⟩
  intro D hD χ hA
  have hp := hD₀ D hD
  have hl0 : 0 < lemma23PaperL D := by linarith [hp.1]
  have hc := (lemma36_bad_count_times_threshold χ hp.1).trans (hp.2 χ hA)
  rw [lemma36_threshold_square _ hl0] at hc
  have hd := (le_div_iff₀ (zpow_pos hl0 (-1266 : ℤ))).mpr hc
  have hz : lemma23PaperL D^(-2005 : ℤ) / lemma23PaperL D^(-1266 : ℤ) =
      lemma23PaperL D^(-739 : ℤ) := by
    simpa only [Int.reduceSub] using
      (zpow_sub₀ (ne_of_gt hl0) (-2005 : ℤ) (-1266 : ℤ)).symm
  calc
    _ ≤ (C*lemma33ActualPrimeMass D*lemma23PaperL D^(-2005 : ℤ)) /
        lemma23PaperL D^(-1266 : ℤ) := hd
    _ = _ := by rw [mul_div_assoc,hz]

end ZhangLS.Spec
