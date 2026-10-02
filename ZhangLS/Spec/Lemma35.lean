import ZhangLS.Spec.Lemma35BSecondMoment
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma35ActualBadFamily {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) :=
  (lemma33ActualFamily D).filter (fun ψ => lemma23PaperL D^(-585 : ℤ) ≤ lemma35ActualB χ ψ.2)

def Lemma35Target : Prop := ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
  ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ((lemma35ActualBadFamily χ).card : ℝ) ≤
      C*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ)

lemma lemma35_mem_bad_family {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : lemma33PrimeIndex D) (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ lemma35ActualBadFamily χ ↔
      Lemma23InPsi (D := D) ψ ∧ ¬(lemma35ActualB χ ψ < lemma23PaperL D^(-585 : ℤ)) := by
  constructor
  · intro h
    have hh := Finset.mem_filter.mp h
    exact ⟨(lemma33_actual_family_mem p ψ).mp hh.1,not_lt.mpr hh.2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨(lemma33_actual_family_mem p ψ).mpr h.1,not_lt.mp h.2⟩

lemma lemma35_bad_count_times_threshold {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) :
    ((lemma35ActualBadFamily χ).card : ℝ)*(lemma23PaperL D^(-585 : ℤ))^2 ≤
      ∑ ψ ∈ lemma33ActualFamily D, (lemma35ActualB χ ψ.2)^2 := by
  have hl0 : 0 < lemma23PaperL D := by linarith
  calc
    _ = ∑ ψ ∈ lemma35ActualBadFamily χ, (lemma23PaperL D^(-585 : ℤ))^2 := by simp
    _ ≤ ∑ ψ ∈ lemma35ActualBadFamily χ, (lemma35ActualB χ ψ.2)^2 := by
      apply Finset.sum_le_sum
      intro ψ hψ
      have hh := (Finset.mem_filter.mp hψ).2
      exact pow_le_pow_left₀ (zpow_pos hl0 _).le hh 2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)


lemma lemma35_threshold_square (L : ℝ) (hL : 0 < L) :
    (L^(-585 : ℤ))^2 = L^(-1170 : ℤ) := by
  rw [pow_two, ← zpow_add₀ (ne_of_gt hL)]
  norm_num only [Int.reduceAdd]

lemma lemma35_uniform_actual_bad_count :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ((lemma35ActualBadFamily χ).card : ℝ) ≤
          50400*(32+Real.pi^2)*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := lemma35_uniform_actual_B_mean_square
  refine ⟨D₀,?_⟩
  intro D hD χ hA
  have hp := hD₀ D hD
  have hl0 : 0 < lemma23PaperL D := by linarith [hp.1]
  have hM : 0 ≤ lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hc := (lemma35_bad_count_times_threshold χ hp.1).trans (hp.2 χ hA)
  rw [lemma35_threshold_square _ hl0] at hc
  have hd := (le_div_iff₀ (zpow_pos hl0 (-1170 : ℤ))).mpr hc
  have hz : lemma23PaperL D^(-1916 : ℤ) / lemma23PaperL D^(-1170 : ℤ) =
      lemma23PaperL D^(-746 : ℤ) := by
    simpa only [Int.reduceSub] using (zpow_sub₀ (ne_of_gt hl0) (-1916 : ℤ) (-1170 : ℤ)).symm
  have hw : lemma23PaperL D^(-746 : ℤ) ≤ lemma23PaperL D^(-739 : ℤ) :=
    zpow_le_zpow_right₀ (show 1 ≤ lemma23PaperL D by linarith [hp.1]) (by norm_num)
  calc
    _ ≤ (50400*(32+Real.pi^2)*lemma33ActualPrimeMass D*
        lemma23PaperL D^(-1916 : ℤ)) / lemma23PaperL D^(-1170 : ℤ) := hd
    _ = 50400*(32+Real.pi^2)*lemma33ActualPrimeMass D*lemma23PaperL D^(-746 : ℤ) := by
      rw [mul_div_assoc,hz]
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (mul_nonneg (by positivity) hM)

theorem lemma35_proved : Lemma35Target := by
  obtain ⟨D₀,hD₀⟩ := lemma35_uniform_actual_bad_count
  exact ⟨50400*(32+Real.pi^2),by positivity,D₀,hD₀⟩

end ZhangLS.Spec
