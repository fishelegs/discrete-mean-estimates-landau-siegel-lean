import ZhangLS.Spec.Lemma35IntegralMean
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma35ActualB {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) : ℝ :=
  ‖lemma23ActualX3 χ ψ (lemma23PaperP D^2)‖ +
    ∫ t : ℝ in Set.Ioc ((D : ℝ)^4) (lemma23PaperP D^2), ‖lemma23ActualX3 χ ψ t‖/t

lemma lemma35_actual_B_nonneg {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) : 0 ≤ lemma35ActualB χ ψ := by
  unfold lemma35ActualB
  apply add_nonneg (norm_nonneg _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hp : 0 < t := lt_of_le_of_lt (pow_nonneg (Nat.cast_nonneg D) 4) ht.1
  exact div_nonneg (norm_nonneg _) hp.le

lemma lemma35_actual_B_mean_square_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (K : ℝ) (hK : 0 ≤ K)
    (hmean : ∀ t : ℝ, t ≤ lemma23PaperP D^2 →
      (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX3 χ ψ.2 t‖^2) ≤ K) :
    (∑ ψ ∈ lemma33ActualFamily D, (lemma35ActualB χ ψ.2)^2) ≤ 10*K*lemma23PaperL D^18 := by
  have he := hmean (lemma23PaperP D^2) le_rfl
  have hi := lemma35_actual_integral_mean_square_le χ hL K hmean
  have hp := lemma35_interval_parameters hL
  have hw : (lemma35WeightLength D)^2 ≤ 4*lemma23PaperL D^18 := by
    calc
      _ ≤ (2*lemma23PaperL D^9)^2 := pow_le_pow_left₀ hp.2.2.1.le hp.2.2.2 2
      _ = _ := by ring
  have hl18 : 1 ≤ lemma23PaperL D^18 := one_le_pow₀ (show 1 ≤ lemma23PaperL D by linarith)
  have hpoint (ψ : lemma33CharacterIndex D) : (lemma35ActualB χ ψ.2)^2 ≤
      2*‖lemma23ActualX3 χ ψ.2 (lemma23PaperP D^2)‖^2 +
        2*(∫ t in Set.Ioc ((D : ℝ)^4) (lemma23PaperP D^2), ‖lemma23ActualX3 χ ψ.2 t‖/t)^2 := by
    unfold lemma35ActualB
    nlinarith [sq_nonneg (‖lemma23ActualX3 χ ψ.2 (lemma23PaperP D^2)‖ -
      (∫ t in Set.Ioc ((D : ℝ)^4) (lemma23PaperP D^2), ‖lemma23ActualX3 χ ψ.2 t‖/t))]
  have hlow : 2*K ≤ 2*K*lemma23PaperL D^18 :=
    le_mul_of_one_le_right (mul_nonneg (by norm_num) hK) hl18
  calc
    _ ≤ ∑ ψ ∈ lemma33ActualFamily D,
        (2*‖lemma23ActualX3 χ ψ.2 (lemma23PaperP D^2)‖^2 +
          2*(∫ t in Set.Ioc ((D : ℝ)^4) (lemma23PaperP D^2), ‖lemma23ActualX3 χ ψ.2 t‖/t)^2) :=
      Finset.sum_le_sum (fun ψ _ => hpoint ψ)
    _ = 2*(∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX3 χ ψ.2 (lemma23PaperP D^2)‖^2) +
        2*(∑ ψ ∈ lemma33ActualFamily D,
          (∫ t in Set.Ioc ((D : ℝ)^4) (lemma23PaperP D^2), ‖lemma23ActualX3 χ ψ.2 t‖/t)^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ 2*K + 2*(K*(lemma35WeightLength D)^2) := add_le_add
      (mul_le_mul_of_nonneg_left he (by norm_num)) (mul_le_mul_of_nonneg_left hi (by norm_num))
    _ ≤ 2*K + 2*(K*(4*lemma23PaperL D^18)) := add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hK) (by norm_num))
    _ ≤ _ := by nlinarith

lemma lemma35_B_mean_scale_identity (L : ℝ) (hL : 0 < L) :
    L^(-1934 : ℤ)*L^18 = L^(-1916 : ℤ) := by
  simpa only [Int.reduceAdd,zpow_ofNat] using (zpow_add₀ (ne_of_gt hL) (-1934 : ℤ) 18).symm

lemma lemma35_uniform_actual_B_mean_square :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 3 ≤ lemma23PaperL D ∧
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        (∑ ψ ∈ lemma33ActualFamily D, (lemma35ActualB χ ψ.2)^2) ≤
          50400*(32+Real.pi^2)*lemma33ActualPrimeMass D*lemma23PaperL D^(-1916 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := lemma35_uniform_actual_X3_mean
  refine ⟨D₀,?_⟩
  intro D hD
  have hp := hD₀ D hD
  refine ⟨hp.2.1,?_⟩
  intro χ hA
  let K : ℝ := 5040*(32+Real.pi^2)*lemma33ActualPrimeMass D*lemma23PaperL D^(-1934 : ℤ)
  have hM : 0 ≤ lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hl0 : 0 < lemma23PaperL D := by linarith [hp.2.1]
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by positivity) hM) (zpow_pos hl0 _).le
  have he := lemma35_actual_B_mean_square_le χ hp.2.1 K hK (hp.2.2 χ hA)
  calc
    _ ≤ 10*K*lemma23PaperL D^18 := he
    _ = 50400*(32+Real.pi^2)*lemma33ActualPrimeMass D*
        (lemma23PaperL D^(-1934 : ℤ)*lemma23PaperL D^18) := by dsimp [K]; ring
    _ = _ := by rw [lemma35_B_mean_scale_identity _ hl0]

end ZhangLS.Spec
