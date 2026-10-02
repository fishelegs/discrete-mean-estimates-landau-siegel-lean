import ZhangLS.Spec.Lemma34IntegralMean
set_option autoImplicit false
namespace ZhangLS.Spec
open MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma34ActualB {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ N) : ℝ :=
  ‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
  ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
  (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
    (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
      ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖)/t)

lemma lemma34_actual_B_nonneg {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ N) : 0 ≤ lemma34ActualB χ ψ := by
  have hI : 0 ≤ ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
    (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
      ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖)/t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (le_of_lt (lt_trans zero_lt_one ht.1))
  exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hI

lemma lemma34_B_algebra_bound (L M C : ℝ) (hL1 : 1 ≤ L) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    2*(4*M*(C*L^1600)) + 2*((80*L)^2*(4*M*(C*L^1600))) ≤
      (51208*C)*M*L^1602 := by
  have hpow : L^1600 ≤ L^1602 := by
    calc
      _ = L^1600*1 := (mul_one _).symm
      _ ≤ L^1600*L^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL1) (by positivity)
      _ = _ := by rw [← pow_add]
  have h8 : 0 ≤ 8*M*C :=
    mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) hM) hC
  have hUp : 8*M*C*L^1600 ≤ 8*M*C*L^1602 := mul_le_mul_of_nonneg_left hpow h8
  calc
    _ = 8*M*C*L^1600 + 51200*M*C*L^1602 := by
      rw [show 1602 = 1600+2 by omega,pow_add]
      generalize hU : L^1600 = U
      generalize hV : C = V
      ring
    _ ≤ 8*M*C*L^1602 + 51200*M*C*L^1602 :=
      add_le_add hUp (le_refl (51200*M*C*L^1602))
    _ = _ := by
      change _ = (51208*C)*M*L^1602
      generalize hU : L^1602 = U
      generalize hV : C = V
      ring


lemma lemma34_actual_B_mean_square {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) :
    (∑ ψ ∈ lemma33ActualFamily D, lemma34ActualB χ ψ.2^2) ≤
      (51208*81^1600) * lemma33ActualPrimeMass D * lemma23PaperL D^1602 := by
  let L := lemma23PaperL D
  let M := lemma33ActualPrimeMass D
  let C := (81 : ℝ)^1600
  let E := fun ψ : lemma33CharacterIndex D =>
    ‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) ((D : ℝ)^80)‖
  let I := fun ψ : lemma33CharacterIndex D =>
    ∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
      (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
        ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)/t
  have hR : 1 ≤ (D : ℝ)^80 := one_le_pow₀ (by exact_mod_cast lemma34_D_positive hL)
  have hE : (∑ ψ ∈ lemma33ActualFamily D, E ψ^2) ≤ 4*M*(C*L^1600) :=
    lemma34_actual_sum_norms_square_mean χ hL _ hR le_rfl
  have hI : (∑ ψ ∈ lemma33ActualFamily D, I ψ^2) ≤ (80*L)^2*(4*M*(C*L^1600)) :=
    lemma34_actual_integral_mean_square χ hL
  have hB : (∑ ψ ∈ lemma33ActualFamily D, lemma34ActualB χ ψ.2^2) ≤
      2*(∑ ψ ∈ lemma33ActualFamily D, E ψ^2) + 2*(∑ ψ ∈ lemma33ActualFamily D, I ψ^2) := by
    calc
      _ = ∑ ψ ∈ lemma33ActualFamily D, (E ψ+I ψ)^2 := rfl
      _ ≤ ∑ ψ ∈ lemma33ActualFamily D, (2*E ψ^2+2*I ψ^2) := by
        apply Finset.sum_le_sum
        intro ψ hψ
        nlinarith [sq_nonneg (E ψ-I ψ)]
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => by positivity)
  have hC : 0 ≤ C := pow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) 1600
  exact (hB.trans (add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num))
    (mul_le_mul_of_nonneg_left hI (by norm_num)))).trans
      (lemma34_B_algebra_bound L M C hL1 hM hC)

end ZhangLS.Spec
