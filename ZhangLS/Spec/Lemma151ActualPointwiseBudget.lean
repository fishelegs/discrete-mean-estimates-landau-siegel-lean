import ZhangLS.Spec.Lemma151ActualKernelFactors
import ZhangLS.Spec.AppendixBDivisorCoefficientB1

/-! Explicit divisor-coefficient replacement and finite product error budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical

noncomputable def actual151NuError (D : ℕ) : ℝ :=
  25920*bCoefficientConstant*lemma23PaperL D^(-951 : ℤ)
noncomputable def actual151FirstConstantBound : ℝ :=
  ∑ j : Fin 3,‖actual151FirstConstant (j.val+1)‖
noncomputable def actual151SecondConstantBound : ℝ :=
  ∑ j : Fin 3,‖actual151SecondConstant (j.val+1)‖
noncomputable def actual151ProductError (D : ℕ) (c : ℝ) : ℝ :=
  actual151FirstError D c*actual151SecondError D c+
    actual151SecondConstantBound*actual151FirstError D c+
    actual151FirstConstantBound*actual151SecondError D c
noncomputable def actual151PointwiseError (D : ℕ) (c : ℝ) : ℝ :=
  actual151NuError D+roughCollisionUniformBudget D+actual151ProductError D c

lemma actual151_first_constant_le (j : Fin 3) :
    ‖actual151FirstConstant (j.val+1)‖≤actual151FirstConstantBound := by
  unfold actual151FirstConstantBound
  exact single_le_sum (fun (i : Fin 3) _ => norm_nonneg (actual151FirstConstant (i.val+1))) (mem_univ j)
lemma actual151_second_constant_le (j : Fin 3) :
    ‖actual151SecondConstant (j.val+1)‖≤actual151SecondConstantBound := by
  unfold actual151SecondConstantBound
  exact single_le_sum (fun (i : Fin 3) _ => norm_nonneg (actual151SecondConstant (i.val+1))) (mem_univ j)

lemma actual151_product_error {x y u v : ℂ} {E F U V : ℝ}
    (hx : ‖x-u‖≤E) (hy : ‖y-v‖≤F) (hu : ‖u‖≤U) (hv : ‖v‖≤V) :
    ‖x*y-u*v‖≤E*F+V*E+U*F := by
  have hE : 0≤E := (norm_nonneg _).trans hx
  have hF : 0≤F := (norm_nonneg _).trans hy
  have hU : 0≤U := (norm_nonneg _).trans hu
  have hV : 0≤V := (norm_nonneg _).trans hv
  have he : x*y-u*v=(x-u)*(y-v)+v*(x-u)+u*(y-v) := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by
    simp only [norm_mul]
    exact add_le_add
      (add_le_add (mul_le_mul hx hy (norm_nonneg _) hE)
        (mul_le_mul hv hx (norm_nonneg _) hV))
      (mul_le_mul hu hy (norm_nonneg _) hU)))

/-- Weighted B.1 is applied to the actual b0 on the full source support. -/
theorem actual151_rhostar_to_rho_uniform (c : ℝ) :
    ∃ D₀ : ℕ,∀ D : ℕ,D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,∀ n₁ : ℕ,
      ‖(∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
          lemma151BChiPsi D (n₁*n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n)-
        (∑ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
          lemma151BChiPsi D (n₁*n)*lemma151Rho (lemma83PaperBeta D c j) n/n)‖≤
        (n₁.divisors.card : ℝ)*actual151NuError D := by
  obtain ⟨N,hN⟩ := appendixB_actual_b_B1_uniform c
  refine ⟨N,?_⟩
  intro D hD χ hA j n₁
  have hP := b_paperP_one_le D
  have hcut : ⌊lemma23PaperP D⌋₊≤lemma31PaperCutoff D := by
    apply Nat.floor_le_floor
    nlinarith only [hP]
  have hS : ∀ n∈roughCollisionDomain D ⌊lemma23PaperP D⌋₊,
      0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D) := by
    intro n hn
    have hh := mem_filter.mp hn
    have hI := mem_Icc.mp hh.1
    exact ⟨hI.1,hI.2.trans hcut,hh.2⟩
  have hh := (hN D hD χ hA j _ hS n₁ false).1
  simp only [Bool.false_eq_true,if_false,mul_one,lemma34_tau2_eq_divisor_card] at hh
  exact hh.trans_eq (by unfold actual151NuError; ring)

/-- Every divisor coordinate lies in the original uniform range, with no
coprimality imposed between the rough rectangle coordinates. -/
theorem actual151_divisor_products_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ,2≤D₀ ∧ ∀ D : ℕ,D₀≤D → ∀ j : Fin 3,∀ n₁ : ℕ,
      (n₁ : ℝ)<lemma56PaperT D →
      ‖(∑ dd∈n₁.divisorsAntidiagonal,
          actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151First D) dd.1*
          actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151Second D) dd.2)-
        (n₁.divisors.card : ℂ)*actual151MainConstant (j.val+1)‖≤
        (n₁.divisors.card : ℝ)*actual151ProductError D c := by
  obtain ⟨N,hN,hfac⟩ := actual151_rough_factors_uniform hc
  refine ⟨N,hN,?_⟩
  intro D hD j n₁ hnT
  have hcard : n₁.divisorsAntidiagonal.card=n₁.divisors.card := by
    rw [←Nat.map_div_right_divisors]
    simp
  have he : (n₁.divisors.card : ℂ)*actual151MainConstant (j.val+1)=
      ∑ _dd∈n₁.divisorsAntidiagonal,actual151MainConstant (j.val+1) := by
    simp [hcard]
  rw [he,←sum_sub_distrib]
  calc
    _ ≤ ∑ dd∈n₁.divisorsAntidiagonal,
      ‖actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151First D) dd.1*
        actual151RoughFactor D (lemma83PaperBeta D c j) (lemma151Second D) dd.2-
        actual151MainConstant (j.val+1)‖ := norm_sum_le _ _
    _ ≤ ∑ _dd∈n₁.divisorsAntidiagonal,actual151ProductError D c := by
      apply sum_le_sum
      intro dd hdd
      obtain ⟨h1,h2,h1n,h2n⟩ := actual151_divisor_coordinates hdd
      have h1T : (dd.1 : ℝ)<lemma56PaperT D := (show (dd.1 : ℝ)≤(n₁ : ℝ) by exact_mod_cast h1n).trans_lt hnT
      have h2T : (dd.2 : ℝ)<lemma56PaperT D := (show (dd.2 : ℝ)≤(n₁ : ℝ) by exact_mod_cast h2n).trans_lt hnT
      exact actual151_product_error (hfac D hD j dd.1 h1 h1T).1
        (hfac D hD j dd.2 h2 h2T).2 (actual151_first_constant_le j)
          (actual151_second_constant_le j)
    _ = _ := by simp [hcard]

end ZhangLS.Spec
