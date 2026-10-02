import ZhangLS.Spec.Lemma31
import ZhangLS.Spec.Lemma33
import ZhangLS.Spec.Lemma34ShortMean
import ZhangLS.Spec.Lemma56ActualPrimeMassLower
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma35CenteredCoefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc (D^4) ⌊x⌋₊ then
    lemma23NuArithmeticFunction χ n * Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))
  else 0

lemma lemma35_actual_X3_eq_centered_sum {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) (x : ℝ) (hx : x ≤ lemma23PaperP D^2) :
    lemma23ActualX3 χ ψ x = ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊,
      lemma35CenteredCoefficient χ x n * ψ (n : ZMod q) := by
  have hf : ⌊x⌋₊ ≤ ⌊lemma23PaperP D^2⌋₊ := Nat.floor_le_floor hx
  have hsub : Finset.Ioc (D^4) ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊ := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc]
    omega
  calc
    _ = ∑ n ∈ Finset.Ioc (D^4) ⌊x⌋₊, lemma35CenteredCoefficient χ x n * ψ (n : ZMod q) := by
      unfold lemma23ActualX3
      apply Finset.sum_congr rfl
      intro n hn
      simp only [lemma35CenteredCoefficient,if_pos hn]
      ring
    _ = _ := Finset.sum_subset hsub (by
      intro n hn hnot
      simp [lemma35CenteredCoefficient,hnot])

lemma lemma35_actual_X3_mean_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (hx : x ≤ lemma23PaperP D^2) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX3 χ ψ.2 x‖^2) =
      lemma33ActualMean D ⌊lemma23PaperP D^2⌋₊ (lemma35CenteredCoefficient χ x) := by
  unfold lemma33ActualMean
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [lemma35_actual_X3_eq_centered_sum χ ψ.2 x hx]

lemma lemma35_centered_coefficient_energy_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (hx : x ≤ lemma23PaperP D^2) :
    (∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖lemma35CenteredCoefficient χ x n‖^2) ≤
      ∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
        ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹ := by
  have hf : ⌊x⌋₊ ≤ ⌊lemma23PaperP D^2⌋₊ := Nat.floor_le_floor hx
  have hsub : Finset.Ioc (D^4) ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊ := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc]
    omega
  have he : (∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D^2⌋₊, ‖lemma35CenteredCoefficient χ x n‖^2) =
      ∑ n ∈ Finset.Ioc (D^4) ⌊x⌋₊, ‖lemma35CenteredCoefficient χ x n‖^2 := by
    exact (Finset.sum_subset hsub (by intros n hn hnot; simp [lemma35CenteredCoefficient,hnot])).symm
  rw [he]
  calc
    _ = ∑ n ∈ Finset.Ioc (D^4) ⌊x⌋₊, ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
      simp only [lemma35CenteredCoefficient,if_pos hn,norm_mul,mul_pow]
      rw [lemma34_centered_weight_square (lemma23PaperCenter D) (by rfl) hn0]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hf)
      (by intros; positivity)

lemma lemma35_actual_X3_mean_energy_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : x ≤ lemma23PaperP D^2) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX3 χ ψ.2 x‖^2) ≤
      (32+Real.pi^2)*lemma23PaperP D^2*
        (∑ n ∈ Finset.Ioc (D^4) ⌊lemma23PaperP D^2⌋₊,
          ‖lemma23NuArithmeticFunction χ n‖^2*(n : ℝ)⁻¹) := by
  rw [lemma35_actual_X3_mean_eq χ x hx]
  apply (lemma33_actual_second_mean_bound hL (lemma35CenteredCoefficient χ x)).trans
  exact mul_le_mul_of_nonneg_left (lemma35_centered_coefficient_energy_le χ x hx)
    (mul_nonneg (by positivity) (sq_nonneg _))

end ZhangLS.Spec
