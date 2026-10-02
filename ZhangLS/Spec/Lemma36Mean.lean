import ZhangLS.Spec.Lemma36CoefficientMajorant
import ZhangLS.Spec.Lemma32OriginalTargetClosure
import ZhangLS.Spec.Lemma34UniformMean
import ZhangLS.Spec.Lemma33
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma36CenteredCoefficient {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc (D^4) ⌊x⌋₊ then
    lemma23ActualVarsigma χ n * Complex.exp (-lemma23PaperCenter D * (Real.log (n : ℝ) : ℂ))
  else 0

lemma lemma36_actual_X4_eq_centered_sum {D q : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ q) (x : ℝ) (hx : x ≤ ((D : ℝ)^8)) :
    lemma23ActualX4 χ ψ x = ∑ n ∈ Finset.Icc 1 (D^8),
      lemma36CenteredCoefficient χ x n * ψ (n : ZMod q) := by
  have hf : ⌊x⌋₊ ≤ D^8 := by
    simpa only [← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_le_floor hx
  have hsub : Finset.Ioc (D^4) ⌊x⌋₊ ⊆ Finset.Icc 1 (D^8) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc]
    omega
  calc
    _ = ∑ n ∈ Finset.Ioc (D^4) ⌊x⌋₊, lemma36CenteredCoefficient χ x n * ψ (n : ZMod q) := by
      unfold lemma23ActualX4
      apply Finset.sum_congr rfl
      intro n hn
      simp only [lemma36CenteredCoefficient,if_pos hn]
      ring
    _ = _ := Finset.sum_subset hsub (by
      intro n hn hnot
      simp [lemma36CenteredCoefficient,hnot])

lemma lemma36_actual_X4_mean_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (hx : x ≤ ((D : ℝ)^8)) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 x‖^2) =
      lemma33ActualMean D (D^8) (lemma36CenteredCoefficient χ x) := by
  unfold lemma33ActualMean
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [lemma36_actual_X4_eq_centered_sum χ ψ.2 x hx]

lemma lemma36_centered_coefficient_energy_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (hx : x ≤ ((D : ℝ)^8)) :
    (∑ n ∈ Finset.Icc 1 (D^8), ‖lemma36CenteredCoefficient χ x n‖^2) ≤
      ∑ n ∈ Finset.Ioc (D^4) (D^8),
        ‖lemma23ActualVarsigma χ n‖^2*(n : ℝ)⁻¹ := by
  have hf : ⌊x⌋₊ ≤ D^8 := by
    simpa only [← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_le_floor hx
  have hsub : Finset.Ioc (D^4) ⌊x⌋₊ ⊆ Finset.Icc 1 (D^8) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc]
    omega
  have he : (∑ n ∈ Finset.Icc 1 (D^8), ‖lemma36CenteredCoefficient χ x n‖^2) =
      ∑ n ∈ Finset.Ioc (D^4) ⌊x⌋₊, ‖lemma36CenteredCoefficient χ x n‖^2 := by
    exact (Finset.sum_subset hsub (by intros n hn hnot; simp [lemma36CenteredCoefficient,hnot])).symm
  rw [he]
  calc
    _ = ∑ n ∈ Finset.Ioc (D^4) ⌊x⌋₊, ‖lemma23ActualVarsigma χ n‖^2*(n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
      simp only [lemma36CenteredCoefficient,if_pos hn,norm_mul,mul_pow]
      rw [lemma34_centered_weight_square (lemma23PaperCenter D) (by rfl) hn0]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hf)
      (by intros; positivity)

lemma lemma36_actual_X4_mean_energy_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 3 ≤ lemma23PaperL D) (x : ℝ) (hx : x ≤ (D : ℝ)^8) :
    (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 x‖^2) ≤
      lemma33ActualPrimeMass D *
        (∑ n ∈ Finset.Ioc (D^4) (D^8),
          ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2/(n : ℝ)) := by
  have hshort : D^8 ≤ ⌊lemma23PaperP D⌋₊ := by
    exact (Nat.pow_le_pow_right χ.modulus_pos (by norm_num : 8 ≤ 80)).trans
      (lemma34_cutoff_nat_le_floor_P hL)
  have hM : 0 ≤ lemma33ActualPrimeMass D :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [lemma36_actual_X4_mean_eq χ x hx]
  apply (lemma34_actual_short_mean_bound D (D^8) hshort _).trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply (lemma36_centered_coefficient_energy_le χ x hx).trans
  apply Finset.sum_le_sum
  intro n hn
  have hcoef := pow_le_pow_left₀ (norm_nonneg _) (lemma36_varsigma_norm_le χ n) 2
  rw [mul_pow] at hcoef
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr (Nat.cast_nonneg n))

/-- Uniform pointwise second moment for the paper's actual X₄, derived from
Lemma 3.2 and the first (short-polynomial) assertion of Lemma 3.3. -/
lemma lemma36_uniform_actual_X4_mean :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      3 ≤ lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ → ∀ t : ℝ, t ≤ (D : ℝ)^8 →
          (∑ ψ ∈ lemma33ActualFamily D, ‖lemma23ActualX4 χ ψ.2 t‖^2) ≤
            C*lemma33ActualPrimeMass D*lemma23PaperL D^(-2007 : ℤ) := by
  obtain ⟨C,hC,D₀,hD₀⟩ := lemma32_proved
  refine ⟨C,hC,max D₀ ⌈Real.exp 3⌉₊,?_⟩
  intro D hD
  have h32 := hD₀ D ((le_max_left _ _).trans hD)
  have hL := lemma33_parameters_at_threshold ((le_max_right _ _).trans hD)
  refine ⟨hL,?_⟩
  intro χ hA t ht
  have hM : 0 ≤ lemma33ActualPrimeMass D :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  calc
    _ ≤ lemma33ActualPrimeMass D *
        (∑ n ∈ Finset.Ioc (D^4) (D^8),
          ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2/(n : ℝ)) :=
      lemma36_actual_X4_mean_energy_le χ hL t ht
    _ ≤ lemma33ActualPrimeMass D*(C*lemma23PaperL D^(-2007 : ℤ)) :=
      mul_le_mul_of_nonneg_left (h32 χ hA) hM
    _ = _ := by ring

end ZhangLS.Spec
