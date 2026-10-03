import ZhangLS.Spec.AppendixBRoughReplacementB1
import ZhangLS.Spec.Lemma34TauProduct
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.BCoefficientBounds

/-! The actual divisor-weighted ν tail through the paper cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- Finite weighted Cauchy in division notation, valid even for zero weights. -/
theorem appendixB_finite_weighted_cauchy {ι : Type*} (S : Finset ι)
    (a b t : ι → ℝ) (ht : ∀ i ∈ S, 0 ≤ t i) :
    (∑ i ∈ S, a i*b i/t i)^2 ≤
      (∑ i ∈ S, (a i)^2/t i)*(∑ i ∈ S, (b i)^2/t i) := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i hi => div_nonneg (sq_nonneg _) (ht i hi))
    (fun i hi => div_nonneg (sq_nonneg _) (ht i hi))
  intro i hi
  exact le_of_eq (by ring)

/-- The actual τ₂ energy; the zero cutoff also causes no exception. -/
theorem appendixB_tau_two_harmonic_energy (N : ℕ) :
    (∑ n ∈ Icc 1 N, (lemma34Tau 2 n : ℝ)^2/(n : ℝ)) ≤
      (harmonic N : ℝ)^4 := by
  by_cases hN : 1 ≤ N
  · simpa only [div_eq_mul_inv, show 2*2=4 by rfl] using
      lemma34_tau_square_harmonic_sum_le 2 N (by decide) hN
  · have : N=0 := by omega
    subst N
    simp

/-- The energy at floor(P²), without changing the original paper scales. -/
theorem appendixB_tau_two_paper_energy {D : ℕ}
    (hD : 1<D) (hL : 1≤lemma23PaperL D) :
    (∑ n ∈ Icc 1 (lemma31PaperCutoff D), (lemma34Tau 2 n : ℝ)^2/(n : ℝ)) ≤
      81*lemma23PaperL D^36 := by
  have hH := (harmonic_le_one_add_log (lemma31PaperCutoff D)).trans
    (lemma31_paper_cutoff_log_factor_le hD hL)
  have hh : 0≤(harmonic (lemma31PaperCutoff D) : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    positivity
  apply (appendixB_tau_two_harmonic_energy _).trans
  convert pow_le_pow_left₀ hh hH 4 using 1 <;> ring

/-- Genuine Lemma 3.1 square-tail consequence, retaining original (A) and the
strict D⁴ endpoint. The half-power is rounded harmlessly toward a weaker bound. -/
theorem appendixB_actual_divisor_nu_tail {D N : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    (hN : N≤lemma31PaperCutoff D) :
    (∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖*
      (lemma34Tau 2 h : ℝ)/(h : ℝ)) ≤ 320*lemma23PaperL D^(-987 : ℤ) := by
  have hν : (∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖^2/(h : ℝ)) ≤
      1260*lemma23PaperL D^(-2011 : ℤ) := by
    apply le_trans _ (by simpa only [lemma31PaperCutoff,div_eq_mul_inv] using
      lemma31_actual_square_paper_tail_le χ hD hL hA hAbs)
    apply sum_le_sum_of_subset_of_nonneg
    · intro h hh
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hh).1,(mem_Ioc.mp hh).2.trans hN⟩
    · intros; positivity
  have hτ : (∑ h∈Ioc (D^4) N, (lemma34Tau 2 h : ℝ)^2/(h : ℝ)) ≤
      81*lemma23PaperL D^36 := by
    apply le_trans _ (appendixB_tau_two_paper_energy hD hL)
    apply sum_le_sum_of_subset_of_nonneg
    · intro h hh
      have hh' := mem_Ioc.mp hh
      exact mem_Icc.mpr ⟨by omega,hh'.2.trans hN⟩
    · intros; positivity
  have hl : 0<lemma23PaperL D := by linarith
  have hexp : lemma23PaperL D^(-2011 : ℤ)*lemma23PaperL D^36 =
      lemma23PaperL D^(-1975 : ℤ) := by
    simpa only [Int.reduceAdd,zpow_ofNat] using
      (zpow_add₀ hl.ne' (-2011 : ℤ) (36 : ℤ)).symm
  have hsquare : (320*lemma23PaperL D^(-987 : ℤ))^2 =
      102400*lemma23PaperL D^(-1974 : ℤ) := by
    rw [mul_pow, pow_two, pow_two, ←zpow_add₀ hl.ne']
    norm_num
  have hpow : lemma23PaperL D^(-1975 : ℤ)≤lemma23PaperL D^(-1974 : ℤ) :=
    zpow_le_zpow_right₀ hL (by norm_num)
  have hc := appendixB_finite_weighted_cauchy (Ioc (D^4) N)
    (fun h => ‖lemma23NuArithmeticFunction χ h‖) (fun h => (lemma34Tau 2 h : ℝ))
    (fun h => (h : ℝ)) (by intros; positivity)
  have hs : (∑ h∈Ioc (D^4) N, ‖lemma23NuArithmeticFunction χ h‖*
      (lemma34Tau 2 h : ℝ)/(h : ℝ))^2 ≤ (320*lemma23PaperL D^(-987 : ℤ))^2 := by
    calc
      _ ≤ (1260*lemma23PaperL D^(-2011 : ℤ))*(81*lemma23PaperL D^36) :=
        hc.trans (mul_le_mul hν hτ (sum_nonneg (by intros; positivity)) (by positivity))
      _ = 102060*lemma23PaperL D^(-1975 : ℤ) := by
        rw [show (1260*lemma23PaperL D^(-2011 : ℤ))*(81*lemma23PaperL D^36) =
          102060*(lemma23PaperL D^(-2011 : ℤ)*lemma23PaperL D^36) by ring,hexp]
      _ ≤ 102400*lemma23PaperL D^(-1974 : ℤ) := by
        exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans
          (mul_le_mul_of_nonneg_right (by norm_num : (102060:ℝ)≤102400) (by positivity))
      _ = _ := hsquare.symm
  exact (sq_le_sq₀ (sum_nonneg (by intros; positivity)) (by positivity)).mp hs

end ZhangLS.Spec
