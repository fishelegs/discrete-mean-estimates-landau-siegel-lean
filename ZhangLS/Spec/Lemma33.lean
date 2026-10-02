import ZhangLS.Spec.Lemma33FirstMean
import ZhangLS.Spec.Lemma33GaussTransform
import ZhangLS.Spec.Lemma33AdditiveLargeSieve
import ZhangLS.Spec.Lemma33ActualSamples
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

lemma lemma33_actual_mean_eq_prime_sum (D M : ℕ) (a : ℕ → ℂ) :
    lemma33ActualMean D M a = ∑ p : lemma33PrimeIndex D,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p.val => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Icc 1 M, a n * χ (n : ZMod p.val)‖ ^ 2 := by
  classical
  unfold lemma33ActualMean lemma33ActualFamily
  rw [Finset.sum_filter]
  change (∑ χ : Σ p : lemma33PrimeIndex D, DirichletCharacter ℂ p.val,
    if Lemma23InPsi (D := D) χ.2 then
      ‖∑ n ∈ Finset.Icc 1 M, a n * χ.2 (n : ZMod χ.1.val)‖ ^ 2 else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  have hΨ (χ : DirichletCharacter ℂ p.val) : Lemma23InPsi (D := D) χ ↔ χ.IsPrimitive := by
    constructor
    · exact fun h => h.2.1
    · intro h
      have hw := lemma33_mem_prime_window.mp p.property
      exact ⟨hw.1,h,hw.2⟩
  simp_rw [hΨ]
  rw [Finset.sum_filter]

lemma lemma33_actual_mean_le_samples (D M : ℕ) (a : ℕ → ℂ) :
    lemma33ActualMean D M a ≤ ∑ i : lemma33AdditiveIndex D,
      ‖lemma33TrigSum (Finset.Icc 1 M) a (lemma33SamplePoint i)‖ ^ 2 := by
  classical
  rw [lemma33_actual_mean_eq_prime_sum]
  calc
    _ ≤ ∑ p : lemma33PrimeIndex D, ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod p.val)),
        ‖lemma33AdditivePolynomial (Finset.Icc 1 M) a u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact lemma33_prime_primitive_mean_le_additive (lemma33_mem_prime_window.mp p.property).1 _ _
    _ = _ := by
      change _ = ∑ i : Σ p : lemma33PrimeIndex D, {u : ZMod p.val // u ≠ 0},
        ‖lemma33TrigSum (Finset.Icc 1 M) a (lemma33SamplePoint i)‖ ^ 2
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_subtype (p := fun u : ZMod p.val => u ≠ 0) (Finset.univ.erase 0) (fun u => by simp)
        (fun u : ZMod p.val => ‖lemma33AdditivePolynomial (Finset.Icc 1 M) a u‖ ^ 2)]
      apply Finset.sum_congr rfl
      intro u hu
      rw [lemma33_additive_polynomial_eq_trig]
      rfl

lemma lemma33_actual_second_mean_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    (a : ℕ → ℂ) :
    lemma33ActualMean D ⌊lemma23PaperP D ^ 2⌋₊ a ≤
      (32 + Real.pi ^ 2) * lemma23PaperP D ^ 2 *
        ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊, ‖a n‖ ^ 2 := by
  have hP : 1 ≤ lemma23PaperP D := by
    have h := Real.exp_le_exp.mpr (pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 9)
    simpa only [Real.exp_zero,lemma23PaperP] using h
  apply (lemma33_actual_mean_le_samples D _ a).trans
  exact lemma33_additive_large_sieve Finset.univ lemma33SamplePoint
    (Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊) a hP ⌊lemma23PaperP D ^ 2⌋₊
    (Nat.floor_le (sq_nonneg _)) (fun n hn => (Finset.mem_Icc.mp hn).2)
    (fun i hi => lemma33_sample_point_bounds i)
    (fun i hi j hj hne => lemma33_actual_samples_separated hL i j hne)

lemma lemma33_actual_second_Dirichlet_mean_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    (c : ℕ → ℂ) (s : ℂ) :
    lemma33ActualMean D ⌊lemma23PaperP D ^ 2⌋₊ (LSeries.term c s) ≤
      (32 + Real.pi ^ 2) * lemma23PaperP D ^ 2 *
        ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊, ‖c n‖ ^ 2 / (n : ℝ) ^ (2 * s.re) := by
  apply (lemma33_actual_second_mean_bound hL (LSeries.term c s)).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact lemma33_LSeries_term_norm_square c s (Finset.mem_Icc.mp hn).1

lemma lemma33_parameters_at_threshold {D : ℕ} (hD : ⌈Real.exp 3⌉₊ ≤ D) :
    3 ≤ lemma23PaperL D := by
  have hc : Real.exp 3 ≤ (⌈Real.exp 3⌉₊ : ℝ) := Nat.le_ceil _
  have hd : (⌈Real.exp 3⌉₊ : ℝ) ≤ D := by exact_mod_cast hD
  have h := Real.log_le_log (Real.exp_pos 3) (hc.trans hd)
  rw [Real.log_exp] at h
  exact h

theorem lemma33_proved : Lemma33Target := by
  classical
  refine ⟨32 + Real.pi ^ 2,by positivity,⌈Real.exp 3⌉₊,?_⟩
  intro D hD c s
  have hL := lemma33_parameters_at_threshold hD
  refine ⟨?_,lemma33_actual_second_Dirichlet_mean_bound hL c s⟩
  apply (lemma33_actual_first_Dirichlet_mean_bound D c s).trans
  have hm : 0 ≤ lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have he : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊,
      ‖c n‖ ^ 2 / (n : ℝ) ^ (2 * s.re) := by
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC : 1 ≤ 32 + Real.pi ^ 2 := by nlinarith [sq_nonneg Real.pi]
  have hh := mul_le_mul_of_nonneg_right hC (mul_nonneg hm he)
  simpa only [one_mul,mul_assoc] using hh

lemma lemma33_original_Dirichlet_sum_eq_actual {p : ℕ}
    (χ : DirichletCharacter ℂ p) (M : ℕ) (c : ℕ → ℂ) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 M, c n * χ (n : ZMod p) / (n : ℂ) ^ s) =
      ∑ n ∈ Finset.Icc 1 M, LSeries.term c s n * χ (n : ZMod p) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [LSeries.term_of_ne_zero (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)]
  ring


end ZhangLS.Spec
