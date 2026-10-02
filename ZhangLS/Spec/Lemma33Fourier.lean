import Mathlib.Analysis.Fourier.AddCircle
import ZhangLS.Spec.Lemma23CharacterOrthogonality
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000

noncomputable def lemma33TrigSum (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * fourier (T := 1) (n : ℤ) (x : AddCircle (1 : ℝ))

lemma lemma33_fourier_interval_orthogonality (m n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      star (fourier (T := 1) m (x : AddCircle (1 : ℝ))) *
        fourier (T := 1) n (x : AddCircle (1 : ℝ))) = if m=n then 1 else 0 := by
  have he := congrFun (fourierCoeff_fourier (T := 1) n) m
  rw [fourierCoeff_eq_intervalIntegral (T := 1) (fourier n) m 0] at he
  simpa only [one_div,inv_one,one_smul,zero_add,smul_eq_mul,
    fourier_neg,Complex.star_def,Pi.single_apply,eq_comm] using he

lemma lemma33_trig_sum_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (lemma33TrigSum S a) := by
  unfold lemma33TrigSum
  apply continuous_finsetSum
  intro n hn
  simp only [fourier_coe_apply]
  fun_prop

lemma lemma33_trig_sum_parseval (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖lemma33TrigSum S a x‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let e := fun n : ℕ => fun x : ℝ => fourier (T := 1) (n : ℤ) (x : AddCircle (1 : ℝ))
  have hc (n : ℕ) : Continuous (e n) := by
    change Continuous (fun x : ℝ => fourier (T := 1) (n : ℤ) (x : AddCircle (1 : ℝ)))
    simp only [fourier_coe_apply]
    fun_prop
  have hi (m n : ℕ) : IntervalIntegrable
      (fun x => star (a m * e m x) * (a n * e n x)) volume 0 1 :=
    (((continuous_const.mul (hc m)).star).mul (continuous_const.mul (hc n))).intervalIntegrable _ _
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_sum]
  calc
    _ = ∫ x in (0 : ℝ)..1, ∑ m ∈ S, ∑ n ∈ S,
        star (a m * e m x) * (a n * e n x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [← Complex.normSq_eq_norm_sq]
      exact lemma23_complex_normSq_finset_sum S (fun n => a n * e n x)
    _ = ∑ m ∈ S, ∑ n ∈ S, ∫ x in (0 : ℝ)..1,
        star (a m * e m x) * (a n * e n x) := by
      have houter := intervalIntegral.integral_finsetSum (s := S)
        (f := fun m x => ∑ n ∈ S, star (a m * e m x) * (a n * e n x))
        (fun m hm => by
          convert IntervalIntegrable.sum S (fun n hn => hi m n) using 1
          ext x
          simp only [Finset.sum_apply])
      rw [houter]
      apply Finset.sum_congr rfl
      intro m hm
      exact intervalIntegral.integral_finsetSum (fun n hn => hi m n)
    _ = _ := by
      have hInt (m n : ℕ) : (∫ x in (0 : ℝ)..1,
          star (a m * e m x) * (a n * e n x)) =
          (star (a m) * a n) * (if m=n then 1 else 0) := by
        calc
          _ = ∫ x in (0 : ℝ)..1, (star (a m) * a n) * (star (e m x) * e n x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            dsimp only
            rw [star_mul]
            ring
          _ = _ := by
            rw [intervalIntegral.integral_const_mul]
            congr 1
            simpa only [e,Int.natCast_inj] using lemma33_fourier_interval_orthogonality (m : ℤ) (n : ℤ)
      simp_rw [hInt]
      simp [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]

lemma lemma33_trig_sum_hasDerivAt (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (lemma33TrigSum S a)
      (lemma33TrigSum S (fun n => a n * (2 * (Real.pi : ℂ) * I * n)) x) x := by
  unfold lemma33TrigSum
  convert HasDerivAt.sum (u := S) (fun n hn => (hasDerivAt_fourier (1 : ℝ) (n : ℤ) x).const_mul (a n)) using 1
  · ext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring

lemma lemma33_trig_sum_periodic (S : Finset ℕ) (a : ℕ → ℂ) :
    Function.Periodic (lemma33TrigSum S a) 1 := by
  intro x
  unfold lemma33TrigSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]

lemma lemma33_trig_derivative_energy (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1,
      ‖lemma33TrigSum S (fun n => a n * (2 * (Real.pi : ℂ) * I * n)) x‖ ^ 2) =
      ∑ n ∈ S, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2 := by
  rw [lemma33_trig_sum_parseval]
  apply Finset.sum_congr rfl
  intro n hn
  simp [norm_mul,abs_of_pos Real.pi_pos]
  ring

lemma lemma33_trig_derivative_energy_bound (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hN : ∀ n ∈ S, n ≤ N) :
    (∫ x in (0 : ℝ)..1,
      ‖lemma33TrigSum S (fun n => a n * (2 * (Real.pi : ℂ) * I * n)) x‖ ^ 2) ≤
      (2 * Real.pi * N) ^ 2 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [lemma33_trig_derivative_energy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hle : (2 * Real.pi * n) ^ 2 ≤ (2 * Real.pi * N) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hN n hn) (by positivity)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hle (sq_nonneg ‖a n‖)

lemma lemma33_trig_square_integral_two_periods (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..2, ‖lemma33TrigSum S a x‖ ^ 2) =
      2 * (∫ x in (0 : ℝ)..1, ‖lemma33TrigSum S a x‖ ^ 2) := by
  have hp : Function.Periodic (fun x => ‖lemma33TrigSum S a x‖ ^ 2) 1 := by
    intro x
    dsimp only
    rw [lemma33_trig_sum_periodic S a x]
  have hc := (lemma33_trig_sum_continuous S a).norm.pow 2
  have hh := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) 0
    (fun t u => hc.intervalIntegrable (μ := volume) t u)
  simpa only [zsmul_eq_mul,Int.cast_ofNat,zero_add,mul_one] using hh

lemma lemma33_trig_square_energy_two_periods (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..2, ‖lemma33TrigSum S a x‖ ^ 2) =
      2 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [lemma33_trig_square_integral_two_periods,lemma33_trig_sum_parseval]

lemma lemma33_trig_derivative_two_period_bound (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hN : ∀ n ∈ S, n ≤ N) :
    (∫ x in (0 : ℝ)..2,
      ‖lemma33TrigSum S (fun n => a n * (2 * (Real.pi : ℂ) * I * n)) x‖ ^ 2) ≤
      2 * (2 * Real.pi * N) ^ 2 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [lemma33_trig_square_integral_two_periods]
  have h := mul_le_mul_of_nonneg_left (lemma33_trig_derivative_energy_bound S a N hN) (by norm_num : 0 ≤ (2 : ℝ))
  simpa only [mul_assoc] using h

end ZhangLS.Spec
