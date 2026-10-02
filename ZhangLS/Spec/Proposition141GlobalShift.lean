import ZhangLS.Spec.Proposition141EighthPrimeIntegral
import ZhangLS.Spec.Proposition141Support
import ZhangLS.Spec.Lemma33FirstMean

/-! # The original (p t₀)^β factor and actual prime mass

The global t₀^β factor is preserved for the entire original complex disk.
Its uniform exp(20) bound follows at the explicit ℒ≥2000 threshold and is
not used to erase prime cancellation. The two existing actual prime-window
representations are identified exactly, with their strict endpoints intact.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- Explicit logarithmic comparison at the same fixed threshold as the
complex shift and Mellin bounds; no additional asymptotic input is needed. -/
theorem proposition141_t0_log_bounds {D : ℕ} (hL : 2000≤lemma23PaperL D) :
    1≤lemma51PaperT0 D ∧ 0≤Real.log (lemma51PaperT0 D) ∧
      Real.log (lemma51PaperT0 D)≤Real.log (lemma23PaperP D) := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have ht : 1≤lemma51PaperT0 D := by
    exact one_le_pow₀ hL1
  refine ⟨ht,Real.log_nonneg ht,?_⟩
  rw [lemma51PaperT0,Real.log_pow,lemma23PaperP,Real.log_exp]
  have hl := Real.log_le_sub_one_of_pos hLp
  have hp : 519≤lemma23PaperL D^8 := by
    have hh : lemma23PaperL D≤lemma23PaperL D^8 :=
      le_self_pow₀ hL1 (by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_left hp hLp.le
  norm_num only [Nat.cast_ofNat]
  calc
    519*Real.log (lemma23PaperL D)≤519*lemma23PaperL D := by linarith
    _ = lemma23PaperL D*519 := by ring
    _ ≤ lemma23PaperL D*lemma23PaperL D^8 := hm
    _ = _ := by ring

/-- The t₀ factor is bounded uniformly over the full complex β disk. -/
theorem proposition141_t0_shift_norm {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {β : ℂ} (hβ : ‖β‖<5*lemma44PaperAlpha D) :
    ‖(lemma51PaperT0 D:ℂ)^β‖≤Real.exp 20 := by
  have ht := proposition141_t0_log_bounds hL
  have htp : 0<lemma51PaperT0 D := by linarith [ht.1]
  have hb := proposition141_complex_shift_parameters hL hβ
  rw [Complex.norm_cpow_eq_rpow_re_of_pos htp,Real.rpow_def_of_pos htp]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (lemma51PaperT0 D)*β.re ≤ Real.log (lemma51PaperT0 D)*|β.re| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) ht.2.1
    _ ≤ Real.log (lemma23PaperP D)*|β.re| :=
      mul_le_mul_of_nonneg_right ht.2.2 (abs_nonneg _)
    _ ≤ 20 := by simpa only [mul_comm] using hb.2.2

/-- Exact positive-real power factorization before any analytic estimate. -/
theorem proposition141_prime_t0_shift_factor {D p : ℕ}
    (hL : 2000≤lemma23PaperL D) (β : ℂ) :
    ((((p:ℝ)*lemma51PaperT0 D):ℝ):ℂ)^β =
      (lemma51PaperT0 D:ℂ)^β*(p:ℂ)^β := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p)
    (le_trans (by norm_num) (proposition141_t0_log_bounds hL).1) β]
  simp only [Complex.ofReal_natCast,mul_comm]

/-- The complete printed shift has a fixed pointwise amplitude bound. -/
theorem proposition141_prime_t0_shift_norm {D p : ℕ}
    (hL : 2000≤lemma23PaperL D) {β : ℂ}
    (hβ : ‖β‖<5*lemma44PaperAlpha D) (hp : p∈lemma56PaperPrimes D) :
    ‖(((((p:ℝ)*lemma51PaperT0 D):ℝ):ℂ)^β)‖≤Real.exp 60 := by
  have hpw := lemma56_paper_prime_weight_parameters hL
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hhi : (p:ℝ)≤2*lemma23PaperP D := by linarith [hpw.2.2.2.1]
  have hb := proposition141_small_shift_power_norm hL hβ hp'.2.1.le hhi
  rw [proposition141_prime_t0_shift_factor hL β,norm_mul]
  calc
    _ ≤ Real.exp 20*Real.exp 40 :=
      mul_le_mul (proposition141_t0_shift_norm hL hβ) hb (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; norm_num

/-- Actual finite prime weights factor, rather than defining a residual by
subtraction or replacing the real part of β by a norm bound. -/
theorem proposition141_prime_t0_shift_sum (D : ℕ)
    (hL : 2000≤lemma23PaperL D) (β : ℂ) (f : ℕ→ℂ) :
    (∑ p∈lemma56PaperPrimes D,
      (((((p:ℝ)*lemma51PaperT0 D):ℝ):ℂ)^β)*f p) =
    (lemma51PaperT0 D:ℂ)^β*(∑ p∈lemma56PaperPrimes D,(p:ℂ)^β*f p) := by
  simp_rw [proposition141_prime_t0_shift_factor hL β,mul_assoc]
  rw [mul_sum]

lemma proposition141_prime_windows_equal (D : ℕ) :
    lemma33PrimeWindow D=lemma56PaperPrimes D := by
  ext p
  rw [lemma33_mem_prime_window,lemma56_mem_paper_primes]
  rfl

lemma proposition141_actual_prime_masses_equal (D : ℕ) :
    lemma33ActualPrimeMass D=lemma56PrimeMass D := by
  unfold lemma33ActualPrimeMass lemma56PrimeMass lemma33PrimeIndex
  rw [←Finset.sum_subtype (lemma33PrimeWindow D) (fun _ => Iff.rfl) (fun p => (p:ℝ)),
    proposition141_prime_windows_equal]

end ZhangLS.Spec
