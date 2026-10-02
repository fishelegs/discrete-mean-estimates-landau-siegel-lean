import ZhangLS.Spec.ChiUniformLBound
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace ZhangLS.Spec
open Complex Finset MeasureTheory Set
open scoped Real ArithmeticFunction.Moebius
set_option maxHeartbeats 1000000

lemma chi_pseries_upper {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ)+1)^(-σ)) ≤ 1 + (σ-1)⁻¹ := by
  have hi : IntegrableOn (fun t : ℝ => t^(-σ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hf (N : ℕ) : AntitoneOn (fun t : ℝ => t^(-σ)) (Icc 1 (1+(N:ℝ))) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have hb (N : ℕ) : (∑ n ∈ range N, ((n : ℝ)+2)^(-σ)) ≤ (σ-1)⁻¹ := by
    have hh := (hf N).sum_le_integral
    have hs : (∑ n ∈ range N, ((n : ℝ)+2)^(-σ)) ≤
        ∫ t in (1:ℝ)..1+(N:ℝ), t^(-σ) := by
      simpa only [Nat.cast_add, Nat.cast_one, show ∀ n : ℝ, 1 + (n+1) = n+2 by intro n; ring] using hh
    apply hs.trans
    rw [intervalIntegral.integral_of_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith : (1:ℝ) ≤ 1+(N:ℝ))]
    calc
      _ ≤ ∫ t in Ioi (1:ℝ), t^(-σ) := by
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.rpow_nonneg (by linarith [mem_Ioi.mp ht] : (0:ℝ) ≤ t) _
        · exact Filter.Eventually.of_forall (fun t ht => ht.1)
      _ = (σ-1)⁻¹ := by
        rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0:ℝ)<1)]
        simp only [Real.one_rpow]
        rw [show -σ+1 = -(σ-1) by ring, neg_div_neg_eq]
        simp only [one_div]
  apply Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _)
  intro N
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, Nat.cast_add, Nat.cast_one]
    have he : ∀ n : ℕ, (n:ℝ)+1+1 = (n:ℝ)+2 := by intro n; ring
    simp_rw [he]
    linarith [hb N]

lemma chi_bounded_LSeries_upper {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries a s‖ ≤ 1 + (s.re-1)⁻¹ := by
  have hsum := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => ha n) hs
  have hmaj : Summable (fun n : ℕ => ((n:ℝ)+1)^(-s.re)) := by
    have h := (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    convert (summable_nat_add_iff 1).mpr h using 1 <;> simp
  have hnorm : ‖LSeries a s‖ ≤ ∑' n : ℕ, ‖LSeries.term a s (n+1)‖ := by
    rw [LSeries, hsum.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]
    exact norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).mpr hsum).norm
  apply hnorm.trans
  apply (Summable.tsum_le_tsum ?_ ((summable_nat_add_iff 1).mpr hsum).norm hmaj).trans
    (chi_pseries_upper hs)
  intro n
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_right (ha (n+1)) (show 0 ≤ (((n:ℝ)+1)^s.re)⁻¹ by positivity)

/-- Absolute convergence gives a uniform-in-height upper bound. -/
theorem chi_actual_L_right_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    {s : ℂ} (hs : 1 < s.re) :
    ‖dirichletLFunction χ s‖ ≤ 1 + (s.re-1)⁻¹ := by
  rw [dirichletLFunction_eq_series χ hs]
  exact chi_bounded_LSeries_upper χ.evalNat_norm_le_one hs

/-- The actual reciprocal Euler series gives the useful sharp right anchor. -/
theorem chi_actual_L_inverse_right_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    {s : ℂ} (hs : 1 < s.re) :
    ‖(dirichletLFunction χ s)⁻¹‖ ≤ 1 + (s.re-1)⁻¹ := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  let a : ℕ → ℂ := fun n => χ.chi (n : ZMod D) * (ArithmeticFunction.moebius n : ℂ)
  have hmul : dirichletLFunction χ s * LSeries a s = 1 := by
    rw [dirichletLFunction, DirichletCharacter.LFunction_eq_LSeries χ.chi hs]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ.chi hs
  have he : (dirichletLFunction χ s)⁻¹ = LSeries a s := inv_eq_of_mul_eq_one_right hmul
  rw [he]
  apply chi_bounded_LSeries_upper ?_ hs
  intro n
  dsimp [a]
  rw [norm_mul]
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  exact (mul_le_mul (χ.chi.norm_le_one _) hmu (norm_nonneg _) (by norm_num)).trans_eq (by ring)

/-- The full half-strip version, including arbitrarily large real part. -/
theorem chi_actual_L_uniform_height_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 8 ≤ Real.log (D:ℝ)) {s : ℂ}
    (hσ : 1-4/Real.log (D:ℝ) ≤ s.re) (ht : |s.im| ≤ (D:ℝ)+1) :
    ‖dirichletLFunction χ s‖ ≤ 14*Real.exp 16*Real.log (D:ℝ) := by
  have hLp : 0 < Real.log (D:ℝ) := by linarith
  by_cases hs2 : 2 ≤ s.re
  · have hh := chi_actual_L_right_bound χ (by linarith : 1 < s.re)
    have hi : (s.re-1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have he : 1 ≤ Real.exp 16 := Real.one_le_exp_iff.mpr (by norm_num)
    have hm := mul_le_mul_of_nonneg_right he hLp.le
    nlinarith
  · have hs2' : s.re ≤ 2 := (lt_of_not_ge hs2).le
    have hspos : 0 < s.re := by
      have hi : 4/Real.log (D:ℝ) ≤ 1/2 := (div_le_iff₀ hLp).mpr (by linarith)
      linarith
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hspos] at hn
    have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD.le
    apply chi_actual_L_uniform_log_bound χ hD hL hσ
    linarith

end ZhangLS.Spec
