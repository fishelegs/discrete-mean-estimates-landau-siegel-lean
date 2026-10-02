import ZhangLS.Spec.Lemma32CoefficientMajorant
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

lemma lemma32_tau_lseries_summable (k : ℕ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (lemma34Tau (k+1) n : ℂ)) s := by
  have hz : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  induction k with
  | zero => simpa only [lemma34Tau,zero_add,pow_one] using hz
  | succ k ih =>
    have hh := ArithmeticFunction.LSeriesSummable_mul
      (f := (↑((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) : ArithmeticFunction ℂ))
      (g := (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) ih hz
    simpa only [← ArithmeticFunction.natCoe_mul,ArithmeticFunction.natCoe_apply,pow_succ,
      lemma34Tau,Nat.succ_eq_add_one] using hh

noncomputable def lemma32WeightedDirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  LSeries (fun n => (lemma32ActualCoefficient χ n : ℂ)) s

lemma lemma32_actual_weighted_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (lemma32ActualCoefficient χ n : ℂ)) s := by
  have ht := lemma32_tau_lseries_summable 15 s hs
  rw [LSeriesSummable,← summable_norm_iff] at ht ⊢
  apply ht.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  simp only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (lemma32_actual_coefficient_nonneg χ n),Complex.norm_natCast]
  exact lemma32_actual_coefficient_le_tau_sixteen χ n

lemma lemma32_actual_weighted_norm_terms_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n => ‖LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) s n‖) :=
  (lemma32_actual_weighted_lseries_summable χ s hs).norm

end ZhangLS.Spec
