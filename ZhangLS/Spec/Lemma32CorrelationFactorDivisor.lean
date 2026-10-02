import ZhangLS.Spec.Lemma32CoprimeCorrelationFactor
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

lemma lemma32_correlation_factor_nonneg (m δ : ℕ) :
    0 ≤ lemma32SquarefreeCorrelationFactor m δ := by
  unfold lemma32SquarefreeCorrelationFactor
  positivity

lemma lemma32_correlation_factor_mono_of_dvd {m D δ : ℕ}
    (hD : 0 < D) (h : m ∣ D) :
    lemma32SquarefreeCorrelationFactor m δ ≤ lemma32SquarefreeCorrelationFactor D δ := by
  have hc : m.primeFactors.card ≤ D.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono h hD.ne')
  have hm : m ≤ D := Nat.le_of_dvd hD h
  have hdvd : m.gcd δ ∣ D.gcd δ :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left m δ).trans h) (Nat.gcd_dvd_right m δ)
  have hg : m.gcd δ ≤ D.gcd δ :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left δ hD) hdvd
  unfold lemma32SquarefreeCorrelationFactor
  apply mul_le_mul
  · apply mul_le_mul
    · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hc
    · exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
    · exact Real.sqrt_nonneg _
    · positivity
  · exact Real.sqrt_le_sqrt (by exact_mod_cast hg)
  · exact Real.sqrt_nonneg _
  · positivity

end ZhangLS.Spec
