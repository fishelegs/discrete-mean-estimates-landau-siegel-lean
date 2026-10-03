import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Lemma32SeriesConvergence
import ZhangLS.Spec.Lemma81FourthMomentArithmetic

/-! Actual reciprocal-totient outer weights needed after ξ=1*b. The r/φ(r)
from the inner sum leaves the convergent outer factor 1/φ(r)^2, not 1/r.
All estimates here are absolute arithmetic facts independent of (A). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition26_tau_four_quadratic_summable :
    Summable (fun n : ℕ => (lemma34Tau 4 n:ℝ)/(n:ℝ)^2) := by
  have hs := (lemma32_tau_lseries_summable 3 (2:ℂ) (by norm_num)).norm
  apply hs.congr
  intro n
  by_cases hn : n=0
  · subst n; simp
  · simp [hn]

lemma proposition26_reciprocal_totient_square (n : ℕ) :
    ((Nat.totient n:ℝ)⁻¹)^2 ≤ (lemma34Tau 4 n:ℝ)/(n:ℝ)^2 := by
  by_cases hn : n=0
  · subst n; simp
  have hh := pow_le_pow_left₀ (by positivity : 0≤(Nat.totient n:ℝ)⁻¹)
    (proposition71_reciprocal_totient_le_tau (Nat.pos_of_ne_zero hn)) 2
  rw [div_pow] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    (by exact_mod_cast lemma81_tau_two_square_le_tau_four n) (sq_nonneg _))

lemma proposition26_reciprocal_totient_square_summable :
    Summable (fun n : ℕ => ((Nat.totient n:ℝ)⁻¹)^2) :=
  proposition26_tau_four_quadratic_summable.of_nonneg_of_le
    (fun _ => sq_nonneg _) proposition26_reciprocal_totient_square

noncomputable def proposition26TotientSquareMass : ℝ :=
  ∑' n : ℕ, ((Nat.totient n:ℝ)⁻¹)^2

lemma proposition26_totient_square_mass_pos : 0<proposition26TotientSquareMass := by
  have hh := proposition26_reciprocal_totient_square_summable.le_tsum 1
    (fun n hn => sq_nonneg ((Nat.totient n:ℝ)⁻¹))
  have h1 : 1≤proposition26TotientSquareMass := by simpa [proposition26TotientSquareMass] using hh
  linarith

/-- The source's d,r weight after retaining the r/φ(r) inner factor. The
constant is a concrete convergent series; no prime or totient asymptotic is
assumed. Arbitrary original strict index sets may be substituted for S. -/
theorem proposition26_outer_totient_sum (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hS : S⊆Icc 1 N) :
    (∑ d∈S, ∑ r∈S, (d:ℝ)⁻¹*((Nat.totient r:ℝ)⁻¹)^2) ≤
      (1+Real.log (N:ℝ))*proposition26TotientSquareMass := by
  rw [← Finset.sum_mul_sum]
  have hd : (∑ d∈S,(d:ℝ)⁻¹)≤1+Real.log (N:ℝ) := by
    have hh : (∑ d∈S,(d:ℝ)⁻¹)≤(harmonic N:ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      exact sum_le_sum_of_subset_of_nonneg hS (fun n hn hnot => by positivity)
    exact hh.trans (harmonic_le_one_add_log N)
  have hr : (∑ r∈S,((Nat.totient r:ℝ)⁻¹)^2)≤proposition26TotientSquareMass :=
    proposition26_reciprocal_totient_square_summable.sum_le_tsum S
      (fun n hn => sq_nonneg _)
  apply mul_le_mul hd hr (sum_nonneg (fun n hn => sq_nonneg _))
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  linarith

end ZhangLS.Spec
