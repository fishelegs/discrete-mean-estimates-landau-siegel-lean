import ZhangLS.Spec.Lemma32SeriesConvergence
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! # Exact values of the genuine divisor Dirichlet series

These follow from actual convolution of arithmetic functions and absolute
convergence, not from a formal Euler-product substitution. In particular the
τ₅/n² envelope has the explicit mass (π²/6)^5≤243.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex
open scoped ArithmeticFunction.zeta

/-- Exact convergent L-series of every positive-order divisor function. -/
theorem tauDirichlet_lseries_value (k : ℕ) (s : ℂ) (hs : 1<s.re) :
    LSeries (fun n:ℕ => (lemma34Tau (k+1) n:ℂ)) s=riemannZeta s^(k+1) := by
  have hz : LSeriesSummable (fun n:ℕ => (ArithmeticFunction.zeta n:ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hv : LSeries (fun n:ℕ => (ArithmeticFunction.zeta n:ℂ)) s=riemannZeta s :=
    ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  induction k with
  | zero => simpa only [lemma34Tau,zero_add,pow_one] using hv
  | succ k ih =>
    have hh := ArithmeticFunction.LSeries_mul'
      (f := (↑((ArithmeticFunction.zeta:ArithmeticFunction ℕ)^(k+1)):ArithmeticFunction ℂ))
      (g := (↑(ArithmeticFunction.zeta:ArithmeticFunction ℕ):ArithmeticFunction ℂ))
      (lemma32_tau_lseries_summable k s hs) hz
    simp only [←ArithmeticFunction.natCoe_mul,ArithmeticFunction.natCoe_apply,←pow_succ] at hh
    change LSeries (fun n:ℕ => (lemma34Tau ((k+1)+1) n:ℂ)) s=
      LSeries (fun n:ℕ => (lemma34Tau (k+1) n:ℂ)) s*
        LSeries (fun n:ℕ => (ArithmeticFunction.zeta n:ℂ)) s at hh
    rw [ih,hv] at hh
    simpa only [Nat.succ_eq_add_one,pow_succ] using hh

/-- Exact positive Dirichlet mass at 2, with the n=0 convention included. -/
theorem tauDirichlet_square_mass (k : ℕ) :
    (∑'n:ℕ,(lemma34Tau (k+1) n:ℝ)/(n:ℝ)^2)=(Real.pi^2/6)^(k+1) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  have he : (∑'n:ℕ,((lemma34Tau (k+1) n:ℝ)/(n:ℝ)^2:ℝ):ℂ)=
      LSeries (fun n:ℕ => (lemma34Tau (k+1) n:ℂ)) 2 := by
    unfold LSeries
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (by norm_num : (2:ℂ)≠0)]
    push_cast
    rw [Complex.cpow_ofNat]
  rw [he,tauDirichlet_lseries_value k 2 (by norm_num),riemannZeta_two]
  push_cast
  rfl

/-- A small fixed numerical upper bound adequate for all later tail budgets. -/
theorem tauDirichlet_five_square_mass_le :
    (∑'n:ℕ,(lemma34Tau 5 n:ℝ)/(n:ℝ)^2)≤243 := by
  rw [tauDirichlet_square_mass 4]
  have hpi : 0≤Real.pi := Real.pi_pos.le
  have hpi4 := Real.pi_le_four
  have hb : Real.pi^2/6≤3 := by nlinarith
  have hh := pow_le_pow_left₀ (by positivity : 0≤Real.pi^2/6) hb 5
  norm_num at hh ⊢
  exact hh

end ZhangLS.Spec
