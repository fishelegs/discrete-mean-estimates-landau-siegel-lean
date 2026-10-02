import ZhangLS.Spec.RiemannZetaCriticalLineBound
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! # Actual zeta and inverse-zeta anchors in Re s>1

The inverse bound is proved from the actual Möbius Dirichlet series, rather
than assumed from a formal Euler product or a logarithmic-derivative bound.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped ComplexOrder
set_option maxHeartbeats 2500000

lemma proposition71_real_zeta_norm_mass {σ : ℝ} (hσ : 1<σ) :
    (∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖)=‖riemannZeta (σ : ℂ)‖ := by
  have ht (n : ℕ) : LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n=
      (‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ : ℂ) :=
    Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg (by norm_num : (0 : ℂ)≤(1 : ℕ → ℂ) n) σ)
  have he : Complex.ofReal (∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖)=riemannZeta (σ : ℂ) := by
    rw [←LSeries_one_eq_riemannZeta (by simpa using hσ)]
    simp only [Complex.ofReal_tsum,LSeries,←ht]
  have hh := congrArg norm he
  rw [Complex.norm_of_nonneg (tsum_nonneg (fun n => norm_nonneg _))] at hh
  exact hh

lemma proposition71_bounded_lseries_norm_zeta {s : ℂ} (hs : 1<s.re)
    (f : ℕ → ℂ) (hf : ∀n, 0<n → ‖f n‖≤1) :
    ‖LSeries f s‖≤‖riemannZeta (s.re : ℂ)‖ := by
  have hfs : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n hn => hf n (Nat.pos_of_ne_zero hn)) hs
  have hon : LSeriesSummable (1 : ℕ → ℂ) (s.re : ℂ) :=
    LSeriesSummable_one_iff.mpr (by simpa using hs)
  have ht (n : ℕ) : ‖LSeries.term f s n‖≤‖LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n‖ := by
    by_cases hn : n=0
    · subst n; simp
    simp only [LSeries.norm_term_eq,if_neg hn,Complex.ofReal_re,Pi.one_apply,norm_one]
    exact div_le_div_of_nonneg_right (hf n (Nat.pos_of_ne_zero hn)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfn := summable_norm_iff.mpr hfs
  have hon' := summable_norm_iff.mpr hon
  calc
    _≤∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hfn
    _≤∑' n, ‖LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n‖ := hfn.tsum_le_tsum ht hon'
    _=_ := proposition71_real_zeta_norm_mass hs

lemma proposition71_real_zeta_elementary_bound {σ : ℝ} (hσ : 1<σ) :
    ‖riemannZeta (σ : ℂ)‖≤2+1/(σ-1) := by
  have hσ0 : 0<σ := by linarith
  have hσ1 : (σ : ℂ)≠1 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hh := norm_riemannZeta_le_fractionalPart_formula (s := (σ : ℂ)) (by simpa using hσ0) hσ1
  have hnorm : ‖(σ : ℂ)-1‖=σ-1 := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_of_nonneg (by linarith : 0≤σ-1)]
  rw [Complex.norm_of_nonneg hσ0.le,hnorm,Complex.ofReal_re,div_self hσ0.ne'] at hh
  have he : σ/(σ-1)+1=2+1/(σ-1) := by
    field_simp [(sub_pos.mpr hσ).ne']
    ring
  exact hh.trans_eq he

/-- Both the direct and reciprocal actual zeta have a genuine absolute-series
anchor independent of height. -/
theorem proposition71_zeta_right_half_bounds {s : ℂ} (hs : 1<s.re) :
    ‖riemannZeta s‖≤2+1/(s.re-1) ∧ ‖(riemannZeta s)⁻¹‖≤2+1/(s.re-1) := by
  have hreal := proposition71_real_zeta_elementary_bound hs
  constructor
  · rw [←LSeries_one_eq_riemannZeta hs]
    exact (proposition71_bounded_lseries_norm_zeta hs 1 (by intro n hn; simp)).trans hreal
  · have he := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at he
    have hne := riemannZeta_ne_zero_of_one_lt_re hs
    have hinv : (riemannZeta s)⁻¹=LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by
      calc
        _=(riemannZeta s)⁻¹*(riemannZeta s*LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s) := by rw [he,mul_one]
        _=_ := by rw [←mul_assoc,inv_mul_cancel₀ hne,one_mul]
    rw [hinv]
    apply (proposition71_bounded_lseries_norm_zeta hs _ ?_).trans hreal
    intro n hn
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one

end ZhangLS.Spec
