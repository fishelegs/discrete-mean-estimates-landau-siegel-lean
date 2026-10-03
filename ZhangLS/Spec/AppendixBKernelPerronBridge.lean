import ZhangLS.Spec.Lemma151Definitions
import ZhangLS.Spec.Lemma84LogPerronSeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! Exact full-kernel Perron bridge for the original Appendix B arithmetic.
The summand keeps l₁, the genuine finite-D β, and strict support. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical ArithmeticFunction.zeta

lemma appendixB_twist_term (β s : ℂ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    LSeries.term (lemma151Twist β f) s n = LSeries.term f (s-β) n := by
  by_cases hn : n=0
  · simp [hn]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
  simp only [lemma151Twist,ArithmeticFunction.coe_mk,div_eq_mul_inv,
    ← Complex.cpow_neg]
  rw [mul_comm ((n : ℂ)^β) (f n),mul_assoc,← Complex.cpow_add _ _ hnC]
  congr 2
  ring

lemma appendixB_twist_summable (β s : ℂ) (f : ArithmeticFunction ℂ)
    (hf : LSeriesSummable f (s-β)) : LSeriesSummable (lemma151Twist β f) s := by
  exact hf.congr (fun n => (appendixB_twist_term β s f n).symm)

lemma appendixB_twist_LSeries (β s : ℂ) (f : ArithmeticFunction ℂ) :
    LSeries (lemma151Twist β f) s = LSeries f (s-β) := by
  unfold LSeries
  exact tsum_congr (appendixB_twist_term β s f)

/-- Genuine absolutely convergent Dirichlet series, with its actual zeta quotient. -/
theorem appendixB_rho_dirichlet_series {β s : ℂ} (hβ : β.re=0) (hs : 1<s.re) :
    LSeriesSummable (lemma151Rho β) s ∧
      LSeries (lemma151Rho β) s=riemannZeta s/riemannZeta (s-β) := by
  have hsβ : 1<(s-β).re := by simpa [hβ] using hs
  have hμ : LSeriesSummable (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (s-β) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsβ
  have ht := appendixB_twist_summable β s _ hμ
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hsum := ArithmeticFunction.LSeriesHasSum_mul hz.LSeriesHasSum ht.LSeriesHasSum
  refine ⟨hsum.LSeriesSummable,?_⟩
  rw [lemma151Rho,ArithmeticFunction.LSeries_mul' hz ht,appendixB_twist_LSeries]
  simp only [ArithmeticFunction.natCoe_apply]
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  have hi := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hsβ
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsβ] at hi
  have hi' : riemannZeta (s-β)*LSeries (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (s-β)=1 := by
    simpa only [ArithmeticFunction.intCoe_apply] using hi
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hsβ)).mpr
  calc
    _ = riemannZeta s*(riemannZeta (s-β)*LSeries (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (s-β)) := by ring
    _ = _ := by rw [hi',mul_one]

/-- This is the source's positive-l sum; the n=0 convention contributes zero. -/
noncomputable def appendixBFullKernelSum (X : ℝ) (β γ : ℂ) (l₁ : ℕ) : ℂ :=
  ∑' l : ℕ, lemma151Kernel X γ (l₁*l)*lemma151Rho β l/l

lemma appendixB_kernel_perron_term {X : ℝ} (hX : 0<X) (hlog : Real.log X≠0)
    (β γ : ℂ) {l₁ : ℕ} (hl : 0<l₁) (n : ℕ) :
    lemma151Kernel X γ (l₁*n)*lemma151Rho β n/n =
      lemma84PerronTerm (lemma151Rho β) (-γ) (X/l₁) n/(Real.log X : ℂ) := by
  by_cases hn : n=0
  · subst n
    simp [lemma151Kernel,lemma84PerronTerm]
  have hnp : 0<n := Nat.pos_of_ne_zero hn
  have hnr : (0 : ℝ)<n := by exact_mod_cast hnp
  have hlr : (0 : ℝ)<l₁ := by exact_mod_cast hl
  have hprod : 0<l₁*n := Nat.mul_pos hl hnp
  have hcut : (n : ℝ)<X/l₁ ↔ ((l₁*n : ℕ) : ℝ)<X := by
    rw [lt_div_iff₀ hlr,Nat.cast_mul,mul_comm]
  have hdiv : X/(l₁ : ℝ)/(n : ℝ)=X/((l₁*n : ℕ) : ℝ) := by
    push_cast
    ring
  unfold lemma151Kernel lemma84PerronTerm
  simp only [hprod,true_and,if_neg hn,neg_neg,hcut]
  split_ifs with h
  · rw [hdiv,Real.log_div hX.ne' (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hprod))]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hlog]
    <;> ring
  · simp

/-- Exact source Perron formula on any positive initial line. The source
normalizer log X and shift X/l₁ are not replaced by asymptotic equivalents. -/
theorem appendixB_full_kernel_perron {X b : ℝ} (hX : 0<X) (hlog : Real.log X≠0)
    (hb : 0<b) {β γ : ℂ} (hβ : β.re=0) (hγ : γ.re=0)
    {l₁ : ℕ} (hl : 0<l₁) :
    appendixBFullKernelSum X β γ l₁ =
      (2*Real.pi : ℂ)⁻¹*(∫ t : ℝ,
        (riemannZeta (1+((b : ℂ)+I*(t : ℂ)))/
          riemannZeta (1+((b : ℂ)+I*(t : ℂ))-β))*
        (((X/l₁ : ℝ) : ℂ)^((b : ℂ)+I*(t : ℂ))/((b : ℂ)+I*(t : ℂ)-γ)^2)) /
          (Real.log X : ℂ) := by
  have hx : 0<X/(l₁ : ℝ) := div_pos hX (Nat.cast_pos.mpr hl)
  have ha := (appendixB_rho_dirichlet_series hβ (by simpa using hb : 1<(((1+b : ℝ) : ℂ)).re)).1
  have hi := lemma84_log_perron_series_identity (lemma151Rho β) hb (-γ) (by simp [hγ]) hx ha
  unfold appendixBFullKernelSum
  simp_rw [appendixB_kernel_perron_term hX hlog β γ hl]
  rw [tsum_div_const,←hi]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  rw [(appendixB_rho_dirichlet_series hβ (by simpa using hb : 1<(1+((b : ℂ)+I*(t : ℂ))).re)).2]
  simp only [sub_eq_add_neg]

end ZhangLS.Spec
