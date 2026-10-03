import ZhangLS.Spec.ChiUniformLBound
import ZhangLS.Spec.Lemma23GoodSet
import Mathlib.Algebra.BigOperators.Module

/-! A source-character bound for the new Proposition 2.6 arithmetic route.
The actual χ-harmonic sum is O(log D) uniformly at all finite cutoffs and
up to frequency/conductor height. Complex finite variation costs exactly
its endpoint plus its total successive variation. No (A) or mean bound is
needed for this arithmetic input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- A uniform actual finite χ polynomial bound on Re s=1, with no dependence
on the cutoff x. The large-height allowance is ‖s‖≤D, well beyond L^20. -/
theorem proposition26_chi_harmonic_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) {s : ℂ}
    (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ)) {x : ℝ} (hx : 1≤x) :
    ‖lemma82FinitePolynomial χ x s‖ ≤
      (14*Real.exp 16+2)*lemma23PaperL D := by
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD.le
  have hDp : (0:ℝ)<D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have hxp : 0<x := by linarith
  have he : 1≤Real.exp 16 := Real.one_le_exp_iff.mpr (by norm_num)
  by_cases hsmall : x≤(D:ℝ)^2
  · have hp := chi_finite_polynomial_harmonic_bound χ hx
      (M:=1) (fun t ht htx => by rw [hs]; norm_num) (by norm_num)
    have hl := Real.log_le_log hxp hsmall
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    change Real.log x≤2*lemma23PaperL D at hl
    norm_num only [one_mul] at hp
    nlinarith only [hp,hl,hL,he,mul_nonneg (sub_nonneg.mpr he) hLp.le]
  · have hDx : (D:ℝ)^2≤x := (lt_of_not_ge hsmall).le
    have hLfun := chi_actual_L_uniform_log_bound χ hD hL
      (s:=s) (by rw [hs]; exact sub_le_self _ (by positivity))
      (hnorm.trans (by nlinarith only [hDp]))
    have herr := chi_actual_truncation_error χ hD hx (s:=s) (by rw [hs]; norm_num)
    rw [hs,Real.rpow_neg_one,div_one] at herr
    have htail : ‖dirichletLFunction χ s-lemma82FinitePolynomial χ x s‖≤2 := by
      apply herr.trans
      calc
        x⁻¹*(D:ℝ)*(‖s‖+1)≤x⁻¹*(D:ℝ)*(2*(D:ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hnorm,hD1]) (by positivity)
        _ = 2*((D:ℝ)^2/x) := by ring
        _ ≤ 2*1 := mul_le_mul_of_nonneg_left ((div_le_one hxp).mpr hDx) (by norm_num)
        _ = 2 := by ring
    have ht := norm_sub_le (dirichletLFunction χ s)
      (dirichletLFunction χ s-lemma82FinitePolynomial χ x s)
    rw [sub_sub_cancel] at ht
    change ‖dirichletLFunction χ s‖≤14*Real.exp 16*lemma23PaperL D at hLfun
    nlinarith only [ht,hLfun,htail,hL]

/-- Finite complex Abel summation exposes the exact variation cost.
The partial-sum premise is discharged for actual χ by the theorem above. -/
theorem proposition26_complex_variation_bound (f g : ℕ→ℂ) (N : ℕ) (K : ℝ)
    (hg : ∀ k≤N, ‖∑ i∈range k,g i‖≤K) :
    ‖∑ i∈range N,f i*g i‖ ≤
      K*(‖f (N-1)‖+∑ i∈range (N-1),‖f (i+1)-f i‖) := by
  change ‖∑ i∈range N,f i • g i‖≤_
  rw [Finset.sum_range_by_parts]
  apply (norm_sub_le _ _).trans
  have he : ‖f (N-1) • (∑ i∈range N,g i)‖ ≤ ‖f (N-1)‖*K := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hg N le_rfl) (norm_nonneg _)
  have hv : ‖∑ i∈range (N-1),(f (i+1)-f i) • (∑ j∈range (i+1),g j)‖ ≤
      (∑ i∈range (N-1),‖f (i+1)-f i‖)*K := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply sum_le_sum
    intro i hi
    rw [norm_smul]
    have hik : i+1≤N := by have := mem_range.mp hi; omega
    exact mul_le_mul_of_nonneg_left (hg (i+1) hik) (norm_nonneg _)
  exact (add_le_add he hv).trans_eq (by ring)

/-- The actual shifted χ sequence is uniformly bounded at every finite
prefix; no generic arithmetic coefficient has replaced χ. -/
theorem proposition26_chi_harmonic_range {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) {s : ℂ}
    (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ)) (N : ℕ) :
    ‖∑ i∈range N,χ.evalNat (i+1)*((i+1:ℕ):ℂ)^(-s)‖ ≤
      (14*Real.exp 16+2)*lemma23PaperL D := by
  by_cases hN : N=0
  · subst N
    simp only [sum_range_zero,norm_zero]
    positivity
  have hNp : 1≤N := Nat.one_le_iff_ne_zero.mpr hN
  have he : (∑ i∈range N,χ.evalNat (i+1)*((i+1:ℕ):ℂ)^(-s)) =
      lemma82FinitePolynomial χ N s := by
    unfold lemma82FinitePolynomial
    rw [Nat.floor_natCast,range_eq_Ico]
    rw [Finset.sum_Ico_add' (fun i : ℕ => χ.evalNat i*(i:ℂ)^(-s)) 0 N (c:=1)]
    simp only [Finset.Ico_add_one_right_eq_Icc,zero_add]
  rw [he]
  exact proposition26_chi_harmonic_uniform χ hD hL hs hnorm (by exact_mod_cast hNp)

/-- Actual complex BV profiles multiplying χ(n)n^-s, uniformly in every
finite cutoff and every Re s=1, ‖s‖≤D. -/
theorem proposition26_chi_harmonic_variation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤lemma23PaperL D) {s : ℂ}
    (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ)) (N : ℕ) (f : ℕ→ℂ) :
    ‖∑ i∈range N,f i*(χ.evalNat (i+1)*((i+1:ℕ):ℂ)^(-s))‖ ≤
      ((14*Real.exp 16+2)*lemma23PaperL D)*
        (‖f (N-1)‖+∑ i∈range (N-1),‖f (i+1)-f i‖) :=
  proposition26_complex_variation_bound f _ N _
    (fun k _ => proposition26_chi_harmonic_range χ hD hL hs hnorm k)

end ZhangLS.Spec
