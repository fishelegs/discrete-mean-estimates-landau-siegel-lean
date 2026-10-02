import ZhangLS.Spec.CharacterAbelAnalyticContinuation
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Complex.Liouville

namespace ZhangLS.Spec
open Complex Finset MeasureTheory Set
open scoped Real
set_option maxHeartbeats 1000000

/-- Actual finite character polynomial, with the inclusive endpoint. The later
logarithmic weight vanishes exactly at an integer endpoint. -/
noncomputable def lemma82FinitePolynomial {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.evalNat n * (n : ℂ)^(-s)

lemma lemma82_sum_zero_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, χ.evalNat n) = ∑ n ∈ Finset.Icc 1 N, χ.evalNat n := by
  letI : Fact (1 < D) := ⟨hD⟩
  rw [← Finset.insert_Icc_add_one_left_eq_Icc N.zero_le, Finset.sum_insert (by simp)]
  simp [RealPrimitiveCharacter.evalNat, χ.chi.map_zero]

lemma lemma82_finite_abel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    lemma82FinitePolynomial χ x s =
      (x : ℂ)^(-s) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.evalNat n) +
      s * ∫ t in Set.Ioc 1 x,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ)^(-(s+1)) := by
  letI : Fact (1 < D) := ⟨hD⟩
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => (t : ℂ)^(-s))
        ((-s) * (t : ℂ)^(-s-1)) t :=
    hasDerivAt_ofReal_cpow_const (by linarith [ht.1]) hs0
  have hi : IntegrableOn (deriv (fun t : ℝ => (t : ℂ)^(-s))) (Set.Icc 1 x) := by
    apply IntegrableOn.congr_fun
      (f := fun t : ℝ => (-s) * (t : ℂ)^(-s-1))
    · apply ContinuousOn.integrableOn_Icc
      exact continuousOn_const.mul (fun t ht =>
        (Complex.continuousAt_ofReal_cpow_const t (-s-1)
          (Or.inr (by linarith [ht.1]))).continuousWithinAt)
    · intro t ht
      exact (hd t ht).deriv.symm
    · exact measurableSet_Icc
  have hh := sum_mul_eq_sub_integral_mul₀ (c := χ.evalNat)
    (by simp [RealPrimitiveCharacter.evalNat, χ.chi.map_zero]) x
    (fun t ht => (hd t ht).differentiableAt) hi
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℂ)^(-s) * χ.evalNat n) =
      lemma82FinitePolynomial χ x s := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊),
      Finset.sum_insert (by simp)]
    have hz : χ.evalNat 0 = 0 := by simp [RealPrimitiveCharacter.evalNat, χ.chi.map_zero]
    rw [hz, mul_zero, zero_add]
    unfold lemma82FinitePolynomial
    exact Finset.sum_congr rfl (fun n hn => mul_comm _ _)
  simp only [Complex.ofReal_natCast] at hh
  rw [hsum, lemma82_sum_zero_endpoint χ hD] at hh
  rw [hh, ← integral_const_mul, sub_eq_add_neg]
  congr 1
  rw [← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, lemma82_sum_zero_endpoint χ hD]
  rw [show -s - 1 = -(s+1) by ring]
  ring

lemma lemma82_abel_tail_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi x,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ)^(-(s+1))‖ ≤
      (D : ℝ) * x^(-s.re) / s.re := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hi := (χ.abelIntegrand_integrable hD hs).mono_set
    (show Set.Ioi x ⊆ Set.Ioi (1:ℝ) from fun t ht => hx.trans_lt ht)
  have hm : IntegrableOn (fun t : ℝ => (D:ℝ) * t^(-s.re-1)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hxp).const_mul _
  calc
    _ ≤ ∫ t in Set.Ioi x, ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) *
        (t : ℂ)^(-(s+1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi x, (D:ℝ)*t^(-s.re-1) := by
      apply integral_mono_ae hi.norm hm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htp : 0 < t := hxp.trans ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htp]
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re, neg_add_rev]
      rw [show -1 + -s.re = -s.re-1 by ring]
      exact mul_le_mul_of_nonneg_right
        (χ.norm_sum_Icc_evalNat_le_modulus hD _) (Real.rpow_nonneg htp.le _)
    _ = (D:ℝ)*x^(-s.re)/s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hxp]
      rw [show -s.re-1+1 = -s.re by ring]
      ring

lemma lemma82_actual_abel_remainder {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    dirichletLFunction χ s - lemma82FinitePolynomial χ x s =
      s * (∫ t in Set.Ioi x,
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ)^(-(s+1))) -
      (x : ℂ)^(-s) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.evalNat n) := by
  let f : ℝ → ℂ := fun t =>
    (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ)^(-(s+1))
  have hi : IntegrableOn f (Set.Ioi 1) := χ.abelIntegrand_integrable hD hs
  have hfin : IntegrableOn f (Set.Ioc 1 x) := hi.mono_set (fun t ht => ht.1)
  have htail : IntegrableOn f (Set.Ioi x) := hi.mono_set (fun t ht => hx.trans_lt ht)
  have hu : Set.Ioc 1 x ∪ Set.Ioi x = Set.Ioi (1:ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨ht,_⟩ | ht)
      · exact ht
      · exact hx.trans_lt ht
    · intro ht
      by_cases htx : t ≤ x
      · exact Or.inl ⟨ht,htx⟩
      · exact Or.inr (lt_of_not_ge htx)
  have hdis : Disjoint (Set.Ioc 1 x) (Set.Ioi x) := by
    exact Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht')
  have hsplit : characterAbelIntegral χ s =
      (∫ t in Set.Ioc 1 x, f t) + ∫ t in Set.Ioi x, f t := by
    unfold characterAbelIntegral
    change (∫ t in Set.Ioi 1, f t) = _
    rw [← hu, setIntegral_union hdis measurableSet_Ioi hfin htail]
  rw [dirichletLFunction_eq_abelIntegral_of_pos_re χ hD hs,
    lemma82_finite_abel χ hD hx hs, hsplit]
  dsimp [f]
  ring

end ZhangLS.Spec
