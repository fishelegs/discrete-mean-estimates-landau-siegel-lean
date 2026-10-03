import ZhangLS.Spec.Proposition71FiniteShortPairs
import ZhangLS.Spec.Proposition71PositiveNatSeries
import ZhangLS.Spec.TauWeightedDeltaCoefficients

/-! # Actual Δ series on all positive long/short pairs

The scale Q stays arbitrary. Thus Q=p and Q=Dp use the same theorem.
Finite support is kept literally and joint summability is proved before any
infinite gcd rearrangement. The zero value of κ is never constrained.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71DeltaPair (D : ℕ) (Q : ℝ) (S : Finset ℕ)
    (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) : ℕ+×ℕ+ → ℂ :=
  proposition71FiniteShortPair S (fun m n =>
    (a n/(n : ℂ))*(κ (m : ℕ)*w (m : ℕ) n*lemma53PaperDelta D ((m : ℝ)/(Q*n))))

/-- The actual absolute long fiber, with the short denominator canceled only
against the actual scale Q*n. -/
lemma proposition71_delta_pair_fiber {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {Q : ℝ} (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    {n : ℕ} (hn : 0<n) (hw : ∀m : ℕ, 0<m → ‖w m n‖≤1)
    (hq : 1≤Q*n) (hqP : Q*n≤lemma23PaperP D^10) :
    Summable (fun m : ℕ+ => (a n/(n : ℂ))*(κ (m : ℕ)*w (m : ℕ) n*
      lemma53PaperDelta D ((m : ℝ)/(Q*n)))) ∧
    (∑'m : ℕ+, ‖(a n/(n : ℂ))*(κ (m : ℕ)*w (m : ℕ) n*
      lemma53PaperDelta D ((m : ℝ)/(Q*n)))‖)≤
      tauDeltaAbsoluteConstant*B*Q*lemma23PaperL D^575*‖a n‖ := by
  let f := tauDeltaDilatedTerm D κ (fun m => w m n) 1 (Q*n)
  have hτ1 : lemma34Tau 5 1=1 := (lemma34_tau_multiplicative 5).map_one
  have ht := tauDelta_actual_dilated_absolute_sum hD hL κ hB hκ (by norm_num : 0<(1:ℕ)) hq hqP
  have hnf : Summable (fun m : ℕ => ‖f m‖) := Summable.of_nonneg_of_le
    (fun m => norm_nonneg _) (tauDelta_dilated_term_norm_le D κ (fun m => w m n) hw 1 (Q*n)) ht.1
  have hf : Summable f := summable_norm_iff.mp hnf
  have hpn := proposition71_positive_nat_summable f hf
  have he (m : ℕ+) : f (m : ℕ)=κ (m : ℕ)*w (m : ℕ) n*lemma53PaperDelta D ((m : ℝ)/(Q*n)) := by
    simp [f,tauDeltaDilatedTerm]
  have hs := (hpn.mul_left (a n/(n : ℂ))).congr (fun m => congrArg (fun z => (a n/(n : ℂ))*z) (he m))
  refine ⟨hs,?_⟩
  have hbound : (∑'m : ℕ, ‖f m‖)≤tauDeltaAbsoluteConstant*B*(Q*n)*lemma23PaperL D^575 := by
    exact (hnf.tsum_le_tsum (tauDelta_dilated_term_norm_le D κ (fun m => w m n) hw 1 (Q*n)) ht.1).trans
      (by simpa only [hτ1,Nat.cast_one,mul_one] using ht.2)
  have hpzero : ‖f 0‖=0 := by simp [f,tauDeltaDilatedTerm]
  have hpnorm := proposition71_positive_nat_tsum (fun m => ‖f m‖) hpzero
  have hnp : 0<(n : ℝ) := by exact_mod_cast hn
  calc
    _=‖a n/(n : ℂ)‖*(∑'m : ℕ+, ‖f (m : ℕ)‖) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro m
      rw [norm_mul,he]
    _=‖a n/(n : ℂ)‖*(∑'m : ℕ, ‖f m‖) := by rw [hpnorm]
    _≤‖a n/(n : ℂ)‖*(tauDeltaAbsoluteConstant*B*(Q*n)*lemma23PaperL D^575) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _=_ := by
      rw [norm_div,Complex.norm_natCast]
      field_simp

/-- Full positive-pair absolute convergence and exact supported short-fiber
sum, with a genuine q·L^575 bound and no normalization of a. -/
theorem proposition71_delta_pairs_summable_and_bound {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {Q : ℝ} (_hQ : 0<Q) (S : Finset ℕ)
    (hS : ∀n∈S, 0<n) (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    (hw : ∀n∈S, ∀m : ℕ, 0<m → ‖w m n‖≤1)
    (hq : ∀n∈S, 1≤Q*n ∧ Q*n≤lemma23PaperP D^10) :
    Summable (proposition71DeltaPair D Q S κ a w) ∧
    (∑'mn : ℕ+×ℕ+, ‖proposition71DeltaPair D Q S κ a w mn‖)≤
      tauDeltaAbsoluteConstant*B*Q*lemma23PaperL D^575*(∑n∈S, ‖a n‖) ∧
    (∑'mn : ℕ+×ℕ+, proposition71DeltaPair D Q S κ a w mn)=
      ∑n∈S, (a n/(n : ℂ))*(∑'m : ℕ+, κ (m : ℕ)*w (m : ℕ) n*
        lemma53PaperDelta D ((m : ℝ)/(Q*n))) := by
  let f := fun (m : ℕ+) (n : ℕ) => (a n/(n : ℂ))*(κ (m : ℕ)*w (m : ℕ) n*
    lemma53PaperDelta D ((m : ℝ)/(Q*n)))
  have hf (n : ℕ) (hn : n∈S) := proposition71_delta_pair_fiber hD hL κ a w hB hκ
    (hS n hn) (hw n hn) (hq n hn).1 (hq n hn).2
  have hs := proposition71_finite_short_pair_hasSum S hS f (fun n hn => (hf n hn).1)
  refine ⟨hs.summable,?_,?_⟩
  · have hn := proposition71_finite_short_pair_hasSum S hS (fun m n => ‖f m n‖)
      (fun n hn => (hf n hn).1.norm)
    have he (mn : ℕ+×ℕ+) : ‖proposition71DeltaPair D Q S κ a w mn‖=
        proposition71FiniteShortPair S (fun m n => ‖f m n‖) mn := by
      simp only [proposition71DeltaPair,proposition71FiniteShortPair,f]
      split_ifs <;> simp only [norm_zero]
    calc
      _=∑'mn : ℕ+×ℕ+, proposition71FiniteShortPair S (fun m n => ‖f m n‖) mn := tsum_congr he
      _=∑n∈S, ∑'m : ℕ+, ‖f m n‖ := hn.tsum_eq
      _≤∑n∈S, tauDeltaAbsoluteConstant*B*Q*lemma23PaperL D^575*‖a n‖ := sum_le_sum (fun n hn => (hf n hn).2)
      _=_ := by rw [mul_sum]
  · calc
      _=∑n∈S, ∑'m : ℕ+, f m n := hs.tsum_eq
      _=_ := by apply sum_congr rfl; intro n hn; exact tsum_mul_left

end ZhangLS.Spec
