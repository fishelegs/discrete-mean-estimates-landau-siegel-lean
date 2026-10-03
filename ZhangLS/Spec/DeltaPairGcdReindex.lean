import ZhangLS.Spec.Proposition71DeltaPairs
import ZhangLS.Spec.PositiveGcdFilteredSums

/-! Genuine positive-pair Delta gcd reindexing for arbitrary positive Q.
The quantitative absolute bound still requires 1 <= Q*n <= P^10 on S.
Neither the long zero value nor a coprimality condition on Q is assumed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def deltaPairGcdTerm (D : ℕ) (Q : ℝ) (S : Finset ℕ)
    (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) (d l k : ℕ+) : ℂ :=
  if ((d : ℕ)*(k : ℕ))∈S then
    (d : ℂ)⁻¹*(a ((d : ℕ)*(k : ℕ))/(k : ℂ))*
      (κ ((d : ℕ)*(l : ℕ))*w ((d : ℕ)*(l : ℕ)) ((d : ℕ)*(k : ℕ)))*
        lemma53PaperDelta D ((l : ℝ)/(Q*(k : ℝ)))
  else 0

/-- Exact denominator and Delta scale cancellation, including the full Q. -/
theorem deltaPair_gcd_term_eq (D : ℕ) {Q : ℝ} (hQ : 0<Q) (S : Finset ℕ)
    (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) (d l k : ℕ+) :
    proposition71DeltaPair D Q S κ a w (d*l,d*k)=deltaPairGcdTerm D Q S κ a w d l k := by
  simp only [proposition71DeltaPair,proposition71FiniteShortPair,deltaPairGcdTerm,
    PNat.mul_coe,Nat.cast_mul]
  split_ifs with hn
  · have hdr : (d : ℝ)≠0 := by exact_mod_cast d.property.ne'
    have hdc : (d : ℂ)≠0 := by exact_mod_cast d.property.ne'
    have hscale : (d : ℝ)*(l : ℝ)/(Q*((d : ℝ)*(k : ℝ)))=(l : ℝ)/(Q*(k : ℝ)) := by field_simp
    rw [hscale]
    field_simp
  · rfl

/-- Joint absolute convergence of the actual gcd-indexed series is derived
from the finite-support Delta theorem and the exact bijection. -/
theorem deltaPair_gcd_summable {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {Q : ℝ} (hQ : 0<Q) (S : Finset ℕ)
    (hS : ∀n∈S, 0<n) (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    (hw : ∀n∈S, ∀m : ℕ, 0<m → ‖w m n‖≤1)
    (hq : ∀n∈S, 1≤Q*n ∧ Q*n≤lemma23PaperP D^10) :
    Summable (fun i : positiveGcdIndex => deltaPairGcdTerm D Q S κ a w i.1 i.2.val.1 i.2.val.2) := by
  have hs := (proposition71_delta_pairs_summable_and_bound hD hL hQ S hS κ a w hB hκ hw hq).1
  exact (positiveGcd_summable _ hs).congr (fun i => deltaPair_gcd_term_eq D hQ S κ a w _ _ _)

/-- Exact d,k,l reindexing of the original finite-short/infinite-long mean.
The actual sum is justified by proved convergence, not a formal Fubini step. -/
theorem deltaPair_gcd_nested_tsum {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {Q : ℝ} (hQ : 0<Q) (S : Finset ℕ)
    (hS : ∀n∈S, 0<n) (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    (hw : ∀n∈S, ∀m : ℕ, 0<m → ‖w m n‖≤1)
    (hq : ∀n∈S, 1≤Q*n ∧ Q*n≤lemma23PaperP D^10) :
    (∑n∈S, (a n/(n : ℂ))*(∑'m : ℕ+, κ (m : ℕ)*w (m : ℕ) n*
      lemma53PaperDelta D ((m : ℝ)/(Q*n))))=
      ∑'d : ℕ+, ∑'k : ℕ+, ∑'l : ℕ+,
        if Nat.Coprime (l : ℕ) (k : ℕ) then deltaPairGcdTerm D Q S κ a w d l k else 0 := by
  have hs := proposition71_delta_pairs_summable_and_bound hD hL hQ S hS κ a w hB hκ hw hq
  rw [←hs.2.2,positiveGcd_filtered_nested_tsum _ hs.1]
  apply tsum_congr
  intro d
  apply tsum_congr
  intro k
  apply tsum_congr
  intro l
  simp only [deltaPair_gcd_term_eq D hQ S κ a w]

end ZhangLS.Spec
