import ZhangLS.Spec.ReciprocalDeltaGcd
import ZhangLS.Spec.PositiveNatFiniteSupport

/-! Exact extraction of the finite d,k support after genuine gcd reindexing.
The source support S may be strict (Section7) or closed (Section14). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def reciprocalDeltaFiniteGcdMean (D A p : ℕ) (S T : Finset ℕ)
    (κ a : ℕ → ℂ) : ℂ :=
  ∑d∈T, ∑k∈T, if hd : 0<d then if hk : 0<k then
    ∑'l : ℕ+, if Nat.Coprime (l : ℕ) k then
      reciprocalDeltaGcdTerm D A p S κ a ⟨d,hd⟩ l ⟨k,hk⟩ else 0
  else 0 else 0

/-- Finite outer extraction costs no analytic estimate and keeps the exact
original condition d*k∈S. -/
theorem reciprocalDelta_gcd_finite_outer (D A p : ℕ) (S T : Finset ℕ)
    (κ a : ℕ → ℂ)
    (hfac : ∀d k : ℕ, 0<d → 0<k → d*k∈S → d∈T ∧ k∈T) :
    (∑'d : ℕ+, ∑'k : ℕ+, ∑'l : ℕ+,
      if Nat.Coprime (l : ℕ) (k : ℕ) then reciprocalDeltaGcdTerm D A p S κ a d l k else 0)=
        reciprocalDeltaFiniteGcdMean D A p S T κ a := by
  have hdout (d : ℕ+) (hd : (d : ℕ)∉T) (k l : ℕ+) :
      reciprocalDeltaGcdTerm D A p S κ a d l k=0 := by
    have hn : (d : ℕ)*(k : ℕ)∉S := fun hh => hd (hfac _ _ d.property k.property hh).1
    simp only [reciprocalDeltaGcdTerm,if_neg hn]
  have hkout (k : ℕ+) (hk : (k : ℕ)∉T) (d l : ℕ+) :
      reciprocalDeltaGcdTerm D A p S κ a d l k=0 := by
    have hn : (d : ℕ)*(k : ℕ)∉S := fun hh => hk (hfac _ _ d.property k.property hh).2
    simp only [reciprocalDeltaGcdTerm,if_neg hn]
  rw [positiveNat_tsum_eq_finset _ T (fun d hd => by simp only [hdout d hd,ite_self,tsum_zero])]
  unfold reciprocalDeltaFiniteGcdMean
  apply sum_congr rfl
  intro d hd
  by_cases hd0 : 0<d
  · rw [dif_pos hd0]
    rw [positiveNat_tsum_eq_finset _ T (fun k hk => by simp only [hkout k hk,ite_self,tsum_zero])]
    apply sum_congr rfl
    intro k hk
    simp only [dif_pos hd0]
    rfl
  · simp only [dif_neg hd0,sum_const_zero]

/-- Direct source-to-finite-gcd interface, with true A*p scale conditions. -/
theorem reciprocalDelta_source_finite_gcd {D A p : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hA : 0<A)
    (S T : Finset ℕ) (hS : ∀n∈S, 0<n) (κ a : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ))
    (hp : ∀n∈S, p.Coprime (A*n))
    (hq : ∀n∈S, 1≤((A : ℝ)*(p : ℝ))*n ∧
      ((A : ℝ)*(p : ℝ))*n≤lemma23PaperP D^10)
    (hfac : ∀d k : ℕ, 0<d → 0<k → d*k∈S → d∈T ∧ k∈T) :
    (∑n∈S, (a n/(n : ℂ))*(∑'m : ℕ+,
      κ (m : ℕ)*lemma53PaperDeltaOne D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ)))*
        ZMod.stdAddChar ((m : ZMod p)*((A*n : ℕ) : ZMod p)⁻¹)))=
      reciprocalDeltaFiniteGcdMean D A p S T κ a := by
  rw [reciprocalDelta_source_gcd_tsum hD hL hA S hS κ a hB hκ hp hq,
    reciprocalDelta_gcd_finite_outer D A p S T κ a hfac]

end ZhangLS.Spec
