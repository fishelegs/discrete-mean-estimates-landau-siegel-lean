import ZhangLS.Spec.Proposition71PrincipalMellinSource
import ZhangLS.Spec.Proposition71GcdAttachment
import ZhangLS.Spec.PositivePairNatExtension
import ZhangLS.Spec.NatProductFiberSums

/-! Joint convergence of the actual two-factor principal convolution terms.
The short a1 coefficient is the only finite support; the long factor remains
unrestricted except for the exact original coprimality conditions. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3500000

noncomputable def proposition71PrincipalPairTerm (D p d₁ d₂ k : ℕ) (c : ℝ)
    (a : ℕ → ℂ) (mn : ℕ×ℕ) : ℂ :=
  if 0<mn.1 ∧ 0<mn.2 ∧ mn.1.Coprime (d₂*k) ∧ mn.2.Coprime k then
    lemma83Kappa (lemma83PaperBeta D c) (d₁*mn.1)*a (d₂*mn.2)*
      lemma53PaperDelta D ((mn.1 : ℝ)*(mn.2 : ℝ)/((p : ℝ)*(k : ℝ))) else 0

lemma proposition71_principal_pair_zero_product (D p d₁ d₂ k : ℕ) (c : ℝ) (a : ℕ → ℂ)
    (m n : ℕ) (h : m*n=0) : proposition71PrincipalPairTerm D p d₁ d₂ k c a (m,n)=0 := by
  rcases Nat.mul_eq_zero.mp h with hm | hn
  · simp [proposition71PrincipalPairTerm,hm]
  · simp [proposition71PrincipalPairTerm,hn]

lemma proposition71_short_coefficient_zero_off_factors {D d n : ℕ} {B : ℝ}
    (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a) (hd : 0<d) (hn : 0<n)
    (hnot : n∉lemma81PolynomialIndices D) : a (d*n)=0 := by
  apply ha.2
  apply le_of_not_gt
  intro hh
  have hdn := (proposition71_mem_indices D (d*n)).mpr ⟨Nat.mul_pos hd hn,hh⟩
  exact hnot (proposition71_short_factors hd hn hdn).2

/-- The genuine coprime Mellin coefficient series gives the zero-extended
positive long fiber used in the actual convolution rearrangement. -/
lemma proposition71_principal_long_fiber_summable {D p d₁ d₂ k l₂ : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ)
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hp : 0<p) (hl₂ : 0<l₂) :
    Summable (fun l₁ : ℕ+ => if (l₁ : ℕ).Coprime (d₂*k) then
      lemma83Kappa (lemma83PaperBeta D c) (d₁*(l₁ : ℕ))*
        lemma53PaperDelta D ((l₁ : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ))) else 0) := by
  have hs := (proposition71_original_principal_mellin_source hD hL c hd₁ hd₂ hk hp hl₂).1
  have hn := (summable_subtype_iff_indicator
    (s := {n : ℕ | n≠0 ∧ n.Coprime (d₂*k)})
    (f := fun n : ℕ => lemma83Kappa (lemma83PaperBeta D c) (d₁*n)*
      lemma53PaperDelta D ((n : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ))))).mp hs
  have hh := proposition71_positive_nat_summable _ hn
  apply hh.congr
  intro l₁
  by_cases hcop : (l₁ : ℕ).Coprime (d₂*k)
  · have hmem : (l₁ : ℕ)∈{n : ℕ | n≠0 ∧ n.Coprime (d₂*k)} :=
      ⟨l₁.ne_zero,hcop⟩
    rw [Set.indicator_of_mem hmem,if_pos hcop]
  · have hmem : (l₁ : ℕ)∉{n : ℕ | n≠0 ∧ n.Coprime (d₂*k)} :=
      fun hh => hcop hh.2
    rw [Set.indicator_of_notMem hmem,if_neg hcop]

/-- Actual absolute double-series convergence, before product-fiber
reindexing. Coefficients are only assumed bounded and strictly supported. -/
theorem proposition71_principal_pair_summable {D p d₁ d₂ k : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ)
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hp : 0<p)
    {B : ℝ} (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a) :
    Summable (proposition71PrincipalPairTerm D p d₁ d₂ k c a) := by
  let f := fun (m : ℕ+) (n : ℕ) => if (m : ℕ).Coprime (d₂*k) ∧ n.Coprime k then
    lemma83Kappa (lemma83PaperBeta D c) (d₁*(m : ℕ))*a (d₂*n)*
      lemma53PaperDelta D ((m : ℝ)*(n : ℝ)/((p : ℝ)*(k : ℝ))) else 0
  have hf (n : ℕ) (hn : n∈lemma81PolynomialIndices D) : Summable (fun m : ℕ+ => f m n) := by
    have hn0 := ((proposition71_mem_indices D n).mp hn).1
    by_cases hnc : n.Coprime k
    · have hh := (proposition71_principal_long_fiber_summable hD hL c hd₁ hd₂ hk hp hn0).mul_left (a (d₂*n))
      apply hh.congr
      intro m
      rcases m with ⟨m,hm0⟩
      change a (d₂*n)*(if m.Coprime (d₂*k) then
        lemma83Kappa (lemma83PaperBeta D c) (d₁*m)*
          lemma53PaperDelta D ((m : ℝ)*(n : ℝ)/((p : ℝ)*(k : ℝ))) else 0)=
        (if m.Coprime (d₂*k) ∧ n.Coprime k then
          lemma83Kappa (lemma83PaperBeta D c) (d₁*m)*a (d₂*n)*
            lemma53PaperDelta D ((m : ℝ)*(n : ℝ)/((p : ℝ)*(k : ℝ))) else 0)
      by_cases hmc : m.Coprime (d₂*k)
      · rw [if_pos hmc,if_pos (And.intro hmc hnc)]
        ring
      · rw [if_neg hmc,if_neg (show ¬(m.Coprime (d₂*k) ∧ n.Coprime k) from fun hh => hmc hh.1)]
        exact mul_zero _
    · have hz : (fun m : ℕ+ => f m n)=fun _ => 0 := by funext m; simp [f,hnc]
      rw [hz]
      exact summable_zero
  have hs := proposition71_finite_short_pair_summable (lemma81PolynomialIndices D)
    (fun n hn => ((proposition71_mem_indices D n).mp hn).1) f hf
  apply positivePairNatCoe_summable _ (proposition71_principal_pair_zero_product D p d₁ d₂ k c a)
  apply hs.congr
  intro mn
  rcases mn with ⟨⟨m,hm0⟩,⟨n,hn0⟩⟩
  change (if n∈lemma81PolynomialIndices D then
      (if m.Coprime (d₂*k) ∧ n.Coprime k then
        lemma83Kappa (lemma83PaperBeta D c) (d₁*m)*a (d₂*n)*
          lemma53PaperDelta D ((m : ℝ)*(n : ℝ)/((p : ℝ)*(k : ℝ))) else 0) else 0)=
    (if 0<m ∧ 0<n ∧ m.Coprime (d₂*k) ∧ n.Coprime k then
      lemma83Kappa (lemma83PaperBeta D c) (d₁*m)*a (d₂*n)*
        lemma53PaperDelta D ((m : ℝ)*(n : ℝ)/((p : ℝ)*(k : ℝ))) else 0)
  by_cases hn : n∈lemma81PolynomialIndices D
  · simp only [if_pos hn,hm0,hn0,true_and]
  · have hz := proposition71_short_coefficient_zero_off_factors a ha hd₂ hn0 hn
    simp only [if_neg hn,hm0,hn0,true_and,hz,mul_zero,zero_mul,ite_self]

end ZhangLS.Spec
