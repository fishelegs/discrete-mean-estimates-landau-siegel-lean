import ZhangLS.Spec.Proposition71PrincipalConvolutionAttachment

/-! Exact finite extraction of the actual supported second convolution factor.
The remaining long factor is the literal coprime kappa series used in (7.19). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3500000

/-- The actual convergent pair sum is a finite l2 sum of genuine complete
coprime-l1 rows. No product-dependent coefficient support is weakened. -/
theorem proposition71_principal_pair_tsum_finite {D p d₁ d₂ k : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ)
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hp : 0<p)
    {B : ℝ} (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a) :
    (∑'mn : ℕ×ℕ,proposition71PrincipalPairTerm D p d₁ d₂ k c a mn)=
      ∑l₂∈lemma81PolynomialIndices D, if l₂.Coprime k then
        a (d₂*l₂)*(∑'l₁ : Proposition71CoprimeIndex (d₂*k),
          lemma83Kappa (lemma83PaperBeta D c) (d₁*l₁.val)*
            lemma53PaperDelta D ((l₁.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ)))) else 0 := by
  have hs := proposition71_principal_pair_summable hD hL c hd₁ hd₂ hk hp a ha
  have hcomm :
      (∑'n : ℕ,∑'m : ℕ,proposition71PrincipalPairTerm D p d₁ d₂ k c a (m,n))=
      (∑'m : ℕ,∑'n : ℕ,proposition71PrincipalPairTerm D p d₁ d₂ k c a (m,n)) :=
    Summable.tsum_comm (f := fun m n : ℕ => proposition71PrincipalPairTerm D p d₁ d₂ k c a (m,n)) hs
  rw [hs.tsum_prod,←hcomm]
  have hz (n : ℕ) (hn : n∉lemma81PolynomialIndices D) (m : ℕ) :
      proposition71PrincipalPairTerm D p d₁ d₂ k c a (m,n)=0 := by
    by_cases hn0 : n=0
    · simp [proposition71PrincipalPairTerm,hn0]
    · have hcoef := proposition71_short_coefficient_zero_off_factors a ha hd₂ (Nat.pos_of_ne_zero hn0) hn
      simp [proposition71PrincipalPairTerm,hcoef]
  rw [tsum_eq_sum (s := lemma81PolynomialIndices D) (fun n hn => by simp only [hz n hn,tsum_zero])]
  apply sum_congr rfl
  intro n hn
  have hn0 := ((proposition71_mem_indices D n).mp hn).1
  by_cases hnc : n.Coprime k
  · rw [if_pos hnc,proposition71_coprime_index_weight_tsum (d₂*k)
      (fun m : ℕ => lemma83Kappa (lemma83PaperBeta D c) (d₁*m)*
        lemma53PaperDelta D ((m : ℝ)*(n : ℝ)/((p : ℝ)*(k : ℝ)))),←tsum_mul_left]
    apply tsum_congr
    intro m
    by_cases hm0 : m=0
    · subst m
      simp [proposition71PrincipalPairTerm]
    · have hm : 0<m := Nat.pos_of_ne_zero hm0
      by_cases hmc : m.Coprime (d₂*k)
      · unfold proposition71PrincipalPairTerm
        rw [if_pos (And.intro hm (And.intro hn0 (And.intro hmc hnc))),if_neg hm0,if_pos hmc]
        ring
      · simp [proposition71PrincipalPairTerm,hm,hn0,hmc,hnc,hm0]
  · simp [proposition71PrincipalPairTerm,hnc]

/-- The complete infinite principal convolution has precisely the source
(7.18) inner structure, before any contour displacement or residue estimate. -/
theorem proposition71_principal_delta_finite_factorization {D p d k : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ) (hd : 0<d) (hk : 0<k) (hp : 0<p)
    {B : ℝ} (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a) :
    proposition71PrincipalDeltaFiber D d k ((p : ℝ)*(k : ℝ))
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m)=
      ∑dd∈d.divisorsAntidiagonal,∑l₂∈lemma81PolynomialIndices D, if l₂.Coprime k then
        a (dd.2*l₂)*(∑'l₁ : Proposition71CoprimeIndex (dd.2*k),
          lemma83Kappa (lemma83PaperBeta D c) (dd.1*l₁.val)*
            lemma53PaperDelta D ((l₁.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ)))) else 0 := by
  rw [proposition71_principal_delta_convolution_split hD hL c hd hk hp a ha]
  apply sum_congr rfl
  intro dd hdd
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hdd).1
  have hd₁ : 0<dd.1 := Nat.pos_of_mul_pos_right (hprod.symm ▸ hd)
  have hd₂ : 0<dd.2 := Nat.pos_of_mul_pos_left (hprod.symm ▸ hd)
  exact proposition71_principal_pair_tsum_finite hD hL c hd₁ hd₂ hk hp a ha

end ZhangLS.Spec
