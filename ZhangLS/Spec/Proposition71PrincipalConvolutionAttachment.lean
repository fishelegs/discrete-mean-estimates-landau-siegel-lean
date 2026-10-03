import ZhangLS.Spec.Proposition71PrincipalPairSeries
import ZhangLS.Spec.Proposition71ConvolutionSplit
import ZhangLS.Spec.Proposition71CharacterFibers

/-! Exact full-series (7.17) attachment to the original principal Delta fiber.
All product-fiber exchanges start from proved joint absolute summability. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000

lemma proposition71_principal_convolution_pointwise {D p d k l : ℕ}
    (hd : 0<d) (hl : 0<l) (c : ℝ) (a : ℕ → ℂ) :
    (if l.Coprime k then
      (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*
        lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(k : ℝ))) else 0)=
      ∑dd∈d.divisorsAntidiagonal,∑mn∈l.divisorsAntidiagonal,
        proposition71PrincipalPairTerm D p dd.1 dd.2 k c a mn := by
  by_cases hc : l.Coprime k
  · rw [if_pos hc,proposition71_kappa_convolution_split _ _ hd.ne' hl.ne']
    simp only [sum_mul,sum_filter]
    apply sum_congr rfl
    intro dd hdd
    have hdprod := (Nat.mem_divisorsAntidiagonal.mp hdd).1
    have hd₁ : 0<dd.1 := Nat.pos_of_mul_pos_right (hdprod.symm ▸ hd)
    have hd₂ : 0<dd.2 := Nat.pos_of_mul_pos_left (hdprod.symm ▸ hd)
    apply sum_congr rfl
    intro mn hmn
    have hmprod := (Nat.mem_divisorsAntidiagonal.mp hmn).1
    have hm : 0<mn.1 := Nat.pos_of_mul_pos_right (hmprod.symm ▸ hl)
    have hn : 0<mn.2 := Nat.pos_of_mul_pos_left (hmprod.symm ▸ hl)
    have hcmn : mn.1.Coprime k ∧ mn.2.Coprime k := by
      rw [←Nat.coprime_mul_iff_left,hmprod]
      exact hc
    have harg : (mn.1 : ℝ)*(mn.2 : ℝ)=(l : ℝ) := by exact_mod_cast hmprod
    by_cases hcd : mn.1.Coprime dd.2
    · have hcm : mn.1.Coprime (dd.2*k) := hcd.mul_right hcmn.1
      rw [if_pos hcd]
      unfold proposition71PrincipalPairTerm
      rw [if_pos (And.intro hm (And.intro hn (And.intro hcm hcmn.2))),harg,
        proposition71_arithmetic_sequence_positive a (Nat.mul_pos hd₂ hn)]
    · have hcm : ¬mn.1.Coprime (dd.2*k) := fun hh => hcd (Nat.coprime_mul_iff_right.mp hh).1
      simp [if_neg hcd,proposition71PrincipalPairTerm,hcm]
  · rw [if_neg hc]
    symm
    apply sum_eq_zero
    intro dd hdd
    apply sum_eq_zero
    intro mn hmn
    have hmprod := (Nat.mem_divisorsAntidiagonal.mp hmn).1
    have hbad : ¬(0<mn.1 ∧ 0<mn.2 ∧ mn.1.Coprime (dd.2*k) ∧ mn.2.Coprime k) := by
      intro hh
      apply hc
      rw [←hmprod]
      exact ((Nat.coprime_mul_iff_right.mp hh.2.2.1).2).mul_left hh.2.2.2
    simp only [proposition71PrincipalPairTerm,if_neg hbad]

/-- Literal infinite (7.17), with summability proved before exchanging the
finite d-divisors and infinite product fibers. -/
theorem proposition71_principal_delta_convolution_split {D p d k : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ) (hd : 0<d) (hk : 0<k) (hp : 0<p)
    {B : ℝ} (a : ℕ → ℂ) (ha : Lemma81AdmissibleSequence D B a) :
    proposition71PrincipalDeltaFiber D d k ((p : ℝ)*(k : ℝ))
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m)=
        ∑dd∈d.divisorsAntidiagonal,∑'mn : ℕ×ℕ,
          proposition71PrincipalPairTerm D p dd.1 dd.2 k c a mn := by
  let F := fun (dd : ℕ×ℕ) (l : ℕ) => ∑mn∈l.divisorsAntidiagonal,
    proposition71PrincipalPairTerm D p dd.1 dd.2 k c a mn
  have hs (dd : ℕ×ℕ) (hdd : dd∈d.divisorsAntidiagonal) :
      Summable (F dd) ∧ (∑'l : ℕ,F dd l)=∑'mn : ℕ×ℕ,proposition71PrincipalPairTerm D p dd.1 dd.2 k c a mn := by
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hdd).1
    have hd₁ : 0<dd.1 := Nat.pos_of_mul_pos_right (hprod.symm ▸ hd)
    have hd₂ : 0<dd.2 := Nat.pos_of_mul_pos_left (hprod.symm ▸ hd)
    exact natProduct_summable_divisorsAntidiagonal _
      (proposition71_principal_pair_summable hD hL c hd₁ hd₂ hk hp a ha)
      (proposition71_principal_pair_zero_product D p dd.1 dd.2 k c a)
  let G := fun l : ℕ => if 0<l ∧ l.Coprime k then
    (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*
      lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(k : ℝ))) else 0
  have hpoint (l : ℕ) : G l=∑dd∈d.divisorsAntidiagonal,F dd l := by
    by_cases hl : 0<l
    · dsimp [G,F]
      simp only [hl,true_and]
      exact proposition71_principal_convolution_pointwise hd hl c a
    · have hz : l=0 := by omega
      subst l
      simp [G,F]
  have hpos : proposition71PrincipalDeltaFiber D d k ((p : ℝ)*(k : ℝ))
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) m)=∑'l : ℕ,G l := by
    rw [←proposition71_positive_nat_tsum G (by simp [G])]
    unfold proposition71PrincipalDeltaFiber
    apply tsum_congr
    intro l
    simp only [G,PNat.pos,true_and]
  rw [hpos]
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun dd hdd => (hs dd hdd).1)]
  exact sum_congr rfl (fun dd hdd => (hs dd hdd).2)

end ZhangLS.Spec
