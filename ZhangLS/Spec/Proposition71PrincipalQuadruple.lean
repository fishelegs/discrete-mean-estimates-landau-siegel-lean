import ZhangLS.Spec.Proposition71PrincipalFiniteFactors
import ZhangLS.Spec.FiniteDivisorProductReindex
import ZhangLS.Spec.Proposition71PrincipalSplitAttachment

/-! Literal source (7.18) with finite original outer support and the complete
inner coprime-kappa series. Every support guard remains explicit. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4500000

noncomputable def proposition71PrincipalQuadTerm (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (d₁ d₂ k l₂ : ℕ) : ℂ :=
  if d₁*d₂*k∈lemma81PolynomialIndices D ∧ l₂.Coprime k then
    a₂ (d₁*d₂*k)*(ArithmeticFunction.moebius k : ℂ)*a₁ (d₂*l₂)/
      ((d₁ : ℂ)*(d₂ : ℂ)*(k : ℂ)*(k.totient : ℂ))*
        ∑'l₁ : Proposition71CoprimeIndex (d₂*k),lemma83Kappa (lemma83PaperBeta D c) (d₁*l₁.val)*
          lemma53PaperDelta D ((l₁.val : ℝ)*(l₂ : ℝ)/((p : ℝ)*(k : ℝ)))
  else 0

noncomputable def proposition71PrincipalQuadMean (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑d₁∈lemma81PolynomialIndices D,∑d₂∈lemma81PolynomialIndices D,
    ∑k∈lemma81PolynomialIndices D,∑l₂∈lemma81PolynomialIndices D,
      proposition71PrincipalQuadTerm D p c a₁ a₂ d₁ d₂ k l₂

/-- A complete source block becomes the exact finite d1,d2,l2 factors of
(7.18); the true complementary d2*k coprimality remains in the inner series. -/
lemma proposition71_principal_block_quad_split {D p d k : ℕ}
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (c : ℝ)
    (hd : 0<d) (hk : 0<k) (hp : 0<p) {B : ℝ}
    (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B a₁) :
    proposition71PrincipalGcdBlock D p d k c a₁ a₂=
      ∑dd∈d.divisorsAntidiagonal,∑l₂∈lemma81PolynomialIndices D,
        proposition71PrincipalQuadTerm D p c a₁ a₂ dd.1 dd.2 k l₂ := by
  unfold proposition71PrincipalGcdBlock
  by_cases hdk : d*k∈lemma81PolynomialIndices D
  · rw [if_pos ⟨hd,hk,hdk⟩,proposition71_principal_delta_finite_factorization hD hL c hd hk hp a₁ ha₁]
    simp only [mul_sum]
    apply sum_congr rfl
    intro dd hdd
    have hdprod := (Nat.mem_divisorsAntidiagonal.mp hdd).1
    apply sum_congr rfl
    intro l₂ hl₂
    have hpS : dd.1*dd.2*k∈lemma81PolynomialIndices D := by simpa only [hdprod] using hdk
    unfold proposition71PrincipalQuadTerm
    by_cases hlc : l₂.Coprime k
    · rw [if_pos hlc,if_pos ⟨hpS,hlc⟩]
      simp only [hdprod]
      have hcast : (dd.1 : ℂ)*(dd.2 : ℂ)=(d : ℂ) := by exact_mod_cast hdprod
      rw [←hcast]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · rw [if_neg hlc,if_neg (show ¬(dd.1*dd.2*k∈lemma81PolynomialIndices D ∧ l₂.Coprime k) from fun hh => hlc hh.2)]
      simp only [mul_zero]
  · rw [if_neg (fun hh => hdk hh.2.2)]
    symm
    apply sum_eq_zero
    intro dd hdd
    have hdprod := (Nat.mem_divisorsAntidiagonal.mp hdd).1
    apply sum_eq_zero
    intro l₂ hl₂
    simp [proposition71PrincipalQuadTerm,hdprod,hdk]

/-- The actual principal prime mean has exactly the four source summations
in (7.18). No contour estimate or residue conclusion appears as a premise. -/
theorem proposition71_prime_principal_eq_quad {D p : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (c : ℝ) (hp : 0<p) {B : ℝ}
    (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B a₁) :
    proposition71PrimePrincipalMean D p c a₁ a₂=proposition71PrincipalQuadMean D p c a₁ a₂ := by
  let S := lemma81PolynomialIndices D
  let F := fun d₁ d₂ : ℕ => ∑k∈S,∑l₂∈S,proposition71PrincipalQuadTerm D p c a₁ a₂ d₁ d₂ k l₂
  have he : proposition71PrimePrincipalMean D p c a₁ a₂=
      ∑d∈S,∑dd∈d.divisorsAntidiagonal,F dd.1 dd.2 := by
    unfold proposition71PrimePrincipalMean
    apply sum_congr rfl
    intro d hd
    calc
      _=∑k∈S,∑dd∈d.divisorsAntidiagonal,∑l₂∈S,
          proposition71PrincipalQuadTerm D p c a₁ a₂ dd.1 dd.2 k l₂ := by
        apply sum_congr rfl
        intro k hk
        exact proposition71_principal_block_quad_split hD hL c
          ((proposition71_mem_indices D d).mp hd).1 ((proposition71_mem_indices D k).mp hk).1 hp a₁ a₂ ha₁
      _=_ := sum_comm
  rw [he,finiteDivisorProduct_reindex S
    (fun n hn => ((proposition71_mem_indices D n).mp hn).1)
    (fun d k hd hk hdk => proposition71_short_factors hd hk hdk) F]
  unfold proposition71PrincipalQuadMean
  apply sum_congr rfl
  intro d₁ hd₁
  apply sum_congr rfl
  intro d₂ hd₂
  by_cases hprod : d₁*d₂∈S
  · rw [if_pos hprod]
  · rw [if_neg hprod]
    symm
    apply sum_eq_zero
    intro k hk
    apply sum_eq_zero
    intro l₂ hl₂
    have hd₁p := ((proposition71_mem_indices D d₁).mp hd₁).1
    have hd₂p := ((proposition71_mem_indices D d₂).mp hd₂).1
    have hkp := ((proposition71_mem_indices D k).mp hk).1
    have hbad : d₁*d₂*k∉lemma81PolynomialIndices D := fun hh => hprod
      (proposition71_short_factors (Nat.mul_pos hd₁p hd₂p) hkp hh).1
    simp [proposition71PrincipalQuadTerm,hbad]

end ZhangLS.Spec
