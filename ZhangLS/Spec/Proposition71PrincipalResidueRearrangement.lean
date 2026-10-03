import ZhangLS.Spec.Proposition71PrincipalQuadruple
import ZhangLS.Spec.Proposition71ResidueMeanAttachment
import ZhangLS.Spec.Section721FiniteRearrangement

/-! Exact arithmetic rearrangement of the actual local principal residues
into the literal S* and then original S_j. No analytic residue approximation
or contour conclusion is a premise. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4500000

lemma proposition71_principal_residue_power {p k l : ℕ} (hp : 0<p) (hk : 0<k) (hl : 0<l) (b : ℂ) :
    ((((p : ℝ)*(k : ℝ)/(l : ℝ) : ℝ) : ℂ)^(1-b))/(k : ℂ)=
      (p : ℂ)^(1-b)/((k : ℂ)^b*(l : ℂ)^(1-b)) := by
  have hpR : 0<(p : ℝ) := by exact_mod_cast hp
  have hkR : 0<(k : ℝ) := by exact_mod_cast hk
  have hlR : 0<(l : ℝ) := by exact_mod_cast hl
  have hkC : (k : ℂ)≠0 := by exact_mod_cast hk.ne'
  have hlC : (l : ℂ)≠0 := by exact_mod_cast hl.ne'
  have hkpow : (k : ℂ)^b≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hkC)
  have hlpow : (l : ℂ)^(1-b)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hlC)
  rw [proposition71_positive_ratio_cpow (mul_pos hpR hkR) hlR,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hpR.le hkR.le]
  simp only [Complex.ofReal_natCast]
  rw [Complex.cpow_sub 1 b hkC,Complex.cpow_one,Complex.cpow_neg (l : ℂ) (1-b)]
  field_simp <;> ring

noncomputable def proposition71PrincipalQuadResidue (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (d₁ d₂ k l₂ : ℕ) : ℂ :=
  if d₁*d₂*k∈lemma81PolynomialIndices D ∧ l₂.Coprime k then
    a₂ (d₁*d₂*k)*(ArithmeticFunction.moebius k : ℂ)*a₁ (d₂*l₂)/
      ((d₁ : ℂ)*(d₂ : ℂ)*(k : ℂ)*(k.totient : ℂ))*
        ∑j : Fin 3,proposition71ActualR D c j*
          lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d₂*k) (1-lemma83PaperBeta D c j)*
          lemma83Lambda (lemma83PaperBeta D c) (d₁*d₂*k) (1-lemma83PaperBeta D c j)*
          ((((p : ℝ)*(k : ℝ)/(l₂ : ℝ) : ℝ) : ℂ)^(1-lemma83PaperBeta D c j))
  else 0

lemma proposition71_principal_residue_star_term {D p d₁ d₂ k l₂ : ℕ}
    (hp : 0<p) (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hl₂ : 0<l₂)
    (c : ℝ) (j : Fin 3) (a₁ a₂ : ℕ → ℂ) :
    a₂ (d₁*d₂*k)*(ArithmeticFunction.moebius k : ℂ)*a₁ (d₂*l₂)/
      ((d₁ : ℂ)*(d₂ : ℂ)*(k : ℂ)*(k.totient : ℂ))*
      (proposition71ActualR D c j*
        lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d₂*k) (1-lemma83PaperBeta D c j)*
        lemma83Lambda (lemma83PaperBeta D c) (d₁*d₂*k) (1-lemma83PaperBeta D c j)*
        ((((p : ℝ)*(k : ℝ)/(l₂ : ℝ) : ℝ) : ℂ)^(1-lemma83PaperBeta D c j)))=
      proposition71ActualR D c j*(p : ℂ)^(1-lemma83PaperBeta D c j)*
        section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d₂ d₁ k l₂ := by
  have hpw := proposition71_principal_residue_power hp hk hl₂ (lemma83PaperBeta D c j)
  unfold section721StarTerm
  have h := congrArg (fun z : ℂ =>
    a₂ (d₁*d₂*k)*(ArithmeticFunction.moebius k : ℂ)*a₁ (d₂*l₂)*proposition71ActualR D c j*
      lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d₂*k) (1-lemma83PaperBeta D c j)*
      lemma83Lambda (lemma83PaperBeta D c) (d₁*d₂*k) (1-lemma83PaperBeta D c j)/
      ((d₁ : ℂ)*(d₂ : ℂ)*(k.totient : ℂ))*z) hpw
  convert h using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

/-- Product support is removed only using the actual zero a2 coefficient;
the original long/short coprimality remains in the source S* term. -/
theorem proposition71_principal_quad_residue_expanded {D p d₁ d₂ k l₂ : ℕ}
    (hp : 0<p) (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hl₂ : 0<l₂)
    (c : ℝ) {B₂ : ℝ} (a₁ a₂ : ℕ → ℂ) (ha₂ : Lemma81AdmissibleSequence D B₂ a₂) :
    proposition71PrincipalQuadResidue D p c a₁ a₂ d₁ d₂ k l₂=
      ∑j : Fin 3,proposition71ActualR D c j*(p : ℂ)^(1-lemma83PaperBeta D c j)*
        (if l₂.Coprime k then section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d₂ d₁ k l₂ else 0) := by
  unfold proposition71PrincipalQuadResidue
  by_cases hcop : l₂.Coprime k
  · by_cases hprod : d₁*d₂*k∈lemma81PolynomialIndices D
    · rw [if_pos ⟨hprod,hcop⟩,mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [if_pos hcop]
      exact proposition71_principal_residue_star_term hp hd₁ hd₂ hk hl₂ c j a₁ a₂
    · have hz : a₂ (d₁*d₂*k)=0 := by
        apply ha₂.2
        apply le_of_not_gt
        intro hh
        exact hprod ((proposition71_mem_indices D _).mpr ⟨Nat.mul_pos (Nat.mul_pos hd₁ hd₂) hk,hh⟩)
      simp [hprod,hcop,hz,section721StarTerm]
  · simp [hcop]

/-- Exact post-contour residue arithmetic is the original S_j, including
all supported modified-kappa, lambda, totient and complex-power factors. -/
theorem proposition71_principal_quad_residue_sum {D p : ℕ} (hp : 0<p) (c : ℝ)
    {B₁ B₂ : ℝ} (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ha₂ : Lemma81AdmissibleSequence D B₂ a₂) :
    (∑d₁∈lemma81PolynomialIndices D,∑d₂∈lemma81PolynomialIndices D,
      ∑k∈lemma81PolynomialIndices D,∑l₂∈lemma81PolynomialIndices D,
        proposition71PrincipalQuadResidue D p c a₁ a₂ d₁ d₂ k l₂)=
      ∑j : Fin 3,proposition71ActualR D c j*(p : ℂ)^(1-lemma83PaperBeta D c j)*
        proposition71ArithmeticSum D c j a₁ a₂ := by
  let S := lemma81PolynomialIndices D
  let R := fun j : Fin 3 => proposition71ActualR D c j*(p : ℂ)^(1-lemma83PaperBeta D c j)
  have hj (j : Fin 3) :
      (∑d₁∈S,∑d₂∈S,∑k∈S,∑l₂∈S,
        R j*(if l₂.Coprime k then section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d₂ d₁ k l₂ else 0))=
      R j*proposition71ArithmeticSum D c j a₁ a₂ := by
    rw [←section721_star_eq_arithmetic_sum c j ha₁ ha₂]
    unfold section721StarArithmeticSum
    rw [sum_comm]
    simp only [S,section721StarTerm,mul_sum,sum_filter,mul_ite,mul_zero]
  have he : (∑d₁∈S,∑d₂∈S,∑k∈S,∑l₂∈S,proposition71PrincipalQuadResidue D p c a₁ a₂ d₁ d₂ k l₂)=
      ∑d₁∈S,∑d₂∈S,∑k∈S,∑l₂∈S,∑j : Fin 3,
        R j*(if l₂.Coprime k then section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d₂ d₁ k l₂ else 0) := by
    apply sum_congr rfl; intro d₁ hd₁
    apply sum_congr rfl; intro d₂ hd₂
    apply sum_congr rfl; intro k hk
    apply sum_congr rfl; intro l₂ hl₂
    exact proposition71_principal_quad_residue_expanded hp ((proposition71_mem_indices D d₁).mp hd₁).1
      ((proposition71_mem_indices D d₂).mp hd₂).1 ((proposition71_mem_indices D k).mp hk).1
      ((proposition71_mem_indices D l₂).mp hl₂).1 c a₁ a₂ ha₂
  change (∑d₁∈S,∑d₂∈S,∑k∈S,∑l₂∈S,proposition71PrincipalQuadResidue D p c a₁ a₂ d₁ d₂ k l₂)=_
  rw [he]
  simp only [Fin.sum_univ_three,sum_add_distrib]
  rw [hj 0,hj 1,hj 2]

end ZhangLS.Spec
