import ZhangLS.Spec.Proposition141PrincipalSaving

/-! Literal source identification and unrestricted positive outer indices. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

/-- Positive d,k source summand before the support restriction. -/
noncomputable def proposition141PrincipalOuterTerm (D D₁ D₂ p:ℕ) (κ a:ℕ→ℂ)
    (i:ℕ×ℕ) : ℂ :=
  if 0 < i.1 ∧ 0 < i.2 ∧ Nat.Coprime i.2 D₁ then
    proposition141PrincipalRow D D₁ D₂ p i.1 i.2 κ a else 0

lemma proposition141_principal_row_of_coefficient_zero (D D₁ D₂ p d k:ℕ)
    (κ a:ℕ→ℂ) (ha:a (d*k)=0) : proposition141PrincipalRow D D₁ D₂ p d k κ a=0 := by
  simp only [proposition141PrincipalRow,ha,zero_div,mul_zero,zero_mul]

/-- The full character-expansion coefficient, not just an invented scalar bound. -/
theorem proposition141_principal_literal_row {D D₁ D₂ p d k:ℕ} [NeZero (D₂*k)]
    (κ a:ℕ→ℂ) :
    proposition141PrincipalRow D D₁ D₂ p d k κ a =
      (d:ℂ)⁻¹ * (a (d*k) / ((k:ℂ)*(Nat.totient (D₂*k):ℂ))) *
        (gaussSum (1:DirichletCharacter ℂ (D₂*k))⁻¹ ZMod.stdAddChar *
          ∑'l:ℕ,if 0<l then κ ((D₁*d)*l) *
            (1:DirichletCharacter ℂ (D₂*k)) (-(l:ZMod (D₂*k))) *
              conj ((1:DirichletCharacter ℂ (D₂*k)) (p:ZMod (D₂*k))) *
                lemma53PaperDelta D ((l:ℝ)/((D₂:ℝ)*(p:ℝ)*(k:ℝ))) else 0) := by
  unfold proposition141PrincipalRow
  rw [proposition141_principal_literal_gauss]

lemma proposition141_principal_outer_off_support {D D₁ D₂ p:ℕ} {Ba:ℝ}
    {κ a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a) (i:ℕ×ℕ)
    (hi:i∉proposition141Indices D ×ˢ proposition141Indices D) :
    proposition141PrincipalOuterTerm D D₁ D₂ p κ a i=0 := by
  unfold proposition141PrincipalOuterTerm
  split_ifs with h
  · apply proposition141_principal_row_of_coefficient_zero
    exact proposition141_omitted_coefficient_zero ha h.1 h.2.1 (by simpa only [mem_product] using hi)
  · rfl

/-- The closed source support, rather than an assumed truncation, proves
summability of every unrestricted positive d,k source row. -/
theorem proposition141_principal_original_outer_sum {D D₁ D₂ p:ℕ} {Ba:ℝ}
    {κ a:ℕ→ℂ} (ha:Proposition141AdmissibleSequence D Ba a) :
    HasSum (proposition141PrincipalOuterTerm D D₁ D₂ p κ a)
      (proposition141PrincipalCorrection D D₁ D₂ p κ a) := by
  have hs : HasSum (proposition141PrincipalOuterTerm D D₁ D₂ p κ a)
      (∑i∈proposition141Indices D ×ˢ proposition141Indices D,
        proposition141PrincipalOuterTerm D D₁ D₂ p κ a i) := hasSum_sum_of_ne_finset_zero
    (s:=proposition141Indices D ×ˢ proposition141Indices D)
    (f:=proposition141PrincipalOuterTerm D D₁ D₂ p κ a)
    (fun i hi=>proposition141_principal_outer_off_support ha i hi)
  have he : (∑i∈proposition141Indices D ×ˢ proposition141Indices D,
      proposition141PrincipalOuterTerm D D₁ D₂ p κ a i)=
      proposition141PrincipalCorrection D D₁ D₂ p κ a := by
    rw [sum_product]
    unfold proposition141PrincipalCorrection
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro k hk
    have hdpos := ((proposition141_mem_indices D d).mp hd).1
    have hkpos := ((proposition141_mem_indices D k).mp hk).1
    simp only [proposition141PrincipalOuterTerm,hdpos,hkpos,true_and]
  exact he ▸ hs

/-- Exact return to the paper's positive l indices, justified by genuine summability. -/
theorem proposition141_principal_positive_indices {D D₁ D₂ p d k:ℕ} {κ:ℕ→ℂ}
    (hs:Summable (proposition141PrincipalTerm D D₁ D₂ p d k κ)) :
    proposition141PrincipalInner D D₁ D₂ p d k κ =
      (ArithmeticFunction.moebius (D₂*k):ℂ) *
        ∑'l:ℕ+,κ ((D₁*d)*(l:ℕ)) * proposition141PrincipalWeight (D₂*k) p (l:ℕ) *
          lemma53PaperDelta D ((l:ℝ)/((D₂:ℝ)*(p:ℝ)*(k:ℝ))) := by
  have ht : (∑'l:ℕ+,proposition141PrincipalTerm D D₁ D₂ p d k κ (l:ℕ))=
      ∑'l:ℕ,proposition141PrincipalTerm D D₁ D₂ p d k κ l := by
    simpa only [proposition141PrincipalTerm,tauDeltaDilatedTerm,lt_self_iff_false,if_false,zero_add]
      using tsum_zero_pnat_eq_tsum_nat hs
  unfold proposition141PrincipalInner
  rw [←ht]
  apply congrArg ((ArithmeticFunction.moebius (D₂*k):ℂ) * ·)
  apply tsum_congr
  intro l
  simp only [proposition141PrincipalTerm,tauDeltaDilatedTerm]
  rw [if_pos (show 0<(l:ℕ) from l.property)]

end ZhangLS.Spec
