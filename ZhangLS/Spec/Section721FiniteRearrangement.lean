import ZhangLS.Spec.Section721ArithmeticWeights

/-! # The literal finite identity (7.21)

S* is defined from its four source summations, not from S. The finite box is
the original strict n < P T⁻² cutoff. All changes of finite summation range
are justified by the actual vanishing of the two admissible sequences.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 6000000

/-- The S* displayed after (7.20), with its literal coefficients and weights. -/
noncomputable def section721StarArithmeticSum (D : ℕ) (c : ℝ) (j : Fin 3)
    (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑ d ∈ lemma81PolynomialIndices D, ∑ d₁ ∈ lemma81PolynomialIndices D,
    ∑ k ∈ lemma81PolynomialIndices D,
      (a₂ (d₁*d*k) * lemma83ModifiedKappa (lemma83PaperBeta D c) d₁ (d*k)
        (1-lemma83PaperBeta D c j) *
        lemma83Lambda (lemma83PaperBeta D c) (d₁*d*k) (1-lemma83PaperBeta D c j) *
        (ArithmeticFunction.moebius k : ℂ) /
        ((d₁ : ℂ)*(d : ℂ)*(Nat.totient k : ℂ)*(k : ℂ)^lemma83PaperBeta D c j)) *
      (∑ l ∈ (lemma81PolynomialIndices D).filter (fun l => l.Coprime k),
        a₁ (d*l)/(l : ℂ)^(1-lemma83PaperBeta D c j))

noncomputable def section721StarTerm (β : Fin 3 → ℂ) (j : Fin 3)
    (a₁ a₂ : ℕ → ℂ) (d a k l : ℕ) : ℂ :=
  (a₂ (a*d*k) * lemma83ModifiedKappa β a (d*k) (1-β j) *
    lemma83Lambda β (a*d*k) (1-β j) * (ArithmeticFunction.moebius k : ℂ) /
      ((a : ℂ)*(d : ℂ)*(Nat.totient k : ℂ)*(k : ℂ)^β j)) *
    (a₁ (d*l)/(l : ℂ)^(1-β j))

noncomputable def section721ReindexedTerm (β : Fin 3 → ℂ) (j : Fin 3)
    (a₁ a₂ : ℕ → ℂ) (d r m a k : ℕ) : ℂ :=
  (↑|ArithmeticFunction.moebius r| : ℂ) /
      ((d : ℂ)*(r : ℂ)*(Nat.totient r : ℂ)) *
    (a₁ (d*r*m)/(m : ℂ)^(1-β j)) *
    (a₂ (d*r*(a*k))*lemma83Lambda β (d*r*(a*k)) (1-β j)/(a*k : ℂ)) *
    (if k.Coprime r then lemma83ModifiedKappa β a (d*r*k) (1-β j) *
      (ArithmeticFunction.moebius k : ℂ)*(k : ℂ)^(1-β j)/(Nat.totient k : ℂ)
    else 0)

lemma section721_supported_le_mem {D n N : ℕ} {B : ℝ} {a : ℕ → ℂ}
    (ha : Lemma81AdmissibleSequence D B a) (hn : 0<n) (hle : n≤N) (hN : a N≠0) :
    n ∈ lemma81PolynomialIndices D := by
  rw [proposition71_mem_indices]
  refine ⟨hn,?_⟩
  have hc : (N : ℝ)<lemma81Cutoff D := lt_of_not_ge (fun h => hN (ha.2 N h))
  exact (by exact_mod_cast hle : (n : ℝ)≤(N : ℝ)).trans_lt hc

/-- The source four-index sum is genuinely supported in the displayed finite
box: every omitted positive coefficient product is zero. -/
theorem section721_omitted_star_coefficient_zero {D d a k l : ℕ}
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂)
    (hd : 0<d) (ha : 0<a) (hk : 0<k) (hl : 0<l)
    (hout : ¬(d ∈ lemma81PolynomialIndices D ∧ a ∈ lemma81PolynomialIndices D ∧
      k ∈ lemma81PolynomialIndices D ∧ l ∈ lemma81PolynomialIndices D)) :
    a₁ (d*l)*a₂ (a*d*k)=0 := by
  by_contra hn
  have hn' := mul_ne_zero_iff.mp hn
  have had : 0<a*d := Nat.mul_pos ha hd
  have hadk : a*d≤a*d*k := by nlinarith
  have had1 : d≤a*d := by nlinarith
  have had2 : a≤a*d := by nlinarith
  apply hout
  exact ⟨section721_supported_le_mem h₂ hd (had1.trans hadk) hn'.2,
    section721_supported_le_mem h₂ ha (had2.trans hadk) hn'.2,
    section721_supported_le_mem h₂ hk (by nlinarith) hn'.2,
    section721_supported_le_mem h₁ hl (by nlinarith) hn'.1⟩

/-- The strict support endpoints themselves contribute zero. -/
theorem section721_star_term_cutoff_zero {D d a k l : ℕ} (c : ℝ) (j : Fin 3)
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂)
    (hout : lemma81Cutoff D ≤ ((d*l : ℕ) : ℝ) ∨
      lemma81Cutoff D ≤ ((a*d*k : ℕ) : ℝ)) :
    section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d a k l = 0 := by
  rcases hout with h | h
  · simp [section721StarTerm,h₁.2 _ h]
  · simp [section721StarTerm,h₂.2 _ h]

/-- Termwise substitution, including the vanished noncoprime branch. -/
theorem section721_star_term_substitution (β : Fin 3 → ℂ) (j : Fin 3)
    (a₁ a₂ : ℕ → ℂ) {d a r k m : ℕ}
    (hd : 0<d) (ha : 0<a) (hr : 0<r) (hk : 0<k) (hm : 0<m) :
    section721StarTerm β j a₁ a₂ d a (r*k) (r*m) *
      (ArithmeticFunction.moebius r : ℂ) =
      section721ReindexedTerm β j a₁ a₂ d r m a k := by
  have hprod : a*d*(r*k)=d*r*(a*k) := by ring
  have hweight := section721_weight_rearrangement (β j) ha hd hr hk hm
  unfold section721StarTerm section721ReindexedTerm
  rw [hprod,←mul_assoc d r k,←mul_assoc d r m]
  push_cast
  by_cases hc : k.Coprime r
  · simp only [if_pos hc] at hweight ⊢
    linear_combination hweight * a₂ (d*r*(a*k)) *
      lemma83ModifiedKappa β a (d*r*k) (1-β j) *
      lemma83Lambda β (d*r*(a*k)) (1-β j) * a₁ (d*r*m)
  · simp only [if_neg hc,mul_zero] at hweight ⊢
    linear_combination hweight * a₂ (d*r*(a*k)) *
      lemma83ModifiedKappa β a (d*r*k) (1-β j) *
      lemma83Lambda β (d*r*(a*k)) (1-β j) * a₁ (d*r*m)

/-- Möbius insertion and the genuine two-variable common-divisor reindexing. -/
theorem section721_star_inner_reindex {D : ℕ} (c : ℝ) (j : Fin 3)
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂) {d a : ℕ}
    (hd : d ∈ lemma81PolynomialIndices D) (ha : a ∈ lemma81PolynomialIndices D) :
    (∑ k ∈ lemma81PolynomialIndices D,
      ∑ l ∈ (lemma81PolynomialIndices D).filter (fun l => l.Coprime k),
        section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d a k l) =
    ∑ r ∈ lemma81PolynomialIndices D, ∑ k ∈ lemma81PolynomialIndices D,
      ∑ m ∈ lemma81PolynomialIndices D,
        section721ReindexedTerm (lemma83PaperBeta D c) j a₁ a₂ d r m a k := by
  have hI := section721_indices_lower D
  have hdp := hI.1 _ hd
  have hap := hI.1 _ ha
  simp_rw [proposition71_mobius_insert]
  rw [section721_common_divisor_reindex _ hI]
  · apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro m hm
    exact section721_star_term_substitution _ _ _ _ hdp hap
      (hI.1 _ hr) (hI.1 _ hk) (hI.1 _ hm)
  · intro k l hk hl hn
    have h1 : a₁ (d*l)≠0 := by
      intro hz; apply hn; simp [section721StarTerm,hz]
    have h2 : a₂ (a*d*k)≠0 := by
      intro hz; apply hn; simp [section721StarTerm,hz]
    have had : 0<a*d := Nat.mul_pos hap hdp
    exact ⟨section721_supported_le_mem h₂ hk (by nlinarith) h2,
      section721_supported_le_mem h₁ hl (by nlinarith) h1⟩

/-- The actual divisor convolution collapses to λ₀ⱼ(dr) ξ₀ⱼ(n;d,r). -/
theorem section721_divisor_sum_collapse (β : Fin 3 → ℂ) (j : Fin 3)
    (a₁ a₂ : ℕ → ℂ) {d r m n : ℕ}
    (hd : 0<d) (hr : 0<r) (hn : 0<n) :
    (∑ ab ∈ n.divisorsAntidiagonal,
      section721ReindexedTerm β j a₁ a₂ d r m ab.1 ab.2) =
    (↑|ArithmeticFunction.moebius r| : ℂ) *
      lemma83Lambda β (d*r) (1-β j) /
        ((d : ℂ)*(r : ℂ)*(Nat.totient r : ℂ)) *
      (a₁ (d*r*m)/(m : ℂ)^(1-β j)) *
      (a₂ (d*r*n)*lemma83Xi β j n d r/(n : ℂ)) := by
  calc
    _ = (↑|ArithmeticFunction.moebius r| : ℂ) /
          ((d : ℂ)*(r : ℂ)*(Nat.totient r : ℂ)) *
        (a₁ (d*r*m)/(m : ℂ)^(1-β j)) * (a₂ (d*r*n)/(n : ℂ)) *
        (lemma83Lambda β (d*r*n) (1-β j) *
          ∑ ab ∈ n.divisorsAntidiagonal.filter (fun ab => ab.2.Coprime r),
            lemma83ModifiedKappa β ab.1 (d*r*ab.2) (1-β j) *
              (ArithmeticFunction.moebius ab.2 : ℂ) *
              (ab.2 : ℂ)^(1-β j)/(Nat.totient ab.2 : ℂ)) := by
      simp only [sum_filter,mul_sum]
      apply sum_congr rfl
      intro ab hab
      have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have hec : (ab.1 : ℂ)*(ab.2 : ℂ)=(n : ℂ) := by exact_mod_cast he
      unfold section721ReindexedTerm
      rw [he,hec]
      split_ifs <;> ring
    _ = _ := by
      rw [proposition71_xi_factor_extraction β j (Nat.ne_of_gt hn)
        (Nat.ne_of_gt hd) (Nat.ne_of_gt hr)]
      ring

/-- The n=d₁k₁ regrouping loses only coefficients proved to be zero. -/
theorem section721_convolution_collapse {D : ℕ} (c : ℝ) (j : Fin 3)
    {B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂) {d r m : ℕ}
    (hd : d ∈ lemma81PolynomialIndices D) (hr : r ∈ lemma81PolynomialIndices D) :
    (∑ a ∈ lemma81PolynomialIndices D, ∑ k ∈ lemma81PolynomialIndices D,
      section721ReindexedTerm (lemma83PaperBeta D c) j a₁ a₂ d r m a k) =
    (↑|ArithmeticFunction.moebius r| : ℂ) *
      lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j) /
        ((d : ℂ)*(r : ℂ)*(Nat.totient r : ℂ)) *
      (a₁ (d*r*m)/(m : ℂ)^(1-lemma83PaperBeta D c j)) *
      (∑ n ∈ lemma81PolynomialIndices D,
        a₂ (d*r*n)*lemma83Xi (lemma83PaperBeta D c) j n d r/(n : ℂ)) := by
  have hI := section721_indices_lower D
  rw [section721_product_reindex _ hI]
  · rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    exact section721_divisor_sum_collapse _ _ _ _ (hI.1 _ hd) (hI.1 _ hr) (hI.1 _ hn)
  · intro a ha k hk hn
    have h2 : a₂ (d*r*(a*k))≠0 := by
      intro hz; apply hn; simp [section721ReindexedTerm,hz]
    have hdr : 0<d*r := Nat.mul_pos (hI.1 _ hd) (hI.1 _ hr)
    have hak : 0<a*k := Nat.mul_pos (hI.1 _ ha) (hI.1 _ hk)
    exact section721_supported_le_mem h₂ hak (by nlinarith) h2

/-- The unconditional exact identity (7.21) for the original admissible
sequences, shifts, λ, κ̃, ξ and strict positive support. -/
theorem section721_star_eq_arithmetic_sum {D : ℕ} (c : ℝ) (j : Fin 3)
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂) :
    section721StarArithmeticSum D c j a₁ a₂ =
      proposition71ArithmeticSum D c j a₁ a₂ := by
  unfold section721StarArithmeticSum proposition71ArithmeticSum
  apply sum_congr rfl
  intro d hd
  calc
    _ = ∑ a ∈ lemma81PolynomialIndices D, ∑ k ∈ lemma81PolynomialIndices D,
        ∑ l ∈ (lemma81PolynomialIndices D).filter (fun l => l.Coprime k),
          section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d a k l := by
      simp only [section721StarTerm,mul_sum]
    _ = ∑ a ∈ lemma81PolynomialIndices D, ∑ r ∈ lemma81PolynomialIndices D,
        ∑ k ∈ lemma81PolynomialIndices D, ∑ m ∈ lemma81PolynomialIndices D,
          section721ReindexedTerm (lemma83PaperBeta D c) j a₁ a₂ d r m a k := by
      apply sum_congr rfl
      intro a ha
      exact section721_star_inner_reindex c j h₁ h₂ hd ha
    _ = ∑ r ∈ lemma81PolynomialIndices D, ∑ m ∈ lemma81PolynomialIndices D,
        ∑ a ∈ lemma81PolynomialIndices D, ∑ k ∈ lemma81PolynomialIndices D,
          section721ReindexedTerm (lemma83PaperBeta D c) j a₁ a₂ d r m a k := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      simp_rw [sum_comm (s := lemma81PolynomialIndices D) (t := lemma81PolynomialIndices D)
        (f := fun k m => section721ReindexedTerm (lemma83PaperBeta D c) j a₁ a₂ d r m _ k)]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      simp_rw [section721_convolution_collapse c j h₂ hd hr]
      rw [←sum_mul,←mul_sum]

end ZhangLS.Spec
