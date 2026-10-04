import ZhangLS.Spec.ActualGramArithmeticAttachment

/-! Regroup the literal P7 positive strict-cutoff box into actual divisor
antidiagonals. The profile-product support is explicit, not replaced by an
assumption about a Gram or an arithmetic asymptotic. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma actualGram_original_box_fiber (D n : ℕ) (hn : n ∈ lemma81PolynomialIndices D) :
    ((lemma81PolynomialIndices D) ×ˢ (lemma81PolynomialIndices D)).filter
      (fun dr => dr.1*dr.2 = n) = n.divisorsAntidiagonal := by
  have hn' := (proposition71_mem_indices D n).mp hn
  ext dr
  simp only [mem_filter, mem_product, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨hd, hr⟩, he⟩
    exact ⟨he, hn'.1.ne'⟩
  · rintro ⟨he, hn0⟩
    have hd0 : 0 < dr.1 := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
    have hr0 : 0 < dr.2 := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
    have hdle : dr.1 ≤ n := he ▸ Nat.le_mul_of_pos_right dr.1 hr0
    have hrle : dr.2 ≤ n := he ▸ Nat.le_mul_of_pos_left dr.2 hd0
    refine ⟨⟨(proposition71_mem_indices D dr.1).mpr ⟨hd0, ?_⟩,
      (proposition71_mem_indices D dr.2).mpr ⟨hr0, ?_⟩⟩, he⟩
    · exact (by exact_mod_cast hdle : (dr.1 : ℝ) ≤ n).trans_lt hn'.2
    · exact (by exact_mod_cast hrle : (dr.2 : ℝ) ≤ n).trans_lt hn'.2

/-- The complete literal P7-box main term, with the genuine Pi and the exact
strict-cutoff support, collapses to the one-variable totient main sum. -/
theorem actualGram_P7_box_main_attachment {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (K : ℕ → ℂ)
    (hK : ∀ n, n ∉ lemma81PolynomialIndices D → K n = 0) :
    (∑ d ∈ lemma81PolynomialIndices D, ∑ r ∈ lemma81PolynomialIndices D,
      lemma84Section8Weight χ c j d r * lemma83Pi χ d r * K (d*r)) =
    ∑ n ∈ lemma81PolynomialIndices D, (‖χ.evalNat n‖ : ℂ) *
      lemma83Lambda (lemma83PaperBeta D c) n (1 - lemma83PaperBeta D c j) /
        (Nat.totient n : ℂ) * K n := by
  let S := lemma81PolynomialIndices D
  let F : ℕ×ℕ → ℂ := fun dr => lemma84Section8Weight χ c j dr.1 dr.2 *
    lemma83Pi χ dr.1 dr.2 * K (dr.1*dr.2)
  have hf := sum_fiberwise_eq_sum_filter (S×ˢS) S (fun dr : ℕ×ℕ => dr.1*dr.2) F
  have hr : (∑ dr ∈ (S×ˢS).filter (fun dr => dr.1*dr.2 ∈ S), F dr) =
      ∑ dr ∈ S×ˢS, F dr := by
    rw [sum_filter]
    apply sum_congr rfl
    intro dr hdr
    by_cases hm : dr.1*dr.2 ∈ S
    · simp [hm]
    · simp [hm, F, hK _ hm]
  rw [hr] at hf
  rw [← sum_product']
  change (∑ dr ∈ S×ˢS, F dr) = _
  rw [← hf]
  apply sum_congr rfl
  intro n hn
  change (∑ dr ∈ ((lemma81PolynomialIndices D)×ˢ(lemma81PolynomialIndices D)).filter
    (fun dr : ℕ×ℕ => dr.1*dr.2=n), F dr) = _
  rw [actualGram_original_box_fiber D n hn]
  have he : (∑ dr ∈ n.divisorsAntidiagonal, F dr) =
      ∑ dr ∈ n.divisorsAntidiagonal,
        lemma84Section8Weight χ c j dr.1 dr.2 * lemma83Pi χ dr.1 dr.2 * K n := by
    apply sum_congr rfl
    intro dr hdr
    simp only [F, (Nat.mem_divisorsAntidiagonal.mp hdr).1]
  rw [he, ← sum_mul, actualGram_weight_pi_collapse χ c j n
    ((proposition71_mem_indices D n).mp hn).1.ne']

end ZhangLS.Spec
