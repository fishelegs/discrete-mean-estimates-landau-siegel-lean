import FixedQuadratic.TimeEnvelope
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators
namespace FixedQuadratic
set_option maxHeartbeats 4000000

theorem formalEntry_truncatedLog_l1_coarse {m : ℕ} (T : Fin m → ℕ)
    (j k s h : ℕ) (b a : Fin m → ℕ) (hjk : j ≤ k) :
    multiCoefficientL1 (formalEntry (fun _ => 2*(j : ℂ)*Complex.I)
      (fun i => truncatedLog (T i)) s h b a) ≤
      2^s*(3/2)^h * 2^(∑ i, a i) * (2*k+2)^(∑ i, (a i-b i)) := by
  apply (formalEntry_truncatedLog_l1_le _ _ _ _ _ _ _ hjk).trans
  have hc : (∏ i, ((a i).choose (b i) : ℝ)) ≤ 2^(∑ i, a i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    · intro i hi; exact_mod_cast Nat.choose_le_two_pow (a i) (b i)
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (2 : ℝ)^s*(3/2)^h*(2*k+2)^(∑ i, (a i-b i)) by positivity)
  convert hh using 1 <;> ring

/-- The actual determinant polynomial's l1 envelope with the exact common
coordinate-degree rebate, not a sum of independent coarse coordinate bounds. -/
theorem formal_minor_truncatedLog_l1_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (T : Fin m → ℕ) (k : ℕ) (j s h : ι → ℕ)
    (b a : ι → Fin m → ℕ) (hj : ∀ r, j r ≤ k) :
    multiCoefficientL1 (Matrix.det (fun r c =>
      formalEntry (fun _ => 2*(j r : ℂ)*Complex.I) (fun i => truncatedLog (T i))
        (s r) (h c) (b r) (a c))) ≤
      (Fintype.card ι).factorial * 2^(∑ r, s r) * (3/2)^(∑ c, h c) *
        2^(∑ c, ∑ i, a c i) * (2*k+2)^(∑ i, ((∑ c, a c i)-(∑ r, b r i))) := by
  classical
  let A : Matrix ι ι (MvPolynomial (Fin m) ℂ) := fun r c =>
    formalEntry (fun _ => 2*(j r : ℂ)*Complex.I) (fun i => truncatedLog (T i))
      (s r) (h c) (b r) (a c)
  have hB : ∀ σ : Equiv.Perm ι, (∏ c, multiCoefficientL1 (A (σ c) c)) ≤
      2^(∑ r, s r) * (3/2)^(∑ c, h c) * 2^(∑ c, ∑ i, a c i) *
        (2*k+2)^(∑ i, ((∑ c, a c i)-(∑ r, b r i))) := by
    intro σ
    by_cases hab : ∀ c i, b (σ c) i ≤ a c i
    · have hd : (∑ c, ∑ i, (a c i-b (σ c) i)) =
          ∑ i, ((∑ c, a c i)-(∑ r, b r i)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => matched_sum_sub
          (fun c => a c i) (fun r => b r i) σ (fun c => hab c i))
      calc
        _ ≤ ∏ c, ((2 : ℝ)^(s (σ c))*(3/2)^(h c)*2^(∑ i, a c i)*
            (2*k+2)^(∑ i, (a c i-b (σ c) i))) := by
          apply Finset.prod_le_prod₀
          · intro c hc; exact multiCoefficientL1_nonneg _
          · intro c hc; exact formalEntry_truncatedLog_l1_coarse _ _ _ _ _ _ _ (hj _)
        _ = _ := by
          simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          rw [Equiv.sum_comp σ, hd]
    · push Not at hab
      obtain ⟨c, i, hi⟩ := hab
      have hz : A (σ c) c = 0 := formalEntry_zero_of_incompatible _ _ _ _ _ _
        (by intro hh; exact (not_le_of_gt hi) (hh i))
      rw [Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hz, multiCoefficientL1_zero])]
      positivity
  change multiCoefficientL1 (Matrix.det A) ≤ _
  have hh := determinant_l1_factorial_le A _ hB
  convert hh using 1
  ring

/-- Clearing contributes exactly one Q factor to the coefficient envelope;
the second Q is introduced later by the two-embedding norm lower bound. -/
theorem cleared_formal_minor_truncatedLog_l1_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] {m : ℕ} (T : Fin m → ℕ) (k : ℕ)
    (j s h : ι → ℕ) (b a : ι → Fin m → ℕ) (hj : ∀ r, j r ≤ k) :
    multiCoefficientL1 ((∏ i, (MvPolynomial.C (logDenominator (T i) : ℂ))^
      ((∑ c, a c i)-(∑ r, b r i))) * Matrix.det (fun r c =>
      formalEntry (fun _ => 2*(j r : ℂ)*Complex.I) (fun i => truncatedLog (T i))
        (s r) (h c) (b r) (a c))) ≤
      (∏ i, (logDenominator (T i) : ℝ)^((∑ c, a c i)-(∑ r, b r i))) *
      ((Fintype.card ι).factorial * 2^(∑ r, s r) * (3/2)^(∑ c, h c) *
        2^(∑ c, ∑ i, a c i) * (2*k+2)^(∑ i, ((∑ c, a c i)-(∑ r, b r i)))) := by
  apply (multiCoefficientL1_mul_le _ _).trans
  have he : (∏ i, (MvPolynomial.C (logDenominator (T i) : ℂ))^
      ((∑ c, a c i)-(∑ r, b r i)) : MvPolynomial (Fin m) ℂ) =
      MvPolynomial.C (∏ i, (logDenominator (T i) : ℂ)^((∑ c, a c i)-(∑ r, b r i))) := by
    simp
  rw [he, multiCoefficientL1_C]
  simp only [norm_prod, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (formal_minor_truncatedLog_l1_le _ _ _ _ _ _ _ hj)
    (by positivity)

end FixedQuadratic
