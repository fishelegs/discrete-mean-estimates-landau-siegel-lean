import ZhangLS.Spec.Lemma23CoefficientBounds

/-!
# Majorants for the actual twentieth-power coefficients

Zhang's Lemma 3.3 uses the pointwise estimates
`|ν₂₀(n)|, |υ₂₀(n)| ≤ τ₄₀(n)`.  This file proves the corresponding finite-cutoff
majorant statement directly from the actual arithmetic coefficients.  The majorant is the
twentieth Dirichlet convolution of the ordinary divisor-counting sequence; identifying it with
the conventional `τ₄₀` and estimating its mean square are subsequent steps.
-/

namespace ZhangLS.Spec

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/-- The real-valued twentieth convolution of the divisor-counting majorant, with each factor
restricted to the same cutoff as the actual Section 4 polynomial. -/
noncomputable def lemma23Nu20DivisorMajorant (X : ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ Fintype.piFinset (fun _ : Fin 20 => Finset.Icc 1 X)
      with (∏ i : Fin 20, p i) = n,
    ∏ i : Fin 20, ((Nat.divisors (p i)).card : ℝ)

/-- The ordinary generalized divisor coefficient `τ₄₀(n) = τ₂^{*20}(n)`, written as a sum over
20 ordered factors, with each `τ₂(pᵢ)` represented by the divisor count of `pᵢ`. -/
noncomputable def lemma23Tau40 (n : ℕ) : ℝ :=
  ∑ p ∈ Fintype.piFinset (fun _ : Fin 20 => Finset.Icc 1 n)
      with (∏ i : Fin 20, p i) = n,
    ∏ i : Fin 20, ((Nat.divisors (p i)).card : ℝ)

/-- A finite Dirichlet-convolution coefficient preserves any pointwise divisor-count majorant.
This is the absolute-value estimate needed before applying a character-family mean-value bound. -/
theorem lemma23TupleConvolutionCoefficient_norm_le_divisor_majorant
    {X m : ℕ} (c : ℕ → ℂ)
    (hc : ∀ n, ‖c n‖ ≤ (Nat.divisors n).card)
    (n : ℕ) :
    ‖lemma23TupleConvolutionCoefficient X m c n‖ ≤
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
          with (∏ i : Fin m, p i) = n,
        ∏ i : Fin m, ((Nat.divisors (p i)).card : ℝ) := by
  classical
  unfold lemma23TupleConvolutionCoefficient
  calc
    ‖∑ p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
        with (∏ i : Fin m, p i) = n,
        ∏ i : Fin m, c (p i)‖ ≤
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
          with (∏ i : Fin m, p i) = n,
        ‖∏ i : Fin m, c (p i)‖ := norm_sum_le _ _
    _ ≤
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
          with (∏ i : Fin m, p i) = n,
        ∏ i : Fin m, ((Nat.divisors (p i)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          calc
            ‖∏ i : Fin m, c (p i)‖ = ∏ i : Fin m, ‖c (p i)‖ := by
              rw [Complex.norm_prod]
            _ ≤ ∏ i : Fin m, ((Nat.divisors (p i)).card : ℝ) := by
              apply Finset.prod_le_prod
              · intro i hi
                positivity
              · intro i hi
                exact_mod_cast hc (p i)

/-- The actual coefficients of `F(s,ψ)^20` satisfy the divisor-convolution majorant. -/
theorem lemma23Nu20Coefficient_norm_le_divisor_majorant
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23Nu20Coefficient χ n‖ ≤ lemma23Nu20DivisorMajorant (D ^ 4) n := by
  simpa [lemma23Nu20DivisorMajorant, lemma23Nu20Coefficient] using
    (lemma23TupleConvolutionCoefficient_norm_le_divisor_majorant
      (X := D ^ 4) (m := 20) (c := lemma23NuArithmeticFunction χ)
      (fun k => lemma23NuArithmeticFunction_norm_le_card_divisors χ k) n)

/-- Removing the per-factor cutoff only enlarges the nonnegative divisor convolution. -/
theorem lemma23Nu20DivisorMajorant_le_tau40 (X n : ℕ) :
    lemma23Nu20DivisorMajorant X n ≤ lemma23Tau40 n := by
  classical
  let S : Finset (Fin 20 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 20 => Finset.Icc 1 X)).filter
      (fun p => (∏ i : Fin 20, p i) = n)
  let T : Finset (Fin 20 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 20 => Finset.Icc 1 n)).filter
      (fun p => (∏ i : Fin 20, p i) = n)
  have hST : S ⊆ T := by
    intro p hp
    simp only [S, T, Finset.mem_filter] at hp ⊢
    refine ⟨Fintype.mem_piFinset.mpr ?_, hp.2⟩
    intro i
    have hcoords := Fintype.mem_piFinset.mp hp.1
    have hpiX : p i ∈ Finset.Icc 1 X := hcoords i
    have hpos : 0 < n := by
      have hprod : 1 ≤ ∏ i : Fin 20, p i :=
        Finset.one_le_prod' (fun j hj => (Finset.mem_Icc.mp (hcoords j)).1)
      rw [hp.2] at hprod
      omega
    have hdiv : p i ∣ n := by
      rw [← hp.2]
      exact Finset.dvd_prod_of_mem (fun j : Fin 20 => p j) (Finset.mem_univ i)
    have hle : p i ≤ n := Nat.le_of_dvd hpos hdiv
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpiX).1, hle⟩
  change (∑ p ∈ S, ∏ i : Fin 20, ((Nat.divisors (p i)).card : ℝ)) ≤
    ∑ p ∈ T, ∏ i : Fin 20, ((Nat.divisors (p i)).card : ℝ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (by
    intro p hp hpT
    positivity)

/-- Zhang's pointwise coefficient estimate for the actual `F^20`: the cutoff convolution is
bounded by the standard generalized divisor function `τ₄₀`. -/
theorem lemma23Nu20Coefficient_norm_le_tau40
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23Nu20Coefficient χ n‖ ≤ lemma23Tau40 n := by
  exact (lemma23Nu20Coefficient_norm_le_divisor_majorant χ n).trans
    (lemma23Nu20DivisorMajorant_le_tau40 (D ^ 4) n)

/-- The inverse coefficient `υ = μ * (χ μ)` has the same elementary divisor-count bound as
`ν`.  The Möbius factors have norm at most one, so each summand in its antidiagonal formula is
bounded by one. -/
theorem lemma23UpsilonArithmeticFunction_norm_le_card_divisors
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23UpsilonArithmeticFunction χ n‖ ≤ (Nat.divisors n).card := by
  classical
  have hsum : lemma23UpsilonArithmeticFunction χ n =
      ∑ q ∈ n.divisorsAntidiagonal,
        (μ q.1 : ℂ) * (χ.chi q.2 * (μ q.2 : ℂ)) := by
    rw [lemma23UpsilonArithmeticFunction, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq
    simp [lemma23CharacterMoebiusArithmeticFunction, toArithmeticFunction, hq2]
  rw [hsum]
  calc
    ‖∑ q ∈ n.divisorsAntidiagonal,
        (μ q.1 : ℂ) * (χ.chi q.2 * (μ q.2 : ℂ))‖ ≤
      ∑ q ∈ n.divisorsAntidiagonal,
        ‖(μ q.1 : ℂ) * (χ.chi q.2 * (μ q.2 : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hμ₁ : ‖(μ q.1 : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or q.1 with h | h | h <;>
          rw [h] <;> norm_num
      have hμ₂ : ‖(μ q.2 : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or q.2 with h | h | h <;>
          rw [h] <;> norm_num
      have hχ : ‖χ.chi q.2‖ ≤ 1 := χ.chi.norm_le_one (q.2 : ZMod D)
      rw [norm_mul, norm_mul]
      calc
        ‖(μ q.1 : ℂ)‖ * (‖χ.chi q.2‖ * ‖(μ q.2 : ℂ)‖) ≤ 1 * (1 * 1) := by
          gcongr
        _ = 1 := by norm_num
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
    _ = (Nat.divisors n).card := by
      exact_mod_cast (by
        have hcard : (Nat.divisors n).card = n.divisorsAntidiagonal.card := by
          rw [← Nat.map_div_right_divisors]
          simp
        exact hcard.symm)

theorem lemma23Upsilon20Coefficient_norm_le_divisor_majorant
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23Upsilon20Coefficient χ n‖ ≤ lemma23Nu20DivisorMajorant (D ^ 4) n := by
  simpa [lemma23Upsilon20Coefficient, lemma23Nu20DivisorMajorant] using
    (lemma23TupleConvolutionCoefficient_norm_le_divisor_majorant
      (X := D ^ 4) (m := 20) (c := lemma23UpsilonArithmeticFunction χ)
      (fun k => lemma23UpsilonArithmeticFunction_norm_le_card_divisors χ k) n)

/-- If the actual one-factor inverse coefficient bound holds, the actual `G^20` coefficients
also satisfy Zhang's `τ₄₀` majorant. -/
theorem lemma23Upsilon20Coefficient_norm_le_tau40
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23Upsilon20Coefficient χ n‖ ≤ lemma23Tau40 n := by
  exact (lemma23Upsilon20Coefficient_norm_le_divisor_majorant χ n).trans
    (lemma23Nu20DivisorMajorant_le_tau40 (D ^ 4) n)

end ZhangLS.Spec
