import ZhangLS.Spec.Lemma23ArithmeticCoefficients
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary coefficient and polynomial norm bounds for Lemma 2.3

The actual coefficient `ν(n) = ∑_{d ∣ n} χ(d)` has norm at most the number of divisors.  This
gives a concrete finite real majorant for Zhang's Section 4 polynomial `F`; estimating that
majorant by a power of `log D` is a separate analytic-number-theory step.
-/

namespace ZhangLS.Spec

open scoped BigOperators

/-- The norm of Zhang's actual coefficient `ν(n)` is at most the divisor count. -/
theorem lemma23NuArithmeticFunction_norm_le_card_divisors
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖ ≤ (Nat.divisors n).card := by
  rw [lemma23NuArithmeticFunction_apply]
  calc
    ‖∑ d ∈ Nat.divisors n, χ.chi d‖ ≤
        ∑ d ∈ Nat.divisors n, ‖χ.chi d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Nat.divisors n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact χ.chi.norm_le_one (d : ZMod D)
    _ = (Nat.divisors n).card := by simp

/-- The actual Section 4 polynomial is bounded by the explicit divisor-weighted sum whenever
the twist coefficients have norm at most one on the truncation range. -/
theorem lemma23ActualSectionFourF_norm_le_divisor_majorant
    {D : ℕ} (χ : RealPrimitiveCharacter D) (ψ : ℕ → ℂ) (s : ℂ)
    (hψ : ∀ n ∈ Finset.Icc 1 (D ^ 4), ‖ψ n‖ ≤ 1) :
    ‖lemma23ActualSectionFourF χ ψ s‖ ≤
      ∑ n ∈ Finset.Icc 1 (D ^ 4),
        ((Nat.divisors n).card : ℝ) * Real.exp (-s.re * Real.log (n : ℝ)) := by
  rw [lemma23ActualSectionFourF, lemma23SectionFourF,
    lemma23FiniteDirichletPolynomial]
  calc
    ‖∑ n ∈ Finset.Icc 1 (D ^ 4),
        lemma23NuArithmeticFunction χ n * ψ n *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc 1 (D ^ 4),
          ‖lemma23NuArithmeticFunction χ n * ψ n *
            Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (D ^ 4),
          ((Nat.divisors n).card : ℝ) * Real.exp (-s.re * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hν := lemma23NuArithmeticFunction_norm_le_card_divisors χ n
      have hψn := hψ n hn
      have hexp :
          ‖Complex.exp (-s * (Real.log (n : ℝ) : ℂ))‖ =
            Real.exp (-s.re * Real.log (n : ℝ)) := by
        rw [Complex.norm_exp, Complex.mul_re]
        simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
      rw [norm_mul, norm_mul, hexp]
      have hprod :
          ‖lemma23NuArithmeticFunction χ n‖ * ‖ψ n‖ ≤ (Nat.divisors n).card := by
        calc
          ‖lemma23NuArithmeticFunction χ n‖ * ‖ψ n‖ ≤
              (Nat.divisors n).card * 1 := by gcongr
          _ = (Nat.divisors n).card := by ring
      exact mul_le_mul_of_nonneg_right hprod (le_of_lt (Real.exp_pos _))

/-- The divisor-weighted harmonic sum is bounded by the square of the harmonic sum.

The proof expands each divisor count as the cardinality of its divisor antidiagonal, then
reindexes all pairs `(a,b)` with `a*b ≤ X` into the rectangle `[1,X] × [1,X]`. -/
theorem lemma23_divisor_weighted_sum_le_harmonic_sq (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X,
      ((Nat.divisors n).card : ℝ) * (n : ℝ)⁻¹ ≤ (harmonic X : ℝ) ^ 2 := by
  classical
  let S : Finset (Σ n : ℕ, ℕ × ℕ) :=
    (Finset.Icc 1 X).sigma fun n => n.divisorsAntidiagonal
  let R : Finset (ℕ × ℕ) := Finset.Icc 1 X ×ˢ Finset.Icc 1 X
  let pairOf (x : Σ n : ℕ, ℕ × ℕ) : ℕ × ℕ := x.2
  let weight (p : ℕ × ℕ) : ℝ := (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹
  have hcard (n : ℕ) :
      (n.divisors).card = n.divisorsAntidiagonal.card := by
    rw [← Nat.map_div_right_divisors]
    simp
  have hsum_expand :
      (∑ n ∈ Finset.Icc 1 X,
        ((Nat.divisors n).card : ℝ) * (n : ℝ)⁻¹) =
      ∑ x ∈ S, (x.1 : ℝ)⁻¹ := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 X,
            ∑ q ∈ n.divisorsAntidiagonal, (n : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro n hn
          have hc : ((n.divisors).card : ℝ) =
              (n.divisorsAntidiagonal.card : ℝ) :=
            congrArg (fun k : ℕ => (k : ℝ)) (hcard n)
          rw [hc]
          simp [Finset.sum_const]
      _ = ∑ x ∈ S, (x.1 : ℝ)⁻¹ := by
          simpa [S] using
            (Finset.sum_sigma (Finset.Icc 1 X)
              (fun n => n.divisorsAntidiagonal)
              (fun x : Σ n, ℕ × ℕ => (x.1 : ℝ)⁻¹)).symm
  have hpair_inj : Set.InjOn pairOf S := by
    intro x hx y hy hxy
    rcases x with ⟨nx, px⟩
    rcases y with ⟨ny, py⟩
    simp only [pairOf] at hxy
    have hpx : px ∈ nx.divisorsAntidiagonal := (Finset.mem_sigma.mp hx).2
    have hpy : py ∈ ny.divisorsAntidiagonal := (Finset.mem_sigma.mp hy).2
    have hnx : px.1 * px.2 = nx := (Nat.mem_divisorsAntidiagonal.mp hpx).1
    have hny : py.1 * py.2 = ny := (Nat.mem_divisorsAntidiagonal.mp hpy).1
    have hfst : nx = ny := by rw [← hnx, ← hny, hxy]
    exact Sigma.ext hfst (heq_of_eq hxy)
  have himage_subset : S.image pairOf ⊆ R := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
    let n := x.1
    let q := x.2
    have hmem := Finset.mem_sigma.mp hx
    have hn : n ∈ Finset.Icc 1 X := hmem.1
    have hq : q ∈ n.divisorsAntidiagonal := hmem.2
    have hprod : q.1 * q.2 = n := (Nat.mem_divisorsAntidiagonal.mp hq).1
    have hnle : n ≤ X := (Finset.mem_Icc.mp hn).2
    have hnpos : 0 < n := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hn).1
    have hq1 : 0 < q.1 := Nat.pos_of_ne_zero (by
      intro hzero
      rw [hzero, zero_mul] at hprod
      omega)
    have hq2 : 0 < q.2 := Nat.pos_of_ne_zero (by
      intro hzero
      rw [hzero, mul_zero] at hprod
      omega)
    have hq1le : q.1 ≤ X := (Nat.le_mul_of_pos_right q.1 hq2).trans (hprod ▸ hnle)
    have hq2le : q.2 ≤ X := (Nat.le_mul_of_pos_left q.2 hq1).trans (hprod ▸ hnle)
    simp only [R, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq1), hq1le⟩,
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq2), hq2le⟩⟩
  have hsum_reindex :
      (∑ x ∈ S, (x.1 : ℝ)⁻¹) = ∑ p ∈ S.image pairOf, weight p := by
    rw [Finset.sum_image hpair_inj]
    apply Finset.sum_congr rfl
    intro x hx
    let n := x.1
    let q := x.2
    have hmem := Finset.mem_sigma.mp hx
    have hn : n ∈ Finset.Icc 1 X := hmem.1
    have hq : q ∈ n.divisorsAntidiagonal := hmem.2
    have hprod : q.1 * q.2 = n := (Nat.mem_divisorsAntidiagonal.mp hq).1
    simp only [pairOf, weight]
    change (n : ℝ)⁻¹ = (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹
    rw [← hprod, Nat.cast_mul, mul_inv]
  have hsum_rect :
      (∑ p ∈ S.image pairOf, weight p) ≤ ∑ p ∈ R, weight p :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset (by
      intro p hp hnot
      simp only [weight]
      positivity)
  have hrect :
      (∑ p ∈ R, weight p) = (harmonic X : ℝ) ^ 2 := by
    change (∑ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 X,
      (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) = _
    rw [Finset.sum_product' (Finset.Icc 1 X) (Finset.Icc 1 X)
      (fun a b : ℕ => (a : ℝ)⁻¹ * (b : ℝ)⁻¹)]
    have hh : (harmonic X : ℝ) =
        ∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [← Finset.sum_mul_sum, ← hh]
    rw [pow_two]
  calc
    _ = ∑ x ∈ S, (x.1 : ℝ)⁻¹ := hsum_expand
    _ = ∑ p ∈ S.image pairOf, weight p := hsum_reindex
    _ ≤ ∑ p ∈ R, weight p := hsum_rect
    _ = (harmonic X : ℝ) ^ 2 := hrect

/-- On `n ≤ X`, a Dirichlet weight with real part at least `1 - δ` is bounded by
`exp (δ log X) / n`. -/
theorem lemma23_exp_dirichlet_weight_le
    {X n : ℕ} {σ δ : ℝ} (hX : 0 < X)
    (hn : n ∈ Finset.Icc 1 X) (hδ : 0 ≤ δ) (hσ : 1 - δ ≤ σ) :
    Real.exp (-σ * Real.log (n : ℝ)) ≤
      Real.exp (δ * Real.log (X : ℝ)) * (n : ℝ)⁻¹ := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide) hn1)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlog_le : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hnpos (by exact_mod_cast hnX)
  have hexp_arg : -σ * Real.log (n : ℝ) ≤
      δ * Real.log (X : ℝ) - Real.log (n : ℝ) := by
    have hmul : (1 - σ) * Real.log (n : ℝ) ≤ δ * Real.log (X : ℝ) := by
      calc
        (1 - σ) * Real.log (n : ℝ) ≤ δ * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlogn_nonneg
        _ ≤ δ * Real.log (X : ℝ) := mul_le_mul_of_nonneg_left hlog_le hδ
    calc
      -σ * Real.log (n : ℝ) =
          (1 - σ) * Real.log (n : ℝ) - Real.log (n : ℝ) := by ring
      _ ≤ _ := sub_le_sub_right hmul _
  calc
    Real.exp (-σ * Real.log (n : ℝ)) ≤
        Real.exp (δ * Real.log (X : ℝ) - Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr hexp_arg
    _ = Real.exp (δ * Real.log (X : ℝ)) * (n : ℝ)⁻¹ := by
      rw [Real.exp_sub, Real.exp_log hnpos]
      simp [div_eq_mul_inv]

/-- The divisor-majorant for Zhang's finite polynomial has a uniform logarithmic bound to the
right of `Re(s) = 1 - δ`.  The remaining comparison with the paper's power `(log D)^88` is an
explicit elementary specialization in `D` and `δ`. -/
theorem lemma23_divisor_exponential_sum_le_harmonic_sq
    {X : ℕ} {σ δ : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hσ : 1 - δ ≤ σ) :
    ∑ n ∈ Finset.Icc 1 X,
      ((Nat.divisors n).card : ℝ) * Real.exp (-σ * Real.log (n : ℝ)) ≤
        Real.exp (δ * Real.log (X : ℝ)) * (harmonic X : ℝ) ^ 2 := by
  let C : ℝ := Real.exp (δ * Real.log (X : ℝ))
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
          C * ((Nat.divisors n).card : ℝ) * (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hweight := lemma23_exp_dirichlet_weight_le hX hn hδ hσ
        have hd : (0 : ℝ) ≤ (Nat.divisors n).card := Nat.cast_nonneg _
        calc
          ((Nat.divisors n).card : ℝ) * Real.exp (-σ * Real.log (n : ℝ)) ≤
              ((Nat.divisors n).card : ℝ) * (C * (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (by simpa [C] using hweight) hd
          _ = C * ((Nat.divisors n).card : ℝ) * (n : ℝ)⁻¹ := by ring
    _ = ∑ n ∈ Finset.Icc 1 X,
          C * (((Nat.divisors n).card : ℝ) * (n : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
    _ = C * (∑ n ∈ Finset.Icc 1 X,
          ((Nat.divisors n).card : ℝ) * (n : ℝ)⁻¹) := by
        rw [← Finset.mul_sum]
    _ ≤ C * (harmonic X : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
          (lemma23_divisor_weighted_sum_le_harmonic_sq X)
        exact le_of_lt (Real.exp_pos _)
    _ = _ := by rfl

/-- A concrete upper bound for Zhang's actual Section 4 polynomial, assuming the twist is
bounded by one and `Re(s) ≥ 1 - δ` on the truncation range. -/
theorem lemma23ActualSectionFourF_norm_le_exp_harmonic_sq
    {D : ℕ} (χ : RealPrimitiveCharacter D) (ψ : ℕ → ℂ) (s : ℂ) (δ : ℝ)
    (hD : 0 < D)
    (hψ : ∀ n ∈ Finset.Icc 1 (D ^ 4), ‖ψ n‖ ≤ 1)
    (hδ : 0 ≤ δ) (hs : 1 - δ ≤ s.re) :
    ‖lemma23ActualSectionFourF χ ψ s‖ ≤
      Real.exp (δ * Real.log ((D ^ 4 : ℕ) : ℝ)) *
        (harmonic (D ^ 4) : ℝ) ^ 2 := by
  calc
    ‖lemma23ActualSectionFourF χ ψ s‖ ≤
        ∑ n ∈ Finset.Icc 1 (D ^ 4),
          ((Nat.divisors n).card : ℝ) *
            Real.exp (-s.re * Real.log (n : ℝ)) :=
      lemma23ActualSectionFourF_norm_le_divisor_majorant χ ψ s hψ
    _ ≤ Real.exp (δ * Real.log ((D ^ 4 : ℕ) : ℝ)) *
          (harmonic (D ^ 4) : ℝ) ^ 2 :=
      lemma23_divisor_exponential_sum_le_harmonic_sq
        (Nat.pow_pos hD) hδ hs

/-- Abel summation turns an endpoint bound and a bound for the weighted partial-sum integral into
a bound for a finite complex Dirichlet sum.  This is the abstract finite-sum step used in
Zhang's proof of Lemma 4.1; the paper-specific coefficient and weight estimates remain separate. -/
theorem lemma23_abel_partial_sum_norm_bound
    {N : ℕ} {c : ℕ → ℂ} {f : ℝ → ℂ} {A B C : ℝ}
    (hc0 : c 0 = 0)
    (hfDiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t)
    (hfInt : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N))
    (hA : ‖f N‖ ≤ A)
    (hB : ‖∑ k ∈ Finset.Icc 0 N, c k‖ ≤ B)
    (hC : ‖∫ t in Set.Ioc (1 : ℝ) N,
        deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C) :
    ‖∑ k ∈ Finset.Icc 0 N, f k * c k‖ ≤ A * B + C := by
  have habel := sum_mul_eq_sub_integral_mul₀' (c := c) hc0 N hfDiff hfInt
  rw [habel]
  have hEndpoint :
      ‖f N‖ * ‖∑ k ∈ Finset.Icc 0 N, c k‖ ≤ A * B :=
    mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg (f N)).trans hA)
  calc
    ‖f N * (∑ k ∈ Finset.Icc 0 N, c k) -
        ∫ t in Set.Ioc (1 : ℝ) N,
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤
        ‖f N * (∑ k ∈ Finset.Icc 0 N, c k)‖ +
          ‖∫ t in Set.Ioc (1 : ℝ) N,
            deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ := norm_sub_le _ _
    _ = ‖f N‖ * ‖∑ k ∈ Finset.Icc 0 N, c k‖ +
          ‖∫ t in Set.Ioc (1 : ℝ) N,
            deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ := by rw [norm_mul]
    _ ≤ A * B + C := add_le_add hEndpoint hC

/-- A derivative bound of the form `‖f' t‖ ≤ K / t` turns the weighted
partial-sum integral into the error term in Abel summation.  This is the
quantitative interface needed when the Dirichlet weight is a real power. -/
theorem lemma23_abel_partial_sum_norm_bound_of_derivative
    {N : ℕ} {c : ℕ → ℂ} {f : ℝ → ℂ} {A B K M : ℝ}
    (hc0 : c 0 = 0)
    (hfDiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t)
    (hfInt : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N))
    (hA : ‖f N‖ ≤ A)
    (hB : ‖∑ k ∈ Finset.Icc 0 N, c k‖ ≤ B)
    (hK : 0 ≤ K)
    (hder : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖deriv f t‖ ≤ K / t)
    (hPartialIntegrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t)
      (Set.Ioc (1 : ℝ) N))
    (hPartialIntegral : ∫ t in Set.Ioc (1 : ℝ) N,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t ≤ M) :
    ‖∑ k ∈ Finset.Icc 0 N, f k * c k‖ ≤ A * B + K * M := by
  let partialSum : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hProdIntegrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv f t * partialSum t) (Set.Ioc (1 : ℝ) N) := by
    have hIcc := integrableOn_mul_sum_Icc (m := 0) c
      (by norm_num : (0 : ℝ) ≤ 1) hfInt
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hMajorantIntegrable : MeasureTheory.IntegrableOn
      (fun t : ℝ => K * (‖partialSum t‖ / t)) (Set.Ioc (1 : ℝ) N) := by
    exact hPartialIntegrable.const_mul K
  have hIntegralComparison :
      (∫ t in Set.Ioc (1 : ℝ) N, ‖deriv f t * partialSum t‖) ≤
        ∫ t in Set.Ioc (1 : ℝ) N, K * (‖partialSum t‖ / t) := by
    apply MeasureTheory.integral_mono_ae hProdIntegrable.norm hMajorantIntegrable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := by linarith [ht.1]
    rw [norm_mul]
    calc
      ‖deriv f t‖ * ‖partialSum t‖ ≤ (K / t) * ‖partialSum t‖ :=
        mul_le_mul_of_nonneg_right (hder t ht) (norm_nonneg _)
      _ = K * (‖partialSum t‖ / t) := by
        field_simp [ne_of_gt htpos]
  have hIntegralMajorant :
      (∫ t in Set.Ioc (1 : ℝ) N, K * (‖partialSum t‖ / t)) ≤ K * M := by
    calc
      (∫ t in Set.Ioc (1 : ℝ) N, K * (‖partialSum t‖ / t)) =
          K * (∫ t in Set.Ioc (1 : ℝ) N, ‖partialSum t‖ / t) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ K * M := mul_le_mul_of_nonneg_left hPartialIntegral hK
  have hC : ‖∫ t in Set.Ioc (1 : ℝ) N,
      deriv f t * partialSum t‖ ≤ K * M := by
    calc
      ‖∫ t in Set.Ioc (1 : ℝ) N, deriv f t * partialSum t‖ ≤
          ∫ t in Set.Ioc (1 : ℝ) N, ‖deriv f t * partialSum t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) N, K * (‖partialSum t‖ / t) :=
        hIntegralComparison
      _ ≤ K * M := hIntegralMajorant
  apply lemma23_abel_partial_sum_norm_bound hc0 hfDiff hfInt hA hB hC

/-- The smooth Abel weight `t^z`, written in a form that is defined for every real `t`. -/
noncomputable def lemma23AbelPowerWeight (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (z * (Real.log t : ℂ))

/-- On `t ≥ 1`, the norm of the power weight is controlled solely by the real
part of its exponent. -/
theorem lemma23AbelPowerWeight_norm_le_exp
    {z : ℂ} {t a : ℝ} (ht : 1 ≤ t) (hz : z.re ≤ a) :
    ‖lemma23AbelPowerWeight z t‖ ≤ Real.exp (a * Real.log t) := by
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hre : (z * (Real.log t : ℂ)).re = z.re * Real.log t := by
    simp [Complex.mul_re]
  rw [lemma23AbelPowerWeight, Complex.norm_exp, hre]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hlogt)

/-- The strip-width estimate used for the power kernel in Zhang's Lemma 4.1.
If `log t ≤ 80 L` and `Re z ≤ log L / (100 L)`, then `|t^z| ≤ L`. -/
theorem lemma23AbelPowerWeight_norm_le_of_strip_exponent
    {z : ℂ} {t L : ℝ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (hlogt : Real.log t ≤ 80 * L)
    (hz : z.re ≤ Real.log L / (100 * L)) :
    ‖lemma23AbelPowerWeight z t‖ ≤ L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hcoef : 0 ≤ Real.log L / (100 * L) := by positivity
  have hpower : (Real.log L / (100 * L)) * Real.log t ≤ Real.log L := by
    calc
      (Real.log L / (100 * L)) * Real.log t ≤
          (Real.log L / (100 * L)) * (80 * L) :=
        mul_le_mul_of_nonneg_left hlogt hcoef
      _ = (4 / 5) * Real.log L := by field_simp; ring
      _ ≤ Real.log L := by nlinarith
  calc
    ‖lemma23AbelPowerWeight z t‖ ≤ Real.exp
        (Real.log L / (100 * L) * Real.log t) :=
      lemma23AbelPowerWeight_norm_le_exp ht hz
    _ ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr hpower
    _ = L := Real.exp_log hLpos

/-- Derivative of the power weight on the positive real axis. -/
theorem lemma23AbelPowerWeight_deriv (z : ℂ) {t : ℝ} (ht : t ≠ 0) :
    deriv (lemma23AbelPowerWeight z) t =
      z * Complex.exp (z * (Real.log t : ℂ)) * (↑(t⁻¹) : ℂ) := by
  have hlog : HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) (↑(t⁻¹) : ℂ) t :=
    (Real.hasDerivAt_log ht).ofReal_comp
  have harg : HasDerivAt (fun x : ℝ => z * (Real.log x : ℂ))
      (z * (↑(t⁻¹) : ℂ)) t := hlog.const_mul z
  have hexp := harg.cexp
  change deriv (fun x : ℝ => Complex.exp (z * (Real.log x : ℂ))) t = _
  calc
    deriv (fun x : ℝ => Complex.exp (z * (Real.log x : ℂ))) t =
        Complex.exp (z * (Real.log t : ℂ)) * (z * (↑(t⁻¹) : ℂ)) := hexp.deriv
    _ = z * Complex.exp (z * (Real.log t : ℂ)) * (↑(t⁻¹) : ℂ) := by ring

/-- A pointwise bound for `‖z‖‖t^z‖` gives the `K/t` derivative bound needed by Abel summation. -/
theorem lemma23AbelPowerWeight_norm_deriv_le
    {z : ℂ} {K t : ℝ} (ht : 0 < t)
    (hweight : ‖z‖ * ‖lemma23AbelPowerWeight z t‖ ≤ K) :
    ‖deriv (lemma23AbelPowerWeight z) t‖ ≤ K / t := by
  rw [lemma23AbelPowerWeight_deriv z (ne_of_gt ht), norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht.le)]
  calc
    ‖z‖ * ‖lemma23AbelPowerWeight z t‖ * t⁻¹ ≤ K * t⁻¹ :=
      mul_le_mul_of_nonneg_right hweight (inv_nonneg.mpr ht.le)
    _ = K / t := by rw [div_eq_mul_inv]

/-- The weighted norm of a finite partial sum is integrable on a bounded interval away from zero.
The partial sum is a measurable step function with only finitely many possible values there. -/
theorem lemma23_partial_sum_div_integrableOn_Ioc
    {N : ℕ} (c : ℕ → ℂ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t)
      (Set.Ioc (1 : ℝ) N) := by
  let C : ℝ := ∑ k ∈ Finset.Icc 0 N, ‖c k‖
  have hsumMeas : Measurable (fun t : ℝ => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) :=
    (measurable_of_countable
      (fun m : ℕ => ∑ k ∈ Finset.Icc 0 m, c k)).comp Nat.measurable_floor
  have hmeas : Measurable
      (fun t : ℝ => ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t) := by
    exact hsumMeas.norm.div measurable_id
  have hmajorant : MeasureTheory.IntegrableOn (fun _ : ℝ => C)
      (Set.Ioc (1 : ℝ) N) := continuous_const.integrableOn_Ioc
  apply MeasureTheory.Integrable.mono' hmajorant
  · exact hmeas.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hfloor : ⌊t⌋₊ ≤ N := by simpa using Nat.floor_le_floor ht.2
    have hpartial : ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C := by
      dsimp [C]
      calc
        ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ‖c k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc 0 N, ‖c k‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_right hfloor) (by intros; positivity)
    have ht1 : (1 : ℝ) < t := (Set.mem_Ioc.mp ht).1
    have htpos : 0 < t := lt_trans zero_lt_one ht1
    have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
    calc
      ‖‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t‖ =
          ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t := by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) htpos.le)]
      _ ≤ C / t :=
        div_le_div_of_nonneg_right hpartial htpos.le
      _ ≤ C := div_le_self hCnonneg (le_of_lt ht1)

/-- Abel summation specialized to the actual real-power kernel used in the proof of
Zhang's Lemma 4.1.  Only the coefficient partial-sum estimates and the pointwise
bound on `‖z‖‖t^z‖` remain as hypotheses. -/
theorem lemma23_abel_power_weight_norm_bound
    {N : ℕ} {c : ℕ → ℂ} {z : ℂ} {A B K M : ℝ}
    (hc0 : c 0 = 0)
    (hA : ‖lemma23AbelPowerWeight z N‖ ≤ A)
    (hB : ‖∑ k ∈ Finset.Icc 0 N, c k‖ ≤ B)
    (hK : 0 ≤ K)
    (hweight : ∀ t ∈ Set.Ioc (1 : ℝ) N,
      ‖z‖ * ‖lemma23AbelPowerWeight z t‖ ≤ K)
    (hPartialIntegral : ∫ t in Set.Ioc (1 : ℝ) N,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t ≤ M) :
    ‖∑ k ∈ Finset.Icc 0 N, lemma23AbelPowerWeight z k * c k‖ ≤ A * B + K * M := by
  have hfDiff : ∀ t ∈ Set.Icc (1 : ℝ) N,
      DifferentiableAt ℝ (lemma23AbelPowerWeight z) t := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hlog : HasDerivAt (fun x : ℝ => (Real.log x : ℂ))
        (↑(t⁻¹) : ℂ) t := (Real.hasDerivAt_log htne).ofReal_comp
    have harg : HasDerivAt (fun x : ℝ => z * (Real.log x : ℂ))
        (z * (↑(t⁻¹) : ℂ)) t := hlog.const_mul z
    change DifferentiableAt ℝ (fun x : ℝ => Complex.exp (z * (Real.log x : ℂ))) t
    exact harg.cexp.differentiableAt
  have hExprContinuous : ContinuousOn
      (fun t : ℝ => z * Complex.exp (z * (Real.log t : ℂ)) * (↑(t⁻¹) : ℂ))
      (Set.Icc (1 : ℝ) N) := by
    intro t ht
    have htne : t ≠ 0 := by linarith [ht.1]
    fun_prop
  have hDerivContinuous : ContinuousOn
      (fun t : ℝ => deriv (lemma23AbelPowerWeight z) t) (Set.Icc (1 : ℝ) N) :=
    hExprContinuous.congr (fun t ht =>
      lemma23AbelPowerWeight_deriv z (by linarith [ht.1]))
  have hfInt : MeasureTheory.IntegrableOn
      (deriv (lemma23AbelPowerWeight z)) (Set.Icc (1 : ℝ) N) :=
    hDerivContinuous.integrableOn_Icc
  have hder : ∀ t ∈ Set.Ioc (1 : ℝ) N,
      ‖deriv (lemma23AbelPowerWeight z) t‖ ≤ K / t := by
    intro t ht
    exact lemma23AbelPowerWeight_norm_deriv_le (by linarith [ht.1]) (hweight t ht)
  exact lemma23_abel_partial_sum_norm_bound_of_derivative
    hc0 hfDiff hfInt hA hB hK hder (lemma23_partial_sum_div_integrableOn_Ioc c)
    hPartialIntegral

/-- The numerical exponent bookkeeping in Lemma 4.1: the paper's endpoint and
weighted-integral bounds `L^1171`, together with the kernel bounds `L` and
`‖z‖ ≤ L^406`, imply the desired `L^79` bound once the twentieth-power
Dirichlet expansion is available. The expansion and partial-sum estimates are
kept explicit hypotheses, so this does not yet claim the paper-specific
coefficient theorem. -/
theorem lemma23_sectionFour_L79_from_abel_data
    {N : ℕ} {c : ℕ → ℂ} {z F : ℂ} {L : ℝ}
    (hL : 3 ≤ L)
    (hc0 : c 0 = 0)
    (hExpansion : F ^ 20 =
      ∑ k ∈ Finset.Icc 0 N, lemma23AbelPowerWeight z k * c k)
    (hEndpoint : ‖lemma23AbelPowerWeight z N‖ ≤ L)
    (hCoefficientEndpoint : ‖∑ k ∈ Finset.Icc 0 N, c k‖ ≤ L ^ 1171)
    (hz : ‖z‖ ≤ L ^ 406)
    (hKernel : ∀ t ∈ Set.Ioc (1 : ℝ) N,
      ‖lemma23AbelPowerWeight z t‖ ≤ L)
    (hPartialIntegral : ∫ t in Set.Ioc (1 : ℝ) N,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ / t ≤ L ^ 1171) :
    ‖F‖ ≤ L ^ 79 := by
  have hL1 : 1 ≤ L := by linarith
  have hWeight : ∀ t ∈ Set.Ioc (1 : ℝ) N,
      ‖z‖ * ‖lemma23AbelPowerWeight z t‖ ≤ L ^ 407 := by
    intro t ht
    calc
      ‖z‖ * ‖lemma23AbelPowerWeight z t‖ ≤ L ^ 406 * L :=
        mul_le_mul hz (hKernel t ht) (norm_nonneg _) (by positivity)
      _ = L ^ 407 := by rw [← pow_succ]
  have hAbel := lemma23_abel_power_weight_norm_bound hc0 hEndpoint
    hCoefficientEndpoint (by positivity : 0 ≤ L ^ 407) hWeight
    hPartialIntegral
  have hSum :
      ‖∑ k ∈ Finset.Icc 0 N, lemma23AbelPowerWeight z k * c k‖ ≤
        2 * L ^ 1578 := by
    calc
      ‖∑ k ∈ Finset.Icc 0 N, lemma23AbelPowerWeight z k * c k‖ ≤
          L * L ^ 1171 + L ^ 407 * L ^ 1171 := hAbel
      _ ≤ L ^ 1578 + L ^ 1578 := by
        apply add_le_add
        · calc
            L * L ^ 1171 = L ^ 1171 * L := by ring
            _ = L ^ 1172 := by rw [← pow_succ]
            _ ≤ L ^ 1578 := pow_le_pow_right₀ hL1 (by norm_num)
        · rw [← pow_add]
      _ = 2 * L ^ 1578 := by ring
  have hF20 : ‖F‖ ^ 20 ≤ 3 * L ^ 1578 := by
    calc
      ‖F‖ ^ 20 = ‖F ^ 20‖ := (norm_pow F 20).symm
      _ = ‖∑ k ∈ Finset.Icc 0 N,
          lemma23AbelPowerWeight z k * c k‖ := by rw [hExpansion]
      _ ≤ 2 * L ^ 1578 := hSum
      _ ≤ 3 * L ^ 1578 := by
        have hnonneg : 0 ≤ L ^ 1578 := by positivity
        nlinarith
  have hThree : 3 ≤ L ^ 2 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 2
    norm_num at hpow ⊢
    linarith
  have hPower : ‖F‖ ^ 20 ≤ (L ^ 79) ^ 20 := by
    calc
      ‖F‖ ^ 20 ≤ 3 * L ^ 1578 := hF20
      _ ≤ L ^ 2 * L ^ 1578 :=
        mul_le_mul_of_nonneg_right hThree (by positivity)
      _ = L ^ 1580 := by rw [← pow_add]
      _ = (L ^ 79) ^ 20 := by
        calc
          L ^ 1580 = L ^ (79 * 20) := by norm_num
          _ = (L ^ 79) ^ 20 := pow_mul L 79 20
  exact le_of_pow_le_pow_left₀ (by norm_num : 20 ≠ 0)
    (by positivity : 0 ≤ L ^ 79) hPower

end ZhangLS.Spec
