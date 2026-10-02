import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite Dirichlet-polynomial calculus for Lemma 2.3

Section 4 normalizes the product of two Dirichlet L-functions by a short Dirichlet polynomial
`F(s, ψ)`.  This file starts formalizing that concrete object: it defines the cutoff polynomial,
proves its analytic and derivative formulas, and proves the logarithmic-derivative identities for
the normalized product and its functional-equation companion.  The paper's estimates for these
quantities are separate and are not assumed here.
-/

namespace ZhangLS.Spec

open Complex

/-- The finite Dirichlet polynomial `∑_{1 ≤ n ≤ X} c(n) n^{-s}`, represented using the
exponential definition `n^{-s} = exp(-s log n)`. -/
noncomputable def lemma23FiniteDirichletPolynomial
    (X : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, c n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ))

/-- Expanding a power of a finite Dirichlet polynomial gives a finite sum over
tuples of indices.  This is the ungrouped convolution expansion needed before
reindexing by the product of the tuple entries. -/
theorem lemma23FiniteDirichletPolynomial_pow_eq_tuple_sum
    (X m : ℕ) (c : ℕ → ℂ) (s : ℂ) :
    (lemma23FiniteDirichletPolynomial X c s) ^ m =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X),
        ∏ i, (c (p i) *
          Complex.exp (-s * (Real.log (p i : ℝ) : ℂ))) := by
  classical
  unfold lemma23FiniteDirichletPolynomial
  exact Finset.sum_pow' (Finset.Icc 1 X)
    (fun n => c n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ))) m

/-- The product of the individual Dirichlet exponential kernels depends only
on the product of the tuple entries. -/
theorem lemma23_dirichletTuple_exp_product
    {m : ℕ} (p : Fin m → ℕ) (hp : ∀ i, 1 ≤ p i) (s : ℂ) :
    (∏ i, Complex.exp (-s * (Real.log (p i : ℝ) : ℂ))) =
      Complex.exp (-s * (Real.log ((∏ i, p i : ℕ) : ℝ) : ℂ)) := by
  have hlog : (∑ i : Fin m, Real.log (p i : ℝ)) =
      Real.log ((∏ i : Fin m, p i : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact (Real.log_prod (s := Finset.univ) (f := fun i : Fin m => (p i : ℝ))
        (by
          intro i hi
          change (p i : ℝ) ≠ 0
          have hpi : 0 < p i := lt_of_lt_of_le Nat.zero_lt_one (hp i)
          exact ne_of_gt (Nat.cast_pos.mpr hpi))).symm
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, hlog]

/-- The product of a tuple in the truncated index box stays below the natural
cutoff raised to the tuple length. -/
theorem lemma23_dirichletTuple_prod_mem_Icc
    (X m : ℕ) (p : Fin m → ℕ)
    (hp : p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)) :
    (∏ i : Fin m, p i) ∈ Finset.Icc 1 (X ^ m) := by
  classical
  have hcoord : ∀ i : Fin m, p i ∈ Finset.Icc 1 X :=
    Fintype.mem_piFinset.mp hp
  rw [Finset.mem_Icc]
  constructor
  · exact Finset.one_le_prod' (fun i hi => (Finset.mem_Icc.mp (hcoord i)).1)
  · calc
      (∏ i : Fin m, p i) ≤ ∏ i : Fin m, X :=
        Finset.prod_le_prod' (fun i hi => (Finset.mem_Icc.mp (hcoord i)).2)
      _ = X ^ m := by simp

/-- The `m`-fold Dirichlet convolution coefficient of the cutoff sequence.
It groups tuples according to the product of their entries. -/
noncomputable def lemma23TupleConvolutionCoefficient
    (X m : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
      with (∏ i : Fin m, p i) = n,
    ∏ i : Fin m, c (p i)

/-- The power of a finite Dirichlet polynomial is a Dirichlet polynomial whose
coefficients are obtained by grouping the tuple expansion by the product of
the tuple entries. -/
theorem lemma23FiniteDirichletPolynomial_pow_eq_convolution_sum
    (X m : ℕ) (c : ℕ → ℂ) (s : ℂ) :
    (lemma23FiniteDirichletPolynomial X c s) ^ m =
      ∑ n ∈ Finset.Icc 1 (X ^ m),
        lemma23TupleConvolutionCoefficient X m c n *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
  classical
  let T := Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 X)
  let q : (Fin m → ℕ) → ℕ := fun p => ∏ i : Fin m, p i
  rw [lemma23FiniteDirichletPolynomial_pow_eq_tuple_sum]
  calc
    (∑ p ∈ T,
        ∏ i : Fin m,
          (c (p i) * Complex.exp (-s * (Real.log (p i : ℝ) : ℂ)))) =
      ∑ p ∈ T,
        (∏ i : Fin m, c (p i)) *
          Complex.exp (-s * (Real.log (q p : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.prod_mul_distrib,
              lemma23_dirichletTuple_exp_product p
                (fun i => (Finset.mem_Icc.mp
                  (Fintype.mem_piFinset.mp hp i)).1) s]
    _ = ∑ n ∈ Finset.Icc 1 (X ^ m),
          ∑ p ∈ T with q p = n,
            (∏ i : Fin m, c (p i)) *
              Complex.exp (-s * (Real.log (q p : ℝ) : ℂ)) := by
            symm
            exact Finset.sum_fiberwise_of_maps_to
              (s := T) (t := Finset.Icc 1 (X ^ m)) (g := q)
              (fun p hp => lemma23_dirichletTuple_prod_mem_Icc X m p hp)
              (fun p => (∏ i : Fin m, c (p i)) *
                Complex.exp (-s * (Real.log (q p : ℝ) : ℂ)))
    _ = ∑ n ∈ Finset.Icc 1 (X ^ m),
          lemma23TupleConvolutionCoefficient X m c n *
            Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp only [lemma23TupleConvolutionCoefficient, q]
            simp only [Nat.cast_prod]
            calc
              (∑ p ∈ T with (∏ i : Fin m, p i) = n,
                  (∏ i : Fin m, c (p i)) *
                    Complex.exp (-s * (Real.log ((∏ i : Fin m, p i) : ℝ) : ℂ))) =
                ∑ p ∈ T with (∏ i : Fin m, p i) = n,
                  (∏ i : Fin m, c (p i)) *
                    Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      simp only [Finset.mem_filter] at hp
                      have hprodR :
                          (∏ i : Fin m, (p i : ℝ)) = (n : ℝ) := by
                        rw [← Nat.cast_prod, hp.2]
                      rw [hprodR]
              _ = (∑ p ∈ T with (∏ i : Fin m, p i) = n,
                    ∏ i : Fin m, c (p i)) *
                  Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) := by
                    rw [← Finset.sum_mul]

/-- Every finite Dirichlet polynomial is analytic everywhere. -/
theorem lemma23FiniteDirichletPolynomial_analyticAt
    (X : ℕ) (c : ℕ → ℂ) (s : ℂ) :
    AnalyticAt ℂ (lemma23FiniteDirichletPolynomial X c) s := by
  unfold lemma23FiniteDirichletPolynomial
  fun_prop

/-- Derivative of the finite Dirichlet polynomial, term by term. -/
theorem lemma23FiniteDirichletPolynomial_deriv
    (X : ℕ) (c : ℕ → ℂ) (s : ℂ) :
    deriv (lemma23FiniteDirichletPolynomial X c) s =
      ∑ n ∈ Finset.Icc 1 X,
        c n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
          (-(Real.log (n : ℝ) : ℂ)) := by
  classical
  unfold lemma23FiniteDirichletPolynomial
  rw [deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hlinear : HasDerivAt
        (fun z : ℂ => -z * (Real.log (n : ℝ) : ℂ))
        (-(Real.log (n : ℝ) : ℂ)) s := by
      simpa only [id_eq, neg_one_mul] using
        ((hasDerivAt_id s).neg).mul_const (Real.log (n : ℝ) : ℂ)
    have hexp := hlinear.cexp
    have hterm := (hasDerivAt_const s (c n)).mul hexp
    have hterm' : HasDerivAt
        (fun z : ℂ => c n * Complex.exp (-z * (Real.log (n : ℝ) : ℂ)))
        (c n * Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
          (-(Real.log (n : ℝ) : ℂ))) s := by
      simpa only [zero_mul, zero_add, ← mul_assoc] using hterm
    exact hterm'.deriv
  · intro n hn
    fun_prop

/-- Zhang's Section 4 polynomial `F(s, ψ)=∑_{n≤D^4} ν(n)ψ(n)n^{-s}`.  The coefficient sequence
`ν` is kept explicit so arithmetic estimates can be added independently of the analytic calculus. -/
noncomputable def lemma23SectionFourF
    (D : ℕ) (ν ψ : ℕ → ℂ) (s : ℂ) : ℂ :=
  lemma23FiniteDirichletPolynomial (D ^ 4) (fun n => ν n * ψ n) s

/-- Zhang's companion polynomial `G(s, ψ)=∑_{n≤D^4} υ(n)ψ(n)n^{-s}`. -/
noncomputable def lemma23SectionFourG
    (D : ℕ) (υ ψ : ℕ → ℂ) (s : ℂ) : ℂ :=
  lemma23FiniteDirichletPolynomial (D ^ 4) (fun n => υ n * ψ n) s

/-- The normalized product `A(s, ψ)=L(s, ψ)L(s, χψ)/F(s, ψ)` used in Section 4.  The two
L-functions are parameters so this definition can later be instantiated with the actual primitive
Dirichlet characters, while `F` is already the paper's finite sum. -/
noncomputable def lemma23SectionFourA
    (D : ℕ) (ν ψ : ℕ → ℂ) (Lψ Lχψ : ℂ → ℂ) (s : ℂ) : ℂ :=
  Lψ s * Lχψ s / lemma23SectionFourF D ν ψ s

/-- The auxiliary factor `B(s, ψ)=Z̃(s, ψ)F(1-s, ψ̄)/F(s, ψ)` from (4.10). -/
noncomputable def lemma23SectionFourB
    (D : ℕ) (ν ψ ψbar : ℕ → ℂ) (Ztilde : ℂ → ℂ) (s : ℂ) : ℂ :=
  Ztilde s * lemma23SectionFourF D ν ψbar (1 - s) /
    lemma23SectionFourF D ν ψ s

/-- The normalized product `L₁ L₂ / F` has the expected logarithmic derivative wherever all
three factors are nonzero. -/
theorem lemma23_logDeriv_normalized_product
    {L₁ L₂ F : ℂ → ℂ} {s : ℂ}
    (hL₁ : DifferentiableAt ℂ L₁ s) (hL₂ : DifferentiableAt ℂ L₂ s)
    (hF : DifferentiableAt ℂ F s)
    (hL₁ne : L₁ s ≠ 0) (hL₂ne : L₂ s ≠ 0) (hFne : F s ≠ 0) :
    logDeriv (fun z : ℂ => L₁ z * L₂ z / F z) s =
      logDeriv L₁ s + logDeriv L₂ s - logDeriv F s := by
  have hprodne : L₁ s * L₂ s ≠ 0 := mul_ne_zero hL₁ne hL₂ne
  have hprod : DifferentiableAt ℂ (fun z : ℂ => L₁ z * L₂ z) s := hL₁.mul hL₂
  rw [logDeriv_div (f := fun z : ℂ => L₁ z * L₂ z) (g := F)
      s hprodne hFne hprod hF,
    logDeriv_mul (f := L₁) (g := L₂) s hL₁ne hL₂ne hL₁ hL₂]

/-- Logarithmic derivative of the actual normalized-product shape `A=Lψ Lχψ/F`, conditional only
on the nonvanishing of the three factors at the point. -/
theorem lemma23SectionFourA_logDeriv
    {D : ℕ} {ν ψ : ℕ → ℂ} {Lψ Lχψ : ℂ → ℂ} {s : ℂ}
    (hLψ : DifferentiableAt ℂ Lψ s) (hLχψ : DifferentiableAt ℂ Lχψ s)
    (hLψne : Lψ s ≠ 0) (hLχψne : Lχψ s ≠ 0)
    (hFne : lemma23SectionFourF D ν ψ s ≠ 0) :
    logDeriv (lemma23SectionFourA D ν ψ Lψ Lχψ) s =
      logDeriv Lψ s + logDeriv Lχψ s -
        logDeriv (lemma23SectionFourF D ν ψ) s := by
  have hF : DifferentiableAt ℂ (lemma23SectionFourF D ν ψ) s := by
    exact (lemma23FiniteDirichletPolynomial_analyticAt
      (D ^ 4) (fun n => ν n * ψ n) s).differentiableAt
  simpa [lemma23SectionFourA] using
    lemma23_logDeriv_normalized_product hLψ hLχψ hF hLψne hLχψne hFne

/-- The logarithmic derivative of Zhang's quotient factor
`B(s)=Z(s)F̄(1-s)/F(s)`.  This is the exact algebraic identity underlying equation (4.11); analytic
bounds for its three terms are deliberately not built into the theorem. -/
theorem lemma23_logDeriv_reflection_quotient
    {Z Fbar F : ℂ → ℂ} {s : ℂ}
    (hZ : DifferentiableAt ℂ Z s)
    (hFbar : DifferentiableAt ℂ Fbar (1 - s))
    (hF : DifferentiableAt ℂ F s)
    (hZne : Z s ≠ 0) (hFbarne : Fbar (1 - s) ≠ 0) (hFne : F s ≠ 0) :
    logDeriv (fun z : ℂ => Z z * Fbar (1 - z) / F z) s =
      logDeriv Z s - logDeriv Fbar (1 - s) - logDeriv F s := by
  have hreflect : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => Fbar (1 - z)) s := hFbar.comp s hreflect
  have hreflectDeriv : deriv (fun z : ℂ => 1 - z) s = -1 := by
    exact (hasDerivAt_id s).const_sub (1 : ℂ) |>.deriv
  have hprodne : Z s * Fbar (1 - s) ≠ 0 := mul_ne_zero hZne hFbarne
  have hprod : DifferentiableAt ℂ (fun z : ℂ => Z z * Fbar (1 - z)) s := hZ.mul hcomp
  rw [logDeriv_div (f := fun z : ℂ => Z z * Fbar (1 - z)) (g := F)
      s hprodne hFne hprod hF,
    logDeriv_mul (f := Z) (g := fun z : ℂ => Fbar (1 - z)) s hZne hFbarne hZ hcomp,
    show logDeriv (fun z : ℂ => Fbar (1 - z)) s =
      logDeriv Fbar (1 - s) * deriv (fun z : ℂ => 1 - z) s from logDeriv_comp hFbar hreflect,
    hreflectDeriv]
  ring

/-- Equation (4.11)'s exact logarithmic-derivative identity for Zhang's finite-polynomial
`B`-factor.  The estimate `B'/B=-2 log P+O(𝓛)` is not assumed or concluded here. -/
theorem lemma23SectionFourB_logDeriv
    {D : ℕ} {ν ψ ψbar : ℕ → ℂ} {Ztilde : ℂ → ℂ} {s : ℂ}
    (hZ : DifferentiableAt ℂ Ztilde s)
    (hZne : Ztilde s ≠ 0)
    (hFbarne : lemma23SectionFourF D ν ψbar (1 - s) ≠ 0)
    (hFne : lemma23SectionFourF D ν ψ s ≠ 0) :
    logDeriv (lemma23SectionFourB D ν ψ ψbar Ztilde) s =
      logDeriv Ztilde s -
        logDeriv (lemma23SectionFourF D ν ψbar) (1 - s) -
        logDeriv (lemma23SectionFourF D ν ψ) s := by
  have hFbar : DifferentiableAt ℂ (lemma23SectionFourF D ν ψbar) (1 - s) := by
    exact (lemma23FiniteDirichletPolynomial_analyticAt
      (D ^ 4) (fun n => ν n * ψbar n) (1 - s)).differentiableAt
  have hF : DifferentiableAt ℂ (lemma23SectionFourF D ν ψ) s := by
    exact (lemma23FiniteDirichletPolynomial_analyticAt
      (D ^ 4) (fun n => ν n * ψ n) s).differentiableAt
  simpa [lemma23SectionFourB] using
    lemma23_logDeriv_reflection_quotient hZ hFbar hF hZne hFbarne hFne

end ZhangLS.Spec
