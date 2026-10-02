import ZhangLS.Spec.Proposition71CoefficientEnergy
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.AllModuliLargeSieve

/-! # Genuine κ*a energy and weighted all-moduli large sieve for Section 7

The full primitive dyadic family, r/φ(r) weights, and actual convolution
coefficients are retained. No averaged polynomial estimate is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

/-- Energy on a positive interval l≥X/3, with the original κ*a coefficients. -/
theorem proposition71_actual_dyadic_coefficient_energy (D : ℕ) (c : ℝ) (d : ℕ)
    {B X : ℝ} (hB : 0≤B) (hX : 0<X) (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B)
    (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hSN : ∀n∈S, 0<n ∧ n≤N) (hSX : ∀n∈S, X/3≤(n : ℝ))
    {s : ℂ} (hs : s.re=1) :
    (∑ n∈S, ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)/
      (n : ℂ)^s‖^2)≤
        B^2*(lemma34Tau 5 d : ℝ)^2*(3/X)*(1+Real.log (N : ℝ))^25 := by
  let A : ℝ := B*(lemma34Tau 5 d : ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  have hterm (n : ℕ) (hn : n∈S) :
      ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)/(n : ℂ)^s‖^2≤
        A^2*(3/X)*((lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹) := by
    have hnp : 0<(n : ℝ) := by exact_mod_cast (hSN n hn).1
    have hcoef := proposition71_actual_convolution_le_tau_five (lemma83PaperBeta D c)
      (lemma83_beta_re D c) hB a ha (d*n)
    have hτ : (lemma34Tau 5 (d*n) : ℝ)≤(lemma34Tau 5 d : ℝ)*(lemma34Tau 5 n : ℝ) := by
      exact_mod_cast proposition71_tau_submultiplicative 5 d n
    have hc : ‖(lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)‖≤
        A*(lemma34Tau 5 n : ℝ) := by
      dsimp [A]
      exact (hcoef.trans (mul_le_mul_of_nonneg_left hτ hB)).trans_eq (by ring)
    have hninv : (n : ℝ)⁻¹≤3/X := by
      rw [←one_div]
      exact (div_le_div_iff₀ hnp hX).mpr (by linarith [hSX n hn])
    rw [norm_div,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hnp,hs,Real.rpow_one]
    calc
      _≤(A*(lemma34Tau 5 n : ℝ)/(n : ℝ))^2 := by gcongr
      _=A^2*((lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹)*(n : ℝ)⁻¹ := by ring
      _≤A^2*((lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹)*(3/X) := by gcongr
      _=_ := by ring
  have hsub : S⊆Icc 1 N := fun n hn => mem_Icc.mpr (hSN n hn)
  calc
    _≤∑ n∈S, A^2*(3/X)*((lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹) := sum_le_sum hterm
    _≤∑ n∈Icc 1 N, A^2*(3/X)*((lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _=A^2*(3/X)*∑ n∈Icc 1 N, (lemma34Tau 5 n : ℝ)^2*(n : ℝ)⁻¹ := by rw [mul_sum]
    _≤A^2*(3/X)*(1+Real.log (N : ℝ))^25 :=
      mul_le_mul_of_nonneg_left (proposition71_tau_five_square_harmonic_sum N hN) (by positivity)
    _=_ := by dsimp [A]; ring

/-- The actual κ*a polynomial has the weighted primitive all-moduli mean
needed by Section7. All closed/strict dyadic modulus endpoints remain exact. -/
theorem proposition71_actual_weighted_dyadic_kappa_mean (D : ℕ) (c : ℝ) (d : ℕ)
    {B X R : ℝ} (hB : 0≤B) (hX : 0<X) (hR : 1≤R)
    (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B)
    (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hSN : ∀n∈S, 0<n ∧ n≤N) (hSX : ∀n∈S, X/3≤(n : ℝ))
    {s : ℂ} (hs : s.re=1) :
    (∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ n∈S,
          ((lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)/(n : ℂ)^s)*
            θ (n : ZMod r)‖^2)≤
      (32+Real.pi^2)*(R^2+(N : ℝ))*
        (B^2*(lemma34Tau 5 d : ℝ)^2*(3/X)*(1+Real.log (N : ℝ))^25) := by
  have hh := primitive_large_sieve_finset_weighted (primitiveDyadicModuli R)
    (fun r hr => (mem_primitiveDyadicModuli.mp hr).1) S
    (fun n => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)/(n : ℂ)^s)
    hR (fun r hr => (mem_primitiveDyadicModuli.mp hr).2.2.le) 0 N
    (fun n hn => ⟨Nat.zero_le n,by simpa using (hSN n hn).2⟩)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (proposition71_actual_dyadic_coefficient_energy D c d hB hX a ha S N hN hSN hSX hs) (by positivity))

/-- The localized interval scale absorbs R²+N by the actual conditions R²≤X,
N≤4X, without pretending that a shifted interval has shorter frequency length. -/
theorem proposition71_actual_localized_kappa_mean (D : ℕ) (c : ℝ) (d : ℕ)
    {B X R : ℝ} (hB : 0≤B) (hX : 0<X) (hR : 1≤R)
    (a : ℕ → ℂ) (ha : ∀n, ‖a n‖≤B)
    (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hSN : ∀n∈S, 0<n ∧ n≤N) (hSX : ∀n∈S, X/3≤(n : ℝ))
    (hRX : R^2≤X) (hNX : (N : ℝ)≤4*X) {s : ℂ} (hs : s.re=1) :
    (∑ r∈primitiveDyadicModuli R, ((r : ℝ)/(Nat.totient r : ℝ))*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖∑ n∈S,
          ((lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*n)/(n : ℂ)^s)*
            θ (n : ZMod r)‖^2)≤
      15*(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(1+Real.log (N : ℝ))^25 := by
  apply (proposition71_actual_weighted_dyadic_kappa_mean D c d hB hX hR a ha S N hN hSN hSX hs).trans
  have hscale : (R^2+(N : ℝ))*(3/X)≤15 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hX).mpr
    linarith
  have hlog : 0≤1+Real.log (N : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)
    linarith
  have hh := mul_le_mul_of_nonneg_right hscale
    (show 0≤(32+Real.pi^2)*B^2*(lemma34Tau 5 d : ℝ)^2*(1+Real.log (N : ℝ))^25 by positivity)
  convert hh using 1 <;> ring

end ZhangLS.Spec
