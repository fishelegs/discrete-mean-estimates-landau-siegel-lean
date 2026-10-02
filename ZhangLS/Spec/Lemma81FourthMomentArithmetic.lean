import ZhangLS.Spec.Lemma34CoefficientEnergy
import ZhangLS.Spec.Lemma33
import ZhangLS.Spec.Lemma81Objects

/-! # Convolution arithmetic for genuine fourth moments in Lemma 8.1

Squaring the actual finite character polynomial gives its actual two-fold
coefficient convolution. Its squared coefficient energy is controlled by τ₄,
whose harmonic sum is bounded by (1+log X)^4.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

lemma lemma81_multichoose_two_square_le_four (e : ℕ) :
    Nat.multichoose 2 e ^ 2 ≤ Nat.multichoose 4 e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h2 := lemma34_multichoose_recurrence 2 e (by norm_num)
    have h4 := lemma34_multichoose_recurrence 4 e (by norm_num)
    have hc : (e+2)^2 ≤ (e+1)*(e+4) := by nlinarith
    have hh : (e+1)^2 * Nat.multichoose 2 (e+1)^2 ≤ (e+1)^2 * Nat.multichoose 4 (e+1) := by
      calc
        _ = ((e+2)*Nat.multichoose 2 e)^2 := by rw [← mul_pow,h2]
        _ ≤ ((e+1)*(e+4))*Nat.multichoose 4 e := by
          rw [mul_pow]
          exact Nat.mul_le_mul hc ih
        _ = (e+1)*((e+4)*Nat.multichoose 4 e) := by ring
        _ = (e+1)*((e+1)*Nat.multichoose 4 (e+1)) := by rw [← h4]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < (e+1)^2)).mp hh

lemma lemma81_tau_two_square_le_tau_four (n : ℕ) : lemma34Tau 2 n ^ 2 ≤ lemma34Tau 4 n := by
  by_cases hn : n = 0
  · subst n
    simp [lemma34Tau]
  · unfold lemma34Tau
    rw [(lemma34_tau_multiplicative 2).multiplicative_factorization _ hn,
      (lemma34_tau_multiplicative 4).multiplicative_factorization _ hn]
    simp only [Finsupp.prod]
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod'
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    change lemma34Tau 2 (p^n.factorization p)^2 ≤ lemma34Tau 4 (p^n.factorization p)
    rw [lemma34_tau_prime_power hp' 1,lemma34_tau_prime_power hp' 3]
    exact lemma81_multichoose_two_square_le_four _

lemma lemma81_tau_two_square_harmonic_sum (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, (lemma34Tau 2 n : ℝ)^2 * (n : ℝ)⁻¹) ≤
      (1+Real.log (X : ℝ))^4 := by
  have hH : 0 ≤ (harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (lemma34Tau 4 n : ℝ) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast lemma81_tau_two_square_le_tau_four n)
        (by positivity)
    _ ≤ (harmonic X : ℝ)^4 := lemma34_tau_weighted_sum_le_harmonic_pow 4 X hX
    _ ≤ _ := pow_le_pow_left₀ hH (harmonic_le_one_add_log X) 4

lemma lemma81_tuple_count_le_tau (X k n : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 X)).filter
      (fun p => (∏ i : Fin k, p i) = n)).card ≤ lemma34Tau k n := by
  have hh := lemma34_tuple_sum_le_arithmetic_pow X k (ArithmeticFunction.zeta : ArithmeticFunction ℕ) n
  have he : lemma34TupleSum X k (ArithmeticFunction.zeta : ArithmeticFunction ℕ) n =
      ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 X)).filter
        (fun p => (∏ i : Fin k, p i) = n)).card := by
    unfold lemma34TupleSum
    calc
      _ = ∑ p ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 X)).filter
          (fun p => (∏ i : Fin k, p i) = n), (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.prod_eq_one
        intro i hi
        have hpi := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp).1 i)).1
        exact ArithmeticFunction.zeta_apply_ne (by omega)
      _ = _ := by simp
  rw [he] at hh
  exact hh

lemma lemma81_tuple_coefficient_norm_le {B : ℝ} (hB : 0 ≤ B) (X k : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc 1 X, ‖a n‖ ≤ B) (n : ℕ) :
    ‖lemma23TupleConvolutionCoefficient X k a n‖ ≤ B^k * (lemma34Tau k n : ℝ) := by
  let T := (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 X)).filter
    (fun p => (∏ i : Fin k, p i) = n)
  have ht (p : Fin k → ℕ) (hp : p ∈ T) : ‖∏ i : Fin k, a (p i)‖ ≤ B^k := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin k, B := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i hi
        exact ha _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp).1 i)
      _ = _ := by simp
  have hcard : (T.card : ℝ) ≤ (lemma34Tau k n : ℝ) := by
    exact_mod_cast lemma81_tuple_count_le_tau X k n
  calc
    _ ≤ ∑ p ∈ T, ‖∏ i : Fin k, a (p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B^k := Finset.sum_le_sum ht
    _ = (T.card : ℝ)*B^k := by simp
    _ ≤ (lemma34Tau k n : ℝ)*B^k := mul_le_mul_of_nonneg_right hcard (pow_nonneg hB _)
    _ = _ := by ring

lemma lemma81_tuple_coefficient_zero_of_large (X k : ℕ) (a : ℕ → ℂ) {n : ℕ}
    (hn : X^k < n) : lemma23TupleConvolutionCoefficient X k a n = 0 := by
  unfold lemma23TupleConvolutionCoefficient
  apply Finset.sum_eq_zero
  intro p hp
  have hh := lemma23_dirichletTuple_prod_mem_Icc X k p (Finset.mem_filter.mp hp).1
  rw [(Finset.mem_filter.mp hp).2] at hh
  exact (not_le_of_gt hn (Finset.mem_Icc.mp hh).2).elim

noncomputable def lemma81FiniteCharacterPolynomial {p : ℕ} (X : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) : ℂ :=
  lemma23FiniteDirichletPolynomial X (fun n => a n * ψ (n : ZMod p)) s

lemma lemma81_actual_polynomial_square_expansion {p : ℕ} (X : ℕ) (a : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma81FiniteCharacterPolynomial X a ψ s ^ 2 =
      ∑ n ∈ Finset.Icc 1 (X^2), lemma23TupleConvolutionCoefficient X 2 a n *
        ψ (n : ZMod p) * Complex.exp (-s*(Real.log (n : ℝ) : ℂ)) := by
  have hh := lemma23FiniteDirichletPolynomial_pow_eq_convolution_sum X 2
    (fun n => a n * ψ (n : ZMod p)) s
  simpa only [lemma23_tupleConvolutionCoefficient_twist] using hh

end ZhangLS.Spec
