import ZhangLS.Spec.DivisorConductorBlockMomentsLong
import ZhangLS.Spec.Lemma56PrimeWeightParameters

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec.DivisorConductorBlockMoments
open Complex Finset
open scoped Classical ComplexConjugate

noncomputable def primeCoefficient (t : ℝ) (p : ℕ) : ℂ :=
  ((p - 1 : ℕ) : ℂ) * (p : ℂ) ^ (I * (t : ℂ))

/-- The literal p-1 prime polynomial with conjugated character values. -/
noncomputable def primePolynomial (S : Finset ℕ) (r : ℕ)
    (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  ∑ p ∈ S, ((p - 1 : ℕ) : ℂ) * (p : ℂ) ^ (I * (t : ℂ)) * conj (θ (p : ZMod r))

theorem imaginary_power_norm (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖(n : ℂ) ^ (I * (t : ℂ))‖ = 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]
  norm_num [Complex.mul_re]

theorem primeCoefficient_norm (t : ℝ) {p : ℕ} (hp : 0 < p) :
    ‖primeCoefficient t p‖ = ((p - 1 : ℕ) : ℝ) := by
  unfold primeCoefficient
  rw [norm_mul, imaginary_power_norm t hp, mul_one, Complex.norm_natCast]

theorem primeCoefficient_norm_le (t : ℝ) {p : ℕ} (hp : p.Prime) :
    ‖primeCoefficient t p‖ ≤ (p : ℝ) := by
  rw [primeCoefficient_norm t hp.pos]
  exact_mod_cast Nat.sub_le p 1

theorem prime_support_card {P : ℝ} (hP : 1 ≤ P) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hupper : ∀ p ∈ S, (p : ℝ) ≤ 2 * P) :
    (S.card : ℝ) ≤ 2 * P := by
  have hsub : S ⊆ Icc 1 ⌊2 * P⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(hprime p hp).one_le, Nat.le_floor (hupper p hp)⟩
  have hc : S.card ≤ ⌊2 * P⌋₊ := by simpa using card_le_card hsub
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by linarith : 0 ≤ 2 * P))

theorem prime_coefficient_energy {P : ℝ} (hP : 1 ≤ P) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hupper : ∀ p ∈ S, (p : ℝ) ≤ 2 * P) (t : ℝ) :
    (∑ p ∈ S, ‖primeCoefficient t p‖ ^ 2) ≤ 8 * P ^ 3 := by
  calc
    _ ≤ ∑ _p ∈ S, (2 * P) ^ 2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (norm_nonneg _) ((primeCoefficient_norm_le t (hprime p hp)).trans (hupper p hp)) 2
    _ = (S.card : ℝ) * (2 * P) ^ 2 := by simp
    _ ≤ (2 * P) * (2 * P) ^ 2 := mul_le_mul_of_nonneg_right (prime_support_card hP S hprime hupper) (sq_nonneg _)
    _ = _ := by ring

/-- Conjugation transfers the genuine inverse-character polynomial to the sieve API. -/
theorem primePolynomial_conjugate_norm (S : Finset ℕ) (r : ℕ)
    (θ : DirichletCharacter ℂ r) (t : ℝ) :
    ‖primePolynomial S r θ t‖ =
      ‖∑ p ∈ S, conj (primeCoefficient t p) * θ (p : ZMod r)‖ := by
  rw [← Complex.norm_conj]
  unfold primePolynomial primeCoefficient
  simp only [map_sum, map_mul, conj_conj]

theorem prime_one_moment {P : ℝ} (hP : 1 ≤ P) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hupper : ∀ p ∈ S, (p : ℝ) ≤ 2 * P) (t : ℝ) :
    ‖primePolynomial S 1 1 t‖ ^ 2 ≤ 16 * P ^ 4 := by
  have heq : primePolynomial S 1 1 t = ∑ p ∈ S, primeCoefficient t p := by
    unfold primePolynomial
    apply sum_congr rfl
    intro p hp
    have hθ : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
      rw [show (p : ZMod 1) = 1 by exact Subsingleton.elim _ _, map_one]
    simp only [hθ, map_one, mul_one, primeCoefficient]
  rw [heq]
  apply (norm_sum_sq_le_card_energy _ _).trans
  calc
    _ ≤ (2 * P) * (8 * P ^ 3) :=
      mul_le_mul (prime_support_card hP S hprime hupper) (prime_coefficient_energy hP S hprime hupper t)
        (sum_nonneg (fun _ _ => sq_nonneg _)) (by linarith)
    _ = _ := by ring

theorem prime_nontrivial_moment {R P : ℝ} (hR : 1 ≤ R) (hP : 1 ≤ P)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hupper : ∀ p ∈ S, (p : ℝ) ≤ 2 * P) (t : ℝ) :
    (∑ r ∈ primitiveDyadicModuli R, ((r : ℝ) / (r.totient : ℝ)) *
      ∑ θ ∈ univ.filter (fun θ : DirichletCharacter ℂ r => θ.IsPrimitive),
        ‖primePolynomial S r θ t‖ ^ 2) ≤
      (16 * (32 + Real.pi ^ 2)) * (R ^ 2 + P) * P ^ 3 := by
  simp_rw [primePolynomial_conjugate_norm]
  have hs := primitive_large_sieve_finset_weighted (primitiveDyadicModuli R)
    (fun r hr => (mem_primitiveDyadicModuli.mp hr).1) S (fun p => conj (primeCoefficient t p))
    hR (fun r hr => (mem_primitiveDyadicModuli.mp hr).2.2.le) 0 ⌊2 * P⌋₊
    (fun p hp => ⟨Nat.zero_le _, by simpa only [zero_add] using Nat.le_floor (hupper p hp)⟩)
  simp only [Complex.norm_conj] at hs
  apply hs.trans
  have he := prime_coefficient_energy hP S hprime hupper t
  have hfloor : (⌊2 * P⌋₊ : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
  calc
    _ ≤ (32 + Real.pi ^ 2) * (R ^ 2 + (⌊2 * P⌋₊ : ℝ)) * (8 * P ^ 3) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ (32 + Real.pi ^ 2) * (2 * (R ^ 2 + P)) * (8 * P ^ 3) := by
      gcongr
      nlinarith [sq_nonneg R]
    _ = _ := by ring

/-- Full exact real conductor block, with the actual conductor-one term. -/
theorem prime_block_bound {R P : ℝ} (hR : 1 ≤ R) (hP : 1 ≤ P)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hupper : ∀ p ∈ S, (p : ℝ) ≤ 2 * P) (t : ℝ) :
    blockMoment R (fun r θ => primePolynomial S r θ t) ≤
      blockConstant * (R ^ 2 + P) * P ^ 3 := by
  apply (blockMoment_le_one_add_nontrivial R _).trans
  have hl := prime_one_moment hP S hprime hupper t
  have hn := prime_nontrivial_moment hR hP S hprime hupper t
  calc
    _ ≤ 16 * P ^ 4 + (16 * (32 + Real.pi ^ 2)) * (R ^ 2 + P) * P ^ 3 := add_le_add hl hn
    _ ≤ 16 * (R ^ 2 + P) * P ^ 3 + (16 * (32 + Real.pi ^ 2)) * (R ^ 2 + P) * P ^ 3 := by
      apply add_le_add _ le_rfl
      calc
        _ = 16 * P * P ^ 3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg R)) (by norm_num))
          (by positivity)
    _ = _ := by unfold blockConstant; ring

noncomputable def paperPrimePolynomial (D r : ℕ) (θ : DirichletCharacter ℂ r) (t : ℝ) : ℂ :=
  primePolynomial (lemma56PaperPrimes D) r θ t

/-- Literal published paper interval. The numeric hL premise supplies its ≤2P geometry;
no analytic hypothesis or prime-distribution estimate is assumed. -/
theorem paper_prime_block_bound {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {R : ℝ} (hR : 1 ≤ R) (t : ℝ) :
    blockMoment R (fun r θ => paperPrimePolynomial D r θ t) ≤
      blockConstant * (R ^ 2 + lemma23PaperP D) * (lemma23PaperP D) ^ 3 := by
  have hp := lemma56_paper_prime_weight_parameters hL
  apply prime_block_bound hR (by linarith [hp.2.1])
  · exact fun p hmem => ((lemma56_mem_paper_primes D p).mp hmem).1
  · intro p hmem
    have hhi := ((lemma56_mem_paper_primes D p).mp hmem).2.2
    linarith [hp.2.2.2.1]

end ZhangLS.Spec.DivisorConductorBlockMoments
