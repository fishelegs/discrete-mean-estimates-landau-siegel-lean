import ZhangLS.Spec.AllModuliGaussParseval
import ZhangLS.Spec.AllModuliFractions
import ZhangLS.Spec.ShiftedAdditiveLargeSieve
import ZhangLS.Spec.Lemma33ActualSamples
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

/-- Nontrivial levels, including every composite level greater than one. -/
def largeSieveModulus := {q : ℕ // 1 < q}
instance (q : largeSieveModulus) : NeZero q.val := ⟨by have := q.property; omega⟩

def allModuliSampleIndex (Q : Finset largeSieveModulus) :=
  Σ q : Q, {u : ZMod q.val.val // IsUnit u}
noncomputable instance (Q : Finset largeSieveModulus) : Fintype (allModuliSampleIndex Q) := by
  classical
  unfold allModuliSampleIndex
  infer_instance
noncomputable def allModuliSamplePoint {Q : Finset largeSieveModulus}
    (i : allModuliSampleIndex Q) : ℝ := (i.2.val.val : ℝ) / i.1.val.val

lemma all_moduli_sample_bounds {Q : Finset largeSieveModulus} (i : allModuliSampleIndex Q) :
    0 ≤ allModuliSamplePoint i ∧ allModuliSamplePoint i ≤ 1 := by
  have hpR : 0 < (i.1.val.val : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hpR.le
  · apply (div_le_iff₀ hpR).mpr
    simpa only [one_mul] using
      (show (i.2.val.val : ℝ) ≤ i.1.val.val by exact_mod_cast (ZMod.val_lt i.2.val).le)

lemma all_moduli_samples_separated {Q : Finset largeSieveModulus} {R P : ℝ}
    (hR : 0 < R) (hRP : R ^ 2 ≤ P ^ 2)
    (hQ : ∀ q ∈ Q, (q.val : ℝ) ≤ 2*R)
    (i j : allModuliSampleIndex Q) (hne : i ≠ j) :
    (8 * P ^ 2)⁻¹ ≤ |allModuliSamplePoint i - allModuliSamplePoint j| := by
  rcases i with ⟨p,u⟩
  rcases j with ⟨q,v⟩
  have hp : 0 < p.val.val := by have := p.val.property; omega
  have hq : 0 < q.val.val := by have := q.val.property; omega
  have hne' : p.val.val ≠ q.val.val ∨ u.val.val ≠ v.val.val := by
    by_contra hn
    push Not at hn
    have he : p = q := Subtype.ext (Subtype.ext hn.1)
    subst q
    have huv : u = v := Subtype.ext (ZMod.val_injective p.val.val hn.2)
    subst v
    exact hne rfl
  have hu : u.val.val.Coprime p.val.val := by
    obtain ⟨w, hw⟩ := u.property
    rw [← hw]
    exact ZMod.val_coe_unit_coprime w
  have hv : v.val.val.Coprime q.val.val := by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw]
    exact ZMod.val_coe_unit_coprime w
  have hh := reduced_fraction_separation hp hq hu hv hne'
  have hpR : 0 < (p.val.val : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q.val.val : ℝ) := by exact_mod_cast hq
  have hprod : (p.val.val : ℝ) * q.val.val ≤ 4 * R ^ 2 := by
    calc
      _ ≤ (2 * R) * (2 * R) := mul_le_mul (hQ p.val p.property)
        (hQ q.val q.property) hqR.le (by positivity)
      _ = _ := by ring
  have hden : (p.val.val : ℝ) * q.val.val ≤ 8 * P ^ 2 := by nlinarith [sq_nonneg P]
  simpa only [one_div,allModuliSamplePoint] using
    (one_div_le_one_div_of_le (mul_pos hpR hqR) hden).trans hh

/-- The unweighted primitive-character large sieve, uniformly for arbitrary (possibly
composite) nontrivial moduli bounded by `2R`, and arbitrary coefficients in a shifted interval.
Subsets of moduli and coefficient support are allowed without further hypotheses. -/
theorem all_moduli_primitive_large_sieve (Q : Finset largeSieveModulus)
    (S : Finset ℕ) (a : ℕ → ℂ) {R : ℝ} (hR : 1 ≤ R)
    (hQ : ∀ q ∈ Q, (q.val : ℝ) ≤ 2*R) (M N : ℕ)
    (hSN : ∀ n ∈ S, M ≤ n ∧ n ≤ M+N) :
    (∑ q ∈ Q, ∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q.val => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod q.val)‖ ^ 2) ≤
      (32 + Real.pi ^ 2) * (R ^ 2 + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let P := Real.sqrt (R^2+(N:ℝ))
  have hP2 : P^2 = R^2+(N:ℝ) := Real.sq_sqrt (by positivity)
  have hP : 1 ≤ P := by
    have := Real.sqrt_nonneg (R^2+(N:ℝ))
    nlinarith [sq_nonneg (R-1), (show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N)]
  have hN : (N:ℝ) ≤ P^2 := by rw [hP2]; nlinarith [sq_nonneg R]
  have hRP : R^2 ≤ P^2 := by rw [hP2]; exact le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hsep := all_moduli_samples_separated (lt_of_lt_of_le zero_lt_one hR) hRP hQ
  have hadd := shifted_additive_large_sieve Finset.univ (@allModuliSamplePoint Q)
    S a hP M N hN hSN (fun i _ => all_moduli_sample_bounds i)
    (fun i _ j _ hne => hsep i j hne)
  rw [hP2] at hadd
  apply le_trans ?_ hadd
  calc
    _ ≤ ∑ q ∈ Q, ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod q.val)),
        ‖lemma33AdditivePolynomial S a u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact all_moduli_primitive_mean_le_additive (by have := q.property; omega) S a
    _ = _ := by
      change _ = ∑ i : (Σ q : Q, {u : ZMod q.val.val // IsUnit u}),
        ‖lemma33TrigSum S a (allModuliSamplePoint i)‖ ^ 2
      rw [Fintype.sum_sigma]
      rw [← Finset.sum_attach Q]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [lemma33_additive_polynomial_eq_trig]
      exact Finset.sum_subtype _ (fun u => by simp) _

/-- Nat-indexed interface for an arbitrary finite subset of nontrivial moduli. -/
theorem primitive_large_sieve_finset (Q : Finset ℕ)
    (hQ1 : ∀ q ∈ Q, 1 < q) (S : Finset ℕ) (a : ℕ → ℂ) {R : ℝ} (hR : 1 ≤ R)
    (hQ : ∀ q ∈ Q, (q : ℝ) ≤ 2*R) (M N : ℕ)
    (hSN : ∀ n ∈ S, M ≤ n ∧ n ≤ M+N) :
    (∑ q ∈ Q, ∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2) ≤
      (32 + Real.pi ^ 2) * (R ^ 2 + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  have h := all_moduli_primitive_large_sieve (Q.subtype (fun q => 1 < q)) S a hR
    (fun q hq => hQ q.val (Finset.mem_subtype.mp hq)) M N hSN
  let f : ℕ → ℝ := fun q => ∑ χ ∈ Finset.univ.filter
    (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2
  change (∑ q ∈ Q.subtype (fun q => 1 < q), f q.val) ≤ _ at h
  rw [Finset.sum_subtype_of_mem f hQ1] at h
  exact h

/-- The actual half-open dyadic window; the explicit lower bound removes the exceptional
level one, and no prime restriction is imposed. -/
noncomputable def primitiveDyadicModuli (R : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌈2*R⌉₊).filter (fun q => R ≤ (q:ℝ) ∧ (q:ℝ) < 2*R)

lemma mem_primitiveDyadicModuli {R : ℝ} {q : ℕ} :
    q ∈ primitiveDyadicModuli R ↔ 1 < q ∧ R ≤ (q:ℝ) ∧ (q:ℝ) < 2*R := by
  classical
  simp only [primitiveDyadicModuli, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨by omega, h.2⟩
  · intro h
    refine ⟨⟨by omega, ?_⟩,h.2⟩
    exact_mod_cast h.2.2.le.trans (Nat.le_ceil _)

/-- Uniform primitive-character large sieve on `R ≤ q < 2R`, for an arbitrary finite
coefficient sequence supported in `M < n ≤ M+N`. The constant is absolute. -/
theorem primitive_dyadic_large_sieve {R : ℝ} (hR : 1 ≤ R)
    (S : Finset ℕ) (a : ℕ → ℂ) (M N : ℕ)
    (hSN : ∀ n ∈ S, M < n ∧ n ≤ M+N) :
    (∑ q ∈ primitiveDyadicModuli R,
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
        ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2) ≤
      (32 + Real.pi ^ 2) * (R ^ 2 + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  exact primitive_large_sieve_finset _
    (fun q hq => (mem_primitiveDyadicModuli.mp hq).1) S a hR
    (fun q hq => (mem_primitiveDyadicModuli.mp hq).2.2.le) M N
    (fun n hn => ⟨(hSN n hn).1.le, (hSN n hn).2⟩)

/-- The standard modulus/totient-weighted companion, with the same absolute constant. -/
theorem all_moduli_primitive_large_sieve_weighted (Q : Finset largeSieveModulus)
    (S : Finset ℕ) (a : ℕ → ℂ) {R : ℝ} (hR : 1 ≤ R)
    (hQ : ∀ q ∈ Q, (q.val : ℝ) ≤ 2*R) (M N : ℕ)
    (hSN : ∀ n ∈ S, M ≤ n ∧ n ≤ M+N) :
    (∑ q ∈ Q, ((q.val : ℝ) / q.val.totient) *
      (∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q.val => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod q.val)‖ ^ 2)) ≤
      (32 + Real.pi ^ 2) * (R ^ 2 + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let P := Real.sqrt (R^2+(N:ℝ))
  have hP2 : P^2 = R^2+(N:ℝ) := Real.sq_sqrt (by positivity)
  have hP : 1 ≤ P := by
    have := Real.sqrt_nonneg (R^2+(N:ℝ))
    nlinarith [sq_nonneg (R-1), (show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N)]
  have hN : (N:ℝ) ≤ P^2 := by rw [hP2]; nlinarith [sq_nonneg R]
  have hRP : R^2 ≤ P^2 := by rw [hP2]; exact le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hsep := all_moduli_samples_separated (lt_of_lt_of_le zero_lt_one hR) hRP hQ
  have hadd := shifted_additive_large_sieve Finset.univ (@allModuliSamplePoint Q)
    S a hP M N hN hSN (fun i _ => all_moduli_sample_bounds i)
    (fun i _ j _ hne => hsep i j hne)
  rw [hP2] at hadd
  apply le_trans ?_ hadd
  calc
    _ ≤ ∑ q ∈ Q, ∑ u ∈ (Finset.univ.filter IsUnit : Finset (ZMod q.val)),
        ‖lemma33AdditivePolynomial S a u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact all_moduli_primitive_mean_weighted_le_additive (by have := q.property; omega) S a
    _ = _ := by
      change _ = ∑ i : (Σ q : Q, {u : ZMod q.val.val // IsUnit u}),
        ‖lemma33TrigSum S a (allModuliSamplePoint i)‖ ^ 2
      rw [Fintype.sum_sigma]
      rw [← Finset.sum_attach Q]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [lemma33_additive_polynomial_eq_trig]
      exact Finset.sum_subtype _ (fun u => by simp) _


/-- Nat-indexed weighted large sieve for arbitrary subsets of moduli. -/
theorem primitive_large_sieve_finset_weighted (Q : Finset ℕ)
    (hQ1 : ∀ q ∈ Q, 1 < q) (S : Finset ℕ) (a : ℕ → ℂ) {R : ℝ} (hR : 1 ≤ R)
    (hQ : ∀ q ∈ Q, (q : ℝ) ≤ 2*R) (M N : ℕ)
    (hSN : ∀ n ∈ S, M ≤ n ∧ n ≤ M+N) :
    (∑ q ∈ Q, ((q : ℝ) / q.totient) *
      (∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2)) ≤
      (32 + Real.pi ^ 2) * (R ^ 2 + (N : ℝ)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  have h := all_moduli_primitive_large_sieve_weighted (Q.subtype (fun q => 1 < q)) S a hR
    (fun q hq => hQ q.val (Finset.mem_subtype.mp hq)) M N hSN
  let f : ℕ → ℝ := fun q => ((q : ℝ) / q.totient) *
    (∑ χ ∈ Finset.univ.filter
    (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2)
  change (∑ q ∈ Q.subtype (fun q => 1 < q), f q.val) ≤ _ at h
  rw [Finset.sum_subtype_of_mem f hQ1] at h
  exact h


/-- The dyadic family is empty throughout the degenerate range `R ≤ 1`. -/
lemma primitiveDyadicModuli_eq_empty_of_le_one {R : ℝ} (hR : R ≤ 1) :
    primitiveDyadicModuli R = ∅ := by
  ext q
  simp only [mem_primitiveDyadicModuli, Finset.notMem_empty, iff_false]
  rintro ⟨hq, hlo, hhi⟩
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  linarith

end ZhangLS.Spec
