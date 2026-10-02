import ZhangLS.Spec.Lemma171DirichletSeries

/-! A converse absolute-convergence criterion for multiplicative Euler products.
The only convergence assumptions concern the individual prime-power series and
an independent summable majorant for their nonconstant local terms. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EulerProduct
open Finset
open scoped Classical

/-- Summable prime-wise excess bounds force absolute convergence of the actual
multiplicative coefficient series. -/
theorem summable_norm_of_prime_power_tsum_le
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (husum : Summable (fun p : Nat.Primes => u p.val))
    (hubound : ∀ {p : ℕ}, p.Prime → (∑' e : ℕ, ‖f (p ^ e)‖) ≤ 1 + u p) :
    Summable (fun n : ℕ => ‖f n‖) := by
  classical
  have hnorm1 : ‖f 1‖ = (1 : ℝ) := by simp [hf1]
  have hnormmul : ∀ {m n : ℕ}, m.Coprime n →
      ‖f (m * n)‖ = ‖f m‖ * ‖f n‖ := by
    intro m n hmn
    rw [hmul hmn, norm_mul]
  have hnormlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun e : ℕ => ‖‖f (p ^ e)‖‖) := by
    intro p hp
    simpa only [norm_norm] using hlocal hp
  apply summable_of_sum_le (c := Real.exp (∑' p : Nat.Primes, u p.val))
    (fun n => norm_nonneg _)
  intro s
  let S : Finset ℕ := s.biUnion Nat.primeFactors
  let A : Set ℕ := Nat.factoredNumbers S
  have hEuler := summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n => ‖f n‖) hnorm1 hnormmul hnormlocal S
  have hAsum : Summable (fun n : A => ‖f n.val‖) := hEuler.2.summable
  have hIsum : Summable (A.indicator (fun n => ‖f n‖)) :=
    summable_subtype_iff_indicator.mp hAsum
  have hAnonneg : ∀ n, 0 ≤ A.indicator (fun n => ‖f n‖) n := by
    intro n
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) n
  have hs_eq : ∑ n ∈ s, ‖f n‖ = ∑ n ∈ s, A.indicator (fun n => ‖f n‖) n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn0 : n = 0
    · simp [Set.indicator_apply, hn0, hf0]
    · have hnA : n ∈ A := Nat.mem_factoredNumbers_of_primeFactors_subset hn0 (by
        intro p hp
        exact Finset.mem_biUnion.mpr ⟨n, hn, hp⟩)
      simp [Set.indicator_of_mem hnA]
  have hprod : (∏ p ∈ S with p.Prime, ∑' e : ℕ, ‖f (p ^ e)‖) ≤
      Real.exp (∑' p : Nat.Primes, u p.val) := by
    calc
      _ ≤ ∏ p ∈ S with p.Prime, (1 + u p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact tsum_nonneg (fun _ => norm_nonneg _)
        · intro p hp
          exact hubound (Finset.mem_filter.mp hp).2
      _ ≤ Real.exp (∑ p ∈ S with p.Prime, u p) :=
        Real.prod_one_add_le_exp_sum _ hu
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.sum_subtype_eq_sum_filter]
        exact Summable.sum_le_tsum (L := SummationFilter.unconditional Nat.Primes)
          (S.subtype Nat.Prime) (fun p _ => hu p.val) husum
  calc
    ∑ n ∈ s, ‖f n‖ = ∑ n ∈ s, A.indicator (fun n => ‖f n‖) n := hs_eq
    _ ≤ ∑' n : ℕ, A.indicator (fun n => ‖f n‖) n :=
      hIsum.sum_le_tsum s (fun n _ => hAnonneg n)
    _ = ∑' n : A, ‖f n.val‖ := (tsum_subtype A _).symm
    _ = ∏ p ∈ S with p.Prime, ∑' e : ℕ, ‖f (p ^ e)‖ := hEuler.2.tsum_eq
    _ ≤ Real.exp (∑' p : Nat.Primes, u p.val) := hprod

/-- Tail-bound form of `summable_norm_of_prime_power_tsum_le`. -/
theorem summable_norm_of_prime_power_tail_le
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (husum : Summable (fun p : Nat.Primes => u p.val))
    (hubound : ∀ {p : ℕ}, p.Prime → (∑' e : ℕ, ‖f (p ^ (e + 1))‖) ≤ u p) :
    Summable (fun n : ℕ => ‖f n‖) := by
  apply summable_norm_of_prime_power_tsum_le f hf0 hf1 hmul hlocal u hu husum
  intro p hp
  rw [(hlocal hp).tsum_eq_zero_add]
  simpa [hf1] using add_le_add_left (hubound hp) (1 : ℝ)

/-- The same criterion with the majorant defined only on primes. -/
theorem summable_norm_of_prime_power_tsum_le_primes
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖))
    (u : Nat.Primes → ℝ) (hu : ∀ p, 0 ≤ u p) (husum : Summable u)
    (hubound : ∀ p : Nat.Primes, (∑' e : ℕ, ‖f (p.val ^ e)‖) ≤ 1 + u p) :
    Summable (fun n : ℕ => ‖f n‖) := by
  classical
  let v : ℕ → ℝ := fun n => if hn : n.Prime then u ⟨n, hn⟩ else 0
  have hv : ∀ n, 0 ≤ v n := by
    intro n
    dsimp [v]
    split_ifs with hn
    · exact hu ⟨n, hn⟩
    · exact le_rfl
  have hv_eq : (fun p : Nat.Primes => v p.val) = u := by
    funext p
    simp [v, p.property]
  have hvs : Summable (fun p : Nat.Primes => v p.val) := by
    rw [hv_eq]
    exact husum
  apply summable_norm_of_prime_power_tsum_le f hf0 hf1 hmul hlocal v hv hvs
  intro p hp
  simpa [v, hp] using hubound ⟨p, hp⟩

/-- Prime-subtype, nonconstant-tail form of the converse criterion. -/
theorem summable_norm_of_prime_power_tail_le_primes
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖))
    (u : Nat.Primes → ℝ) (hu : ∀ p, 0 ≤ u p) (husum : Summable u)
    (hubound : ∀ p : Nat.Primes, (∑' e : ℕ, ‖f (p.val ^ (e + 1))‖) ≤ u p) :
    Summable (fun n : ℕ => ‖f n‖) := by
  apply summable_norm_of_prime_power_tsum_le_primes f hf0 hf1 hmul hlocal u hu husum
  intro p
  rw [(hlocal p.property).tsum_eq_zero_add]
  simpa [hf1] using add_le_add_left (hubound p) (1 : ℝ)

end EulerProduct
