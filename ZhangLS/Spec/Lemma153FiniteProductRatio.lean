import ZhangLS.Spec.Lemma153GeneralMLocal
/-! Exact finite replacement ratios for normally convergent Euler products.
The nonzero baseline is always explicit and will be supplied by the proved
M₁ denominator theorem, rather than silently dividing by a zero product. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma153_finite_ite_hasProd {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    HasProd (fun i => if i ∈ S then f i else 1) (∏ i ∈ S, f i) := by
  change Tendsto (fun T : Finset ι => ∏ i ∈ T, if i ∈ S then f i else 1)
    atTop (𝓝 (∏ i ∈ S, f i))
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨S,fun T hT => hT⟩] with T hT
  rw [← Finset.prod_subset hT (by intro i hi hni; exact if_neg hni)]
  simp

lemma lemma153_finite_replacement_ratio {ι : Type*} (S : Finset ι)
    (f g : ι → ℂ) (F G : ℂ) (hf : HasProd f F) (hg : HasProd g G)
    (hF : F ≠ 0) (hagree : ∀ i, i ∉ S → g i = f i) :
    G/F = ∏ i ∈ S, g i/f i := by
  have hfn (i : ι) : f i ≠ 0 := by
    intro hi
    exact hF ((hf.unique (hasProd_zero_of_exists_eq_zero ⟨i,hi⟩)))
  have hR := lemma153_finite_ite_hasProd S (fun i => g i/f i)
  have he : HasProd g (F*(∏ i ∈ S, g i/f i)) := by
    apply (hf.mul hR).congr_fun
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact (mul_div_cancel₀ _ (hfn i)).symm
    · rw [if_neg hi,mul_one,hagree i hi]
  rw [← he.unique hg]
  exact mul_div_cancel_left₀ _ hF

noncomputable def lemma153PrimeDivisorSet (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.preimage (fun q : Nat.Primes => q.val)
    (fun _ _ _ _ h => Subtype.ext h)

lemma lemma153_mem_prime_divisor_set {n : ℕ} (hn : n ≠ 0) (q : Nat.Primes) :
    q ∈ lemma153PrimeDivisorSet n ↔ q.val ∣ n := by
  unfold lemma153PrimeDivisorSet
  rw [Finset.mem_preimage]
  simp [Nat.mem_primeFactors,q.property,hn]

lemma lemma153_prime_divisor_set_power (q : Nat.Primes) (n : ℕ) (hn : n ≠ 0) :
    lemma153PrimeDivisorSet (q.val^n) = {q} := by
  ext p
  rw [lemma153_mem_prime_divisor_set (pow_ne_zero n q.property.ne_zero),Finset.mem_singleton]
  constructor
  · intro h
    have hpq := p.property.dvd_of_dvd_pow h
    have he := (Nat.dvd_prime q.property).mp hpq
    rcases he with he | he
    · exact False.elim (p.property.ne_one he)
    · exact Subtype.ext he
  · rintro rfl
    exact dvd_pow_self p.val hn

end ZhangLS.Spec
