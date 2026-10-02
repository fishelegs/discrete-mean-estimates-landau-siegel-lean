import ZhangLS.Spec.Proposition71Objects
import ZhangLS.Spec.Proposition71GaussAverage

/-! # Exact strict-support and unit branches for Section 7

The short k variable is a unit modulo the family prime; this is not claimed
for the long l variable. The latter nonunit branch remains explicit.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma proposition71_cutoff_le_P (D : ℕ) : lemma81Cutoff D ≤ lemma23PaperP D := by
  have hT : 1 ≤ lemma56PaperT D := by
    apply Real.one_le_exp_iff.mpr
    exact Real.rpow_nonneg (Real.log_natCast_nonneg D) _
  have h := zpow_le_one_of_nonpos₀ hT (by norm_num : (-2 : ℤ) ≤ 0)
  unfold lemma81Cutoff
  simpa using mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- Every positive integer occurring in a supported a₂(dk) is below p. -/
theorem proposition71_short_index_lt_prime {D p n : ℕ}
    (hprime : p ∈ lemma56PaperPrimes D)
    (hcut : (n : ℝ) < lemma81Cutoff D) : n < p := by
  have hp := (lemma56_mem_paper_primes D p).mp hprime
  have he : (n : ℝ) < (p : ℝ) := hcut.trans
    ((proposition71_cutoff_le_P D).trans_lt hp.2.1)
  exact_mod_cast he

/-- The short support really proves the unit condition; it is not assumed. -/
theorem proposition71_short_index_unit {D p n : ℕ}
    (hprime : p ∈ lemma56PaperPrimes D) (hn : 0 < n)
    (hcut : (n : ℝ) < lemma81Cutoff D) : IsUnit (n : ZMod p) := by
  have hp := ((lemma56_mem_paper_primes D p).mp hprime).1
  have hnp := proposition71_short_index_lt_prime hprime hcut
  rw [ZMod.isUnit_iff_coprime,Nat.coprime_comm,hp.coprime_iff_not_dvd]
  exact fun h => (not_le_of_gt hnp) (Nat.le_of_dvd hn h)

/-- Applied to the actual a₂(dk), positivity and nonzero coefficient imply
that k is a unit. No condition is imposed on the unrelated long index l. -/
theorem proposition71_supported_second_index_unit {D p d k : ℕ} {B : ℝ}
    {a : ℕ → ℂ} (ha : Lemma81AdmissibleSequence D B a)
    (hprime : p ∈ lemma56PaperPrimes D) (hd : 0 < d) (hk : 0 < k)
    (han : a (d*k) ≠ 0) : IsUnit (k : ZMod p) := by
  have hcut : ((d*k : ℕ) : ℝ) < lemma81Cutoff D :=
    lt_of_not_ge (fun h => han (ha.2 (d*k) h))
  have hkle : k ≤ d*k := by nlinarith
  apply proposition71_short_index_unit hprime hk
  exact (by exact_mod_cast hkle : (k : ℝ) ≤ ((d*k : ℕ) : ℝ)).trans_lt hcut

/-- In particular the nonunit l branch is precisely a vanished average. -/
theorem proposition71_divisible_long_index_zero {D p k l : ℕ} [NeZero p]
    (hprime : p ∈ lemma56PaperPrimes D) (hpl : p ∣ l) :
    (∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter
      (fun ψ => ψ.IsPrimitive), gaussSum ψ⁻¹ ZMod.stdAddChar *
        ψ (l : ZMod p) * ψ⁻¹ (k : ZMod p)) = 0 := by
  have hp := ((lemma56_mem_paper_primes D p).mp hprime).1
  letI : Fact p.Prime := ⟨hp⟩
  have hzero : (l : ZMod p) = 0 := by exact_mod_cast (ZMod.natCast_eq_zero_iff l p).mpr hpl
  exact proposition71_gauss_average_nonunit _ _ (Or.inl (by rw [hzero]; exact not_isUnit_zero))

/-- Every positive factor is bounded by the triple product. -/
lemma proposition71_factors_le_product {d r m : ℕ} (hd : 0<d) (hr : 0<r) (hm : 0<m) :
    d≤d*r*m ∧ r≤d*r*m ∧ m≤d*r*m := by
  have hdr : 0<d*r := Nat.mul_pos hd hr
  have hdle : d≤d*r := by nlinarith
  have hrle : r≤d*r := by nlinarith
  have hle : d*r≤d*r*m := by nlinarith
  exact ⟨hdle.trans hle,hrle.trans hle,by nlinarith⟩

/-- No positive term of the original four arithmetic sums is lost by the
finite cutoff: outside the displayed finite index box its coefficient vanishes. -/
theorem proposition71_omitted_positive_coefficient_zero {D d r m n : ℕ}
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂)
    (hd : 0<d) (hr : 0<r) (hm : 0<m) (hn : 0<n)
    (hout : ¬(d ∈ lemma81PolynomialIndices D ∧ r ∈ lemma81PolynomialIndices D ∧
      m ∈ lemma81PolynomialIndices D ∧ n ∈ lemma81PolynomialIndices D)) :
    a₁ (d*r*m)*a₂ (d*r*n)=0 := by
  by_contra h
  have hne := mul_ne_zero_iff.mp h
  have hc₁ : ((d*r*m : ℕ) : ℝ)<lemma81Cutoff D :=
    lt_of_not_ge (fun hh => hne.1 (h₁.2 _ hh))
  have hc₂ : ((d*r*n : ℕ) : ℝ)<lemma81Cutoff D :=
    lt_of_not_ge (fun hh => hne.2 (h₂.2 _ hh))
  have hprod₁ := proposition71_factors_le_product hd hr hm
  have hprod₂ := proposition71_factors_le_product hd hr hn
  apply hout
  rw [proposition71_mem_indices,proposition71_mem_indices,
    proposition71_mem_indices,proposition71_mem_indices]
  exact ⟨⟨hd,(by exact_mod_cast hprod₁.1 : (d : ℝ) ≤ ((d*r*m : ℕ) : ℝ)).trans_lt hc₁⟩,
    ⟨hr,(by exact_mod_cast hprod₁.2.1 : (r : ℝ) ≤ ((d*r*m : ℕ) : ℝ)).trans_lt hc₁⟩,
    ⟨hm,(by exact_mod_cast hprod₁.2.2 : (m : ℝ) ≤ ((d*r*m : ℕ) : ℝ)).trans_lt hc₁⟩,
    ⟨hn,(by exact_mod_cast hprod₂.2.2 : (n : ℝ) ≤ ((d*r*n : ℕ) : ℝ)).trans_lt hc₂⟩⟩

end ZhangLS.Spec
