import ZhangLS.Spec.Proposition71PrimeGaussAttachment
import ZhangLS.Spec.Proposition71GaussDecomposition
import ZhangLS.Spec.Proposition71DeltaOneAbsolute
import ZhangLS.Spec.Proposition71NatMultiples
import ZhangLS.Spec.Proposition71DivisibleDeltaBranch
import ZhangLS.Spec.Proposition71SingleGaussCorrection
import ZhangLS.Spec.Proposition71PrimeGaussRestoration
import ZhangLS.Spec.Proposition71GaussRestorationMean

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
example {p : ℕ} [NeZero p] (hp : p.Prime) (k : ZMod p) (hk : IsUnit k) :
    (∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum ψ⁻¹ ZMod.stdAddChar*ψ 0*ψ⁻¹ k)/(p : ℂ)=0 := by
  rw [proposition71_normalized_gauss_decomposition hp 0 k hk]
  simp
example (D p n : ℕ) (κ : ℕ → ℂ) : proposition71DivisibleDeltaTerm D p n κ 0=0 := by
  simp [proposition71DivisibleDeltaTerm]
example {p n : ℕ} (hp : 0<p) (hn : 0<n) (D : ℕ) (κ : ℕ → ℂ) (l : ℕ) :
    (if 0<p*l then κ (p*l)*lemma53PaperDeltaOne D (((p*l : ℕ) : ℝ)/((p : ℝ)*(n : ℝ))) else 0)=
      proposition71DeltaOneDilatedTerm D κ (fun _ => 1) p (n : ℝ) l :=
  proposition71_divisible_delta_reindexed hp hn D κ l
example (D : ℕ) : ((lemma81PolynomialIndices D).card : ℝ)≤
    lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) := proposition71_strict_indices_card_le_cutoff D
example (D : ℕ) : (Fintype.card (lemma33PrimeIndex D) : ℝ)*lemma23PaperP D≤lemma33ActualPrimeMass D :=
  proposition71_prime_count_times_P_le_mass D
#check proposition71_original_gauss_restoration_bound
#check proposition71_original_additive_delta_reduction
end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition71_actual_family_sum_by_prime
#print axioms ZhangLS.Spec.proposition71PrimeGaussDeltaTerm
#print axioms ZhangLS.Spec.proposition71_actual_gauss_term_interchange
#print axioms ZhangLS.Spec.proposition71_actual_prime_gauss_average_series
#print axioms ZhangLS.Spec.proposition71_actual_prime_gauss_term_branches
#print axioms ZhangLS.Spec.proposition71PrimeAveragedDeltaMean
#print axioms ZhangLS.Spec.proposition71_original_delta_mean_eq_prime_average
#print axioms ZhangLS.Spec.proposition71_additive_character_norm
#print axioms ZhangLS.Spec.proposition71_additive_character_correction_norm
#print axioms ZhangLS.Spec.proposition71_normalized_gauss_decomposition
#print axioms ZhangLS.Spec.proposition71_normalized_gauss_nat_decomposition
#print axioms ZhangLS.Spec.proposition71DeltaOneDilatedTerm
#print axioms ZhangLS.Spec.proposition71_delta_one_dilated_norm_bound
#print axioms ZhangLS.Spec.proposition71_delta_one_dilated_absolute_bound
#print axioms ZhangLS.Spec.proposition71_nat_multiples_tsum
#print axioms ZhangLS.Spec.proposition71_nat_multiples_summable_iff
#print axioms ZhangLS.Spec.proposition71DivisibleDeltaTerm
#print axioms ZhangLS.Spec.proposition71_divisible_delta_reindexed
#print axioms ZhangLS.Spec.proposition71_divisible_delta_branch_bound
#print axioms ZhangLS.Spec.proposition71AdditiveDeltaSingle
#print axioms ZhangLS.Spec.proposition71GaussCorrectionSingle
#print axioms ZhangLS.Spec.proposition71NormalizedGaussSingle
#print axioms ZhangLS.Spec.proposition71_normalized_gauss_single_decomposition
#print axioms ZhangLS.Spec.proposition71_prime_short_absolute_scales
#print axioms ZhangLS.Spec.proposition71_single_gauss_correction_bound
#print axioms ZhangLS.Spec.proposition71PrimeAdditiveDeltaMean
#print axioms ZhangLS.Spec.proposition71_prime_gauss_term_by_short_index
#print axioms ZhangLS.Spec.proposition71_prime_gauss_mean_by_short_index
#print axioms ZhangLS.Spec.proposition71_prime_gauss_restoration_bound
#print axioms ZhangLS.Spec.proposition71_strict_indices_card_le_cutoff
#print axioms ZhangLS.Spec.proposition71AdditiveDeltaMean
#print axioms ZhangLS.Spec.proposition71_prime_count_times_P_le_mass
#print axioms ZhangLS.Spec.proposition71_original_gauss_restoration_bound
#print axioms ZhangLS.Spec.proposition71_original_gauss_restoration_little_o
#print axioms ZhangLS.Spec.proposition71_original_additive_delta_reduction
#print ZhangLS.Spec.proposition71PrimeGaussDeltaTerm
#print ZhangLS.Spec.proposition71PrimeAveragedDeltaMean
#print ZhangLS.Spec.proposition71_normalized_gauss_decomposition
#print ZhangLS.Spec.proposition71_normalized_gauss_nat_decomposition
#print ZhangLS.Spec.proposition71DivisibleDeltaTerm
#print ZhangLS.Spec.proposition71_divisible_delta_branch_bound
#print ZhangLS.Spec.proposition71NormalizedGaussSingle
#print ZhangLS.Spec.proposition71_single_gauss_correction_bound
#print ZhangLS.Spec.proposition71PrimeAdditiveDeltaMean
#print ZhangLS.Spec.proposition71AdditiveDeltaMean
#print ZhangLS.Spec.proposition71_original_gauss_restoration_bound
#print ZhangLS.Spec.proposition71_original_gauss_restoration_little_o
#print ZhangLS.Spec.proposition71_original_additive_delta_reduction
#print ZhangLS.Spec.tauDeltaAbsoluteConstant
#print ZhangLS.Spec.tauDelta_actual_absolute_sum
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.lemma81ThetaOne
#print ZhangLS.Spec.lemma33ActualFamily
#print ZhangLS.Spec.lemma33ActualPrimeMass
#print ZhangLS.Spec.Proposition71AtConstant
