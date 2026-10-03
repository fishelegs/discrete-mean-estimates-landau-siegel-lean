import ZhangLS.Spec.Proposition71GaussDecomposition
import ZhangLS.Spec.Proposition71DeltaLocalization
import ZhangLS.Spec.Proposition71DivisibleDeltaBranch

/-! # The genuine primitive-Gauss correction for one short index

The O(1)/p correction and the p-divisible restoration are separately defined,
proved summable and bounded. Their combined cost is 7 C_abs B n L^575.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000

noncomputable def proposition71AdditiveDeltaSingle {p : ℕ} [NeZero p]
    (D n : ℕ) (κ : ℕ → ℂ) : ℕ → ℂ :=
  proposition71DeltaOneDilatedTerm D κ
    (fun m => ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)) 1 ((p : ℝ)*(n : ℝ))

noncomputable def proposition71GaussCorrectionSingle {p : ℕ} [NeZero p]
    (D n : ℕ) (κ : ℕ → ℂ) : ℕ → ℂ :=
  proposition71DeltaOneDilatedTerm D κ
    (fun m => 1-ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)) 1 ((p : ℝ)*(n : ℝ))

noncomputable def proposition71NormalizedGaussSingle {p : ℕ} [NeZero p]
    (D n : ℕ) (κ : ℕ → ℂ) (m : ℕ) : ℂ :=
  if 0<m then κ m*lemma53PaperDeltaOne D ((m : ℝ)/((p : ℝ)*(n : ℝ)))*
    ((∑ψ∈(univ : Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum ψ⁻¹ ZMod.stdAddChar*ψ (m : ZMod p)*ψ⁻¹ (n : ZMod p))/(p : ℂ)) else 0

/-- Exact decomposition, including the zero index and the nonunit branch. -/
lemma proposition71_normalized_gauss_single_decomposition {D p n : ℕ} [NeZero p]
    (hp : p∈lemma56PaperPrimes D) (hn : n∈lemma81PolynomialIndices D)
    (κ : ℕ → ℂ) (m : ℕ) :
    proposition71NormalizedGaussSingle (p := p) D n κ m=
      proposition71AdditiveDeltaSingle (p := p) D n κ m+
        (p : ℂ)⁻¹*proposition71GaussCorrectionSingle (p := p) D n κ m-
          proposition71DivisibleDeltaTerm D p n κ m := by
  unfold proposition71NormalizedGaussSingle proposition71AdditiveDeltaSingle
    proposition71GaussCorrectionSingle proposition71DeltaOneDilatedTerm proposition71DivisibleDeltaTerm
  by_cases hm : 0<m
  · rw [if_pos hm,if_pos hm,proposition71_normalized_gauss_nat_decomposition hp hn m]
    simp only [Nat.one_mul]
    by_cases hpm : p∣m <;> simp only [hpm,if_true,if_false,if_pos hm] <;> ring
  · simp only [if_neg hm,mul_zero,zero_add,sub_self,ite_self]

/-- Every required absolute scale follows from the actual original prime and
short support, with no extension of the n-range. -/
lemma proposition71_prime_short_absolute_scales {D p n : ℕ}
    (hL : 3≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    (hn : n∈lemma81PolynomialIndices D) :
    1≤(n : ℝ) ∧ (n : ℝ)≤lemma23PaperP D^10 ∧
      1≤(p : ℝ)*(n : ℝ) ∧ (p : ℝ)*(n : ℝ)≤lemma23PaperP D^10 := by
  have hn' := (proposition71_mem_indices D n).mp hn
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn'.1
  have hnP : (n : ℝ)≤lemma23PaperP D := hn'.2.le.trans (proposition71_cutoff_le_P D)
  have hP : 0< lemma23PaperP D := Real.exp_pos _
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hP2 : 2≤lemma23PaperP D := by
    have hh := Real.add_one_le_exp (lemma23PaperL D^9)
    have h9 := one_le_pow₀ (n := 9) hL1
    change 2≤Real.exp (lemma23PaperL D^9)
    linarith
  have hP1 : 1≤lemma23PaperP D := by linarith
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast ((lemma56_mem_paper_primes D p).mp hp).1.one_le
  have hpP : (p : ℝ)≤2*lemma23PaperP D :=
    (proposition71_paper_prime_le_three_halves_P hL hp).trans (by nlinarith only [hP.le])
  have hP10 : lemma23PaperP D≤lemma23PaperP D^10 := le_self_pow₀ hP1 (by norm_num)
  refine ⟨hn1,hnP.trans hP10,by nlinarith only [hp1,hn1],?_⟩
  calc
    _≤(2*lemma23PaperP D)*lemma23PaperP D := mul_le_mul hpP hnP (by positivity) (by positivity)
    _≤lemma23PaperP D^3 := by nlinarith only [hP2,sq_nonneg (lemma23PaperP D)]
    _≤_ := pow_le_pow_right₀ hP1 (by norm_num)

/-- Actual absolute convergence and combined normalized-Gauss error at one n.
The p-divisible branch contributes τ₅(p)=5 rather than a lost factor p. -/
theorem proposition71_single_gauss_correction_bound {D p n : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    (hn : n∈lemma81PolynomialIndices D) (κ : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hκ : ∀m : ℕ, 0<m → ‖κ m‖≤B*(lemma34Tau 5 m : ℝ)) :
    Summable (proposition71AdditiveDeltaSingle (p := p) D n κ) ∧
      Summable (proposition71NormalizedGaussSingle (p := p) D n κ) ∧
      ‖(∑'m, proposition71NormalizedGaussSingle (p := p) D n κ m)-
        (∑'m, proposition71AdditiveDeltaSingle (p := p) D n κ m)‖≤
          7*tauDeltaAbsoluteConstant*B*(n : ℝ)*lemma23PaperL D^575 := by
  have hpprime := ((lemma56_mem_paper_primes D p).mp hp).1
  have hnp := ((proposition71_mem_indices D n).mp hn).1
  have hsc := proposition71_prime_short_absolute_scales (by linarith) hp hn
  have hτ1 : lemma34Tau 5 1=1 := (lemma34_tau_multiplicative 5).map_one
  have hτp : lemma34Tau 5 p=5 := by
    simpa only [show 4+1=5 by norm_num,pow_one,Nat.multichoose_one_right] using lemma34_tau_prime_power hpprime 4 1
  have hA := proposition71_delta_one_dilated_absolute_bound hD hL κ
    (fun m => ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)) hB (by norm_num : (0 : ℝ)≤1) hκ
    (fun m hm => (proposition71_additive_character_norm (m : ZMod p) (n : ZMod p)).le)
    (by norm_num : (0 : ℕ)<1) hsc.2.2.1 hsc.2.2.2
  have hC := proposition71_delta_one_dilated_absolute_bound hD hL κ
    (fun m => 1-ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)) hB (by norm_num : (0 : ℝ)≤2) hκ
    (fun m hm => proposition71_additive_character_correction_norm (m : ZMod p) (n : ZMod p))
    (by norm_num : (0 : ℕ)<1) hsc.2.2.1 hsc.2.2.2
  have hV := proposition71_divisible_delta_branch_bound hD hL hpprime.pos hnp hsc.2.1 κ hB hκ
  change Summable (proposition71AdditiveDeltaSingle (p := p) D n κ) ∧ _ at hA
  change Summable (proposition71GaussCorrectionSingle (p := p) D n κ) ∧ _ at hC
  have he : proposition71NormalizedGaussSingle (p := p) D n κ=
      (fun m => proposition71AdditiveDeltaSingle (p := p) D n κ m+
        (p : ℂ)⁻¹*proposition71GaussCorrectionSingle (p := p) D n κ m-
          proposition71DivisibleDeltaTerm D p n κ m) :=
    funext (proposition71_normalized_gauss_single_decomposition hp hn κ)
  have hG : Summable (proposition71NormalizedGaussSingle (p := p) D n κ) := by
    rw [he]
    exact (hA.1.add (hC.1.mul_left (p : ℂ)⁻¹)).sub hV.1
  have ht : (∑'m, proposition71NormalizedGaussSingle (p := p) D n κ m)-
      (∑'m, proposition71AdditiveDeltaSingle (p := p) D n κ m)=
      (p : ℂ)⁻¹*(∑'m, proposition71GaussCorrectionSingle (p := p) D n κ m)-
        (∑'m, proposition71DivisibleDeltaTerm D p n κ m) := by
    rw [he,(hA.1.add (hC.1.mul_left _)).tsum_sub hV.1,hA.1.tsum_add (hC.1.mul_left _),tsum_mul_left]
    ring
  have hpr : 0<(p : ℝ) := by exact_mod_cast hpprime.pos
  have hcNorm : ‖(p : ℂ)⁻¹*(∑'m, proposition71GaussCorrectionSingle (p := p) D n κ m)‖≤
      2*tauDeltaAbsoluteConstant*B*(n : ℝ)*lemma23PaperL D^575 := by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    have hh := mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hC.1.norm).trans hC.2) (inv_nonneg.mpr hpr.le)
    apply hh.trans_eq
    simp only [hτ1,Nat.cast_one,mul_one]
    field_simp
  refine ⟨hA.1,hG,?_⟩
  rw [ht]
  apply (norm_sub_le _ _).trans
  have hv := hV.2
  rw [hτp] at hv
  norm_num only [Nat.cast_ofNat] at hv
  exact (add_le_add hcNorm hv).trans_eq (by ring)

end ZhangLS.Spec
