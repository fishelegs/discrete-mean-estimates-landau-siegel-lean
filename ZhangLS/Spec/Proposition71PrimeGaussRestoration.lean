import ZhangLS.Spec.Proposition71SingleGaussCorrection
import ZhangLS.Spec.Proposition71PrimeGaussAttachment

/-! # Summing both genuine Gauss corrections over the original short support

The short cardinality remains explicit. It is later bounded by PT⁻², not P,
so the actual prime sum can pay for every principal/nonunit restoration term.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000

noncomputable def proposition71PrimeAdditiveDeltaMean {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑n∈lemma81PolynomialIndices D, (a₂ n/(n : ℂ))*
    (∑'m, proposition71AdditiveDeltaSingle (p := p) D n
      (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) m)

lemma proposition71_prime_gauss_term_by_short_index {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) (m : ℕ) :
    (p : ℂ)⁻¹*proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m=
      ∑n∈lemma81PolynomialIndices D, (a₂ n/(n : ℂ))*
        proposition71NormalizedGaussSingle (p := p) D n
          (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) m := by
  by_cases hm : m=0
  · subst m; simp [proposition71PrimeGaussDeltaTerm,proposition71NormalizedGaussSingle]
  have hmp : 0<m := Nat.pos_of_ne_zero hm
  unfold proposition71PrimeGaussDeltaTerm proposition71NormalizedGaussSingle
  simp only [if_neg hm,if_pos hmp,mul_sum]
  apply sum_congr rfl
  intro n hn
  simp only [div_eq_mul_inv,mul_sum,sum_mul]
  apply sum_congr rfl
  intro ψ hψ
  ring

lemma proposition71_prime_gauss_mean_by_short_index {D p : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    (p : ℂ)⁻¹*(∑'m, proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m)=
      ∑n∈lemma81PolynomialIndices D, (a₂ n/(n : ℂ))*
        (∑'m, proposition71NormalizedGaussSingle (p := p) D n
          (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) m) := by
  let κ := fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m
  have hκ (m : ℕ) (_hm : 0<m) : ‖κ m‖≤B₁*(lemma34Tau 5 m : ℝ) :=
    proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m
  have hs (n : ℕ) (hn : n∈lemma81PolynomialIndices D) :=
    (proposition71_single_gauss_correction_bound hD hL hp hn κ hB₁ hκ).2.1
  have hh := hasSum_sum (s := lemma81PolynomialIndices D)
    (fun n hn => (hs n hn).hasSum.mul_left (a₂ n/(n : ℂ)))
  have hsum : HasSum (fun m => (p : ℂ)⁻¹*proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m)
      (∑n∈lemma81PolynomialIndices D, (a₂ n/(n : ℂ))*
        (∑'m, proposition71NormalizedGaussSingle (p := p) D n κ m)) := by
    apply hh.congr
    intro S
    apply sum_congr rfl
    intro m hm
    exact (proposition71_prime_gauss_term_by_short_index D c a₁ a₂ m).symm
  simpa only [tsum_mul_left] using hsum.tsum_eq

/-- Both principal correction and p-divisible restoration have now been paid
for, with the exact count of short indices still visible. -/
theorem proposition71_prime_gauss_restoration_bound {D p : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ B₂ : ℝ} (hB₁ : 0≤B₁) (hB₂ : 0≤B₂) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ha₂ : ∀n, ‖a₂ n‖≤B₂) :
    ‖(p : ℂ)⁻¹*(∑'m, proposition71PrimeGaussDeltaTerm (p := p) D c a₁ a₂ m)-
      proposition71PrimeAdditiveDeltaMean (p := p) D c a₁ a₂‖≤
      7*tauDeltaAbsoluteConstant*B₁*B₂*((lemma81PolynomialIndices D).card : ℝ)*lemma23PaperL D^575 := by
  let κ := fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m
  have hκ (m : ℕ) (_hm : 0<m) : ‖κ m‖≤B₁*(lemma34Tau 5 m : ℝ) :=
    proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m
  rw [proposition71_prime_gauss_mean_by_short_index hD hL hp hB₁ c a₁ a₂ ha₁]
  unfold proposition71PrimeAdditiveDeltaMean
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑_n∈lemma81PolynomialIndices D, 7*tauDeltaAbsoluteConstant*B₁*B₂*lemma23PaperL D^575 := by
      apply sum_le_sum
      intro n hn
      have hnp : 0<(n : ℝ) := by exact_mod_cast ((proposition71_mem_indices D n).mp hn).1
      have hb := (proposition71_single_gauss_correction_bound hD hL hp hn κ hB₁ hκ).2.2
      rw [←mul_sub,norm_mul,norm_div,Complex.norm_natCast]
      have hh := mul_le_mul (div_le_div_of_nonneg_right (ha₂ n) hnp.le) hb
        (norm_nonneg _) (div_nonneg hB₂ hnp.le)
      apply hh.trans_eq
      field_simp
    _=_ := by simp only [sum_const,nsmul_eq_mul]; ring

lemma proposition71_strict_indices_card_le_cutoff (D : ℕ) :
    ((lemma81PolynomialIndices D).card : ℝ)≤lemma81Cutoff D := by
  have hsub : lemma81PolynomialIndices D⊆Icc 1 ⌊lemma81Cutoff D⌋₊ := by
    intro n hn
    have hh := (proposition71_mem_indices D n).mp hn
    exact mem_Icc.mpr ⟨hh.1,Nat.le_floor hh.2.le⟩
  have hh := card_le_card hsub
  simp only [Nat.card_Icc,add_tsub_cancel_right] at hh
  have hcut : 0≤lemma81Cutoff D := by unfold lemma81Cutoff lemma23PaperP lemma56PaperT; positivity
  exact (by exact_mod_cast hh : ((lemma81PolynomialIndices D).card : ℝ)≤⌊lemma81Cutoff D⌋₊).trans
    (Nat.floor_le hcut)

end ZhangLS.Spec
