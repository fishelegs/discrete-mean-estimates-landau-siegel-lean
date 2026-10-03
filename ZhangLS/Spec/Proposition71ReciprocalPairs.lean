import ZhangLS.Spec.Proposition71DeltaPairs
import ZhangLS.Spec.Proposition71PrimeGaussRestoration
import ZhangLS.Spec.AdditiveReciprocity

/-! # Actual reciprocal additive pairs after primitive Gauss averaging

Every original short index is a unit modulo p; the long index has no
coprimality restriction. Joint summability is derived from the genuine
absolute Delta bound before any gcd reindexing is used.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3500000

noncomputable def proposition71ReciprocalWeight (p m n : ℕ) : ℂ :=
  if hn : 0<n then
    letI : NeZero n := ⟨hn.ne'⟩
    ZMod.stdAddChar (-(m : ZMod n)*(p : ZMod n)⁻¹)
  else 0

lemma proposition71_reciprocal_weight_norm (p m n : ℕ) (hn : 0<n) :
    ‖proposition71ReciprocalWeight p m n‖=1 := by
  letI : NeZero n := ⟨hn.ne'⟩
  simp only [proposition71ReciprocalWeight,dif_pos hn]
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

noncomputable def proposition71PrimeReciprocalPair (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℕ+×ℕ+ → ℂ :=
  proposition71DeltaPair D (p : ℝ) (lemma81PolynomialIndices D)
    (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m)
    a₂ (proposition71ReciprocalWeight p)

lemma proposition71_prime_reciprocal_pair_summable {D p : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    Summable (proposition71PrimeReciprocalPair D p c a₁ a₂) := by
  have hpp : p.Prime := ((lemma56_mem_paper_primes D p).mp hp).1
  have hp0 : 0<(p : ℝ) := by exact_mod_cast hpp.pos
  apply (proposition71_delta_pairs_summable_and_bound hD hL hp0 (lemma81PolynomialIndices D)
    (fun n hn => ((proposition71_mem_indices D n).mp hn).1) _ a₂
    (proposition71ReciprocalWeight p) hB₁
    (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m)
    (fun n hn m hm => (proposition71_reciprocal_weight_norm p m n
      ((proposition71_mem_indices D n).mp hn).1).le)
    (fun n hn => (proposition71_prime_short_absolute_scales (by linarith) hp hn).2.2)).1

/-- The literal positive long summand, without a p-coprimality condition. -/
lemma proposition71_additive_single_reciprocity {D p n : ℕ} [NeZero p]
    (hp : p∈lemma56PaperPrimes D) (hn : n∈lemma81PolynomialIndices D)
    (κ : ℕ → ℂ) (m : ℕ+) :
    proposition71AdditiveDeltaSingle (p := p) D n κ (m : ℕ)=
      κ (m : ℕ)*proposition71ReciprocalWeight p (m : ℕ) n*
        lemma53PaperDelta D ((m : ℝ)/((p : ℝ)*(n : ℝ))) := by
  have hn0 := ((proposition71_mem_indices D n).mp hn).1
  letI : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  have hc : n.Coprime p := by
    simpa only [ZMod.isUnit_iff_coprime] using proposition71_short_index_unit hp hn0 ((proposition71_mem_indices D n).mp hn).2
  have hr := additiveReciprocity_delta (D := D) hc (m : ℕ)
  unfold proposition71AdditiveDeltaSingle proposition71DeltaOneDilatedTerm
  simp only [proposition71ReciprocalWeight,dif_pos hn0]
  simp only [PNat.pos,if_true,one_mul]
  calc
    _=κ (m : ℕ)*(lemma53PaperDeltaOne D ((m : ℝ)/((n : ℝ)*(p : ℝ)))*
        ZMod.stdAddChar ((m : ZMod p)*(n : ZMod p)⁻¹)) := by rw [mul_comm (n : ℝ)]; ring
    _=κ (m : ℕ)*(lemma53PaperDelta D ((m : ℝ)/((n : ℝ)*(p : ℝ)))*
        ZMod.stdAddChar (-(m : ZMod n)*(p : ZMod n)⁻¹)) := by rw [hr]
    _=_ := by rw [mul_comm (n : ℝ)]; ring

/-- Exact attachment of the actual prime additive mean to the summable
positive-pair function used by the gcd bijection. -/
theorem proposition71_prime_additive_eq_reciprocal_pairs {D p : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    proposition71PrimeAdditiveDeltaMean (p := p) D c a₁ a₂=
      ∑'mn : ℕ+×ℕ+, proposition71PrimeReciprocalPair D p c a₁ a₂ mn := by
  have hpp : p.Prime := ((lemma56_mem_paper_primes D p).mp hp).1
  have hp0 : 0<(p : ℝ) := by exact_mod_cast hpp.pos
  have hh := proposition71_delta_pairs_summable_and_bound hD hL hp0 (lemma81PolynomialIndices D)
    (fun n hn => ((proposition71_mem_indices D n).mp hn).1)
    (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) a₂
    (proposition71ReciprocalWeight p) hB₁
    (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m)
    (fun n hn m hm => (proposition71_reciprocal_weight_norm p m n
      ((proposition71_mem_indices D n).mp hn).1).le)
    (fun n hn => (proposition71_prime_short_absolute_scales (by linarith) hp hn).2.2)
  unfold proposition71PrimeReciprocalPair
  rw [hh.2.2]
  unfold proposition71PrimeAdditiveDeltaMean
  apply sum_congr rfl
  intro n hn
  congr 1
  rw [←proposition71_positive_nat_tsum _ (by simp [proposition71AdditiveDeltaSingle,proposition71DeltaOneDilatedTerm])]
  apply tsum_congr
  intro m
  exact proposition71_additive_single_reciprocity hp hn _ m

end ZhangLS.Spec
