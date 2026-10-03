import ZhangLS.Spec.ReciprocalDeltaFiniteGcd
import ZhangLS.Spec.Proposition71GaussRestorationMean

/-! The original Section7 mean attached to its literal finite d,k and
infinite coprime-l expression (7.8). No nonprincipal or principal main-term
estimate is assumed here. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_short_factors {D d k : ℕ} (hd : 0<d) (hk : 0<k)
    (hdk : d*k∈lemma81PolynomialIndices D) :
    d∈lemma81PolynomialIndices D ∧ k∈lemma81PolynomialIndices D := by
  have hh := (proposition71_mem_indices D (d*k)).mp hdk
  have hdle : d≤d*k := by nlinarith
  have hkle : k≤d*k := by nlinarith
  exact ⟨(proposition71_mem_indices D d).mpr ⟨hd,
    (by exact_mod_cast hdle : (d : ℝ)≤((d*k : ℕ) : ℝ)).trans_lt hh.2⟩,
    (proposition71_mem_indices D k).mpr ⟨hk,
    (by exact_mod_cast hkle : (k : ℝ)≤((d*k : ℕ) : ℝ)).trans_lt hh.2⟩⟩

noncomputable def proposition71PrimeGcdMean (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  reciprocalDeltaFiniteGcdMean D 1 p (lemma81PolynomialIndices D) (lemma81PolynomialIndices D)
    (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) a₂

/-- All finite support, reciprocal phase and kernel changes in (7.8) are
exact equalities after the already paid primitive-Gauss corrections. -/
theorem proposition71_prime_additive_eq_gcd {D p : ℕ} [NeZero p]
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    proposition71PrimeAdditiveDeltaMean (p := p) D c a₁ a₂=
      proposition71PrimeGcdMean D p c a₁ a₂ := by
  let κ := fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m
  have hc (n : ℕ) (hn : n∈lemma81PolynomialIndices D) : p.Coprime (1*n) := by
    have hn' := (proposition71_mem_indices D n).mp hn
    have hh := proposition71_short_index_unit hp hn'.1 hn'.2
    simpa only [Nat.one_mul,ZMod.isUnit_iff_coprime,Nat.coprime_comm] using hh
  have hq (n : ℕ) (hn : n∈lemma81PolynomialIndices D) :
      1≤((1 : ℝ)*(p : ℝ))*n ∧ ((1 : ℝ)*(p : ℝ))*n≤lemma23PaperP D^10 := by
    simpa only [one_mul] using (proposition71_prime_short_absolute_scales (by linarith) hp hn).2.2
  have he := reciprocalDelta_source_finite_gcd hD hL (by norm_num : 0<(1 : ℕ))
    (lemma81PolynomialIndices D) (lemma81PolynomialIndices D)
    (fun n hn => ((proposition71_mem_indices D n).mp hn).1) κ a₂ hB₁
    (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m)
    hc (by simpa only [Nat.cast_one] using hq) (fun d k hd hk hdk => proposition71_short_factors hd hk hdk)
  change _=reciprocalDeltaFiniteGcdMean D 1 p (lemma81PolynomialIndices D) (lemma81PolynomialIndices D) κ a₂
  rw [←he]
  unfold proposition71PrimeAdditiveDeltaMean
  apply sum_congr rfl
  intro n hn
  congr 1
  rw [←proposition71_positive_nat_tsum _ (by simp [proposition71AdditiveDeltaSingle,proposition71DeltaOneDilatedTerm])]
  apply tsum_congr
  intro m
  simp only [proposition71AdditiveDeltaSingle,proposition71DeltaOneDilatedTerm,PNat.pos,
    if_true,Nat.cast_one,one_mul,κ]
  ring

noncomputable def proposition71GcdMean (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑p : lemma33PrimeIndex D, -I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
    proposition71PrimeGcdMean D p.val c a₁ a₂

theorem proposition71_additive_eq_gcd {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ)
    (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    proposition71AdditiveDeltaMean D c a₁ a₂=proposition71GcdMean D c a₁ a₂ := by
  unfold proposition71AdditiveDeltaMean proposition71GcdMean
  apply sum_congr rfl
  intro p hp
  have hp' : p.val∈lemma56PaperPrimes D := by simpa only [lemma35_prime_windows_eq] using p.property
  rw [proposition71_prime_additive_eq_gcd hD hL hp' hB₁ c a₁ a₂ ha₁]

/-- Original ThetaOne now reaches the actual reciprocal gcd expression,
with the same strict coefficients, original (A), and uniform quantifiers. -/
theorem proposition71_original_gcd_reduction :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-proposition71GcdMean D c a₁ a₂‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨N,hN,hbound⟩ := proposition71_original_additive_delta_reduction B₁ B₂ hB₁ hB₂ ε hε
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hND := (le_max_left _ _).trans hD
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right N ⌈Real.exp 2000⌉₊).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  rw [←proposition71_additive_eq_gcd (by have := hN.trans hND; omega) hL hB₁.le c a₁ a₂ ha₁]
  exact hbound D hND χ hA c a₁ a₂ ha₁ ha₂

end ZhangLS.Spec
