import ZhangLS.Spec.Proposition71GcdAttachment
import ZhangLS.Spec.Proposition71CharacterFibers

/-! The actual finite arithmetic Section7 mean splits exactly into the
principal mu/phi fiber and genuine nonprincipal character fibers (7.9). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate
set_option maxHeartbeats 3500000

noncomputable def proposition71PrincipalGcdBlock (D p d k : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  if 0<d ∧ 0<k ∧ d*k∈lemma81PolynomialIndices D then
    (d : ℂ)⁻¹*(a₂ (d*k)/(k : ℂ))*((ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ))*
      proposition71PrincipalDeltaFiber D d k ((p : ℝ)*(k : ℝ))
        (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m)
  else 0

noncomputable def proposition71NonprincipalGcdBlock (D p d k : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  if h : 0<d ∧ 0<k ∧ d*k∈lemma81PolynomialIndices D then
    letI : NeZero k := ⟨h.2.1.ne'⟩
    (d : ℂ)⁻¹*(a₂ (d*k)/(k : ℂ))*(k.totient : ℂ)⁻¹*
      ∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
        gaussSum θ⁻¹ ZMod.stdAddChar*conj (θ (p : ZMod k))*
          proposition71CharacterDeltaFiber D d ((p : ℝ)*(k : ℝ))
            (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) θ
  else 0

/-- Literal actual d,k block, preserving the original coefficient product. -/
theorem proposition71_gcd_block_split {D p : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (d k : ℕ+) :
    (∑'l : ℕ+, if Nat.Coprime (l : ℕ) (k : ℕ) then
      reciprocalDeltaGcdTerm D 1 p (lemma81PolynomialIndices D)
        (fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m) a₂ d l k else 0)=
      proposition71PrincipalGcdBlock D p (d : ℕ) (k : ℕ) c a₁ a₂+
        proposition71NonprincipalGcdBlock D p (d : ℕ) (k : ℕ) c a₁ a₂ := by
  let κ := fun m => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) m
  let v := (d : ℂ)⁻¹*(a₂ ((d : ℕ)*(k : ℕ))/(k : ℂ))
  by_cases hdk : (d : ℕ)*(k : ℕ)∈lemma81PolynomialIndices D
  · have hkS := (proposition71_short_factors d.property k.property hdk).2
    have hk' := (proposition71_mem_indices D (k : ℕ)).mp hkS
    have hpk : p.Coprime (k : ℕ) := by
      have hu := proposition71_short_index_unit hp hk'.1 hk'.2
      simpa only [ZMod.isUnit_iff_coprime,Nat.coprime_comm] using hu
    letI : NeZero (k : ℕ) := ⟨k.property.ne'⟩
    have hsc := (proposition71_prime_short_absolute_scales (by linarith) hp hkS).2.2
    have hs := proposition71_reciprocal_fiber_split hD hL hpk κ hB₁
      (fun m hm => proposition71_actual_convolution_le_tau_five _ (lemma83_beta_re D c) hB₁ a₁ ha₁.1 m)
      d.property hsc.1 hsc.2
    calc
      _=v*(∑'l : ℕ+, if Nat.Coprime (l : ℕ) (k : ℕ) then
        κ ((d : ℕ)*(l : ℕ))*deltaReciprocalWeight p (l : ℕ) (k : ℕ)*
          lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(k : ℝ))) else 0) := by
        rw [←tsum_mul_left]
        apply tsum_congr
        intro l
        by_cases hl : Nat.Coprime (l : ℕ) (k : ℕ)
        · simp only [if_pos hl,reciprocalDeltaGcdTerm,if_pos hdk,Nat.one_mul,Nat.cast_one,one_mul]
          dsimp [v,κ]
          ring
        · simp only [if_neg hl,mul_zero]
      _=_ := by
        simp only [proposition71PrincipalGcdBlock,proposition71NonprincipalGcdBlock,
          if_pos (show 0<(d : ℕ) ∧ 0<(k : ℕ) ∧ (d : ℕ)*(k : ℕ)∈lemma81PolynomialIndices D from
            ⟨d.property,k.property,hdk⟩),
          dif_pos (show 0<(d : ℕ) ∧ 0<(k : ℕ) ∧ (d : ℕ)*(k : ℕ)∈lemma81PolynomialIndices D from
            ⟨d.property,k.property,hdk⟩)]
        convert congrArg (fun z => v*z) hs using 1 <;> dsimp only [v,κ] <;> ring_nf <;> congr 1
  · simp [reciprocalDeltaGcdTerm,proposition71PrincipalGcdBlock,proposition71NonprincipalGcdBlock,hdk]

noncomputable def proposition71PrimePrincipalMean (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑d∈lemma81PolynomialIndices D, ∑k∈lemma81PolynomialIndices D,
    proposition71PrincipalGcdBlock D p d k c a₁ a₂

noncomputable def proposition71PrimeNonprincipalMean (D p : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑d∈lemma81PolynomialIndices D, ∑k∈lemma81PolynomialIndices D,
    proposition71NonprincipalGcdBlock D p d k c a₁ a₂

/-- The actual (7.9) split after all Gauss corrections were paid. -/
theorem proposition71_prime_gcd_principal_split {D p : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) (hp : p∈lemma56PaperPrimes D)
    {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    proposition71PrimeGcdMean D p c a₁ a₂=
      proposition71PrimePrincipalMean D p c a₁ a₂+proposition71PrimeNonprincipalMean D p c a₁ a₂ := by
  unfold proposition71PrimeGcdMean reciprocalDeltaFiniteGcdMean
    proposition71PrimePrincipalMean proposition71PrimeNonprincipalMean
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hd0 := ((proposition71_mem_indices D d).mp hd).1
  have hk0 := ((proposition71_mem_indices D k).mp hk).1
  rw [dif_pos hd0,dif_pos hk0]
  exact proposition71_gcd_block_split hD hL hp hB₁ c a₁ a₂ ha₁ ⟨d,hd0⟩ ⟨k,hk0⟩

noncomputable def proposition71PrincipalMean (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑p : lemma33PrimeIndex D, -I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
    proposition71PrimePrincipalMean D p.val c a₁ a₂

noncomputable def proposition71NonprincipalMean (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑p : lemma33PrimeIndex D, -I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
    proposition71PrimeNonprincipalMean D p.val c a₁ a₂

theorem proposition71_gcd_eq_principal_add_nonprincipal {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {B₁ : ℝ} (hB₁ : 0≤B₁) (c : ℝ)
    (a₁ a₂ : ℕ → ℂ) (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) :
    proposition71GcdMean D c a₁ a₂=
      proposition71PrincipalMean D c a₁ a₂+proposition71NonprincipalMean D c a₁ a₂ := by
  unfold proposition71GcdMean proposition71PrincipalMean proposition71NonprincipalMean
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hp' : p.val∈lemma56PaperPrimes D := by simpa only [lemma35_prime_windows_eq] using p.property
  rw [proposition71_prime_gcd_principal_split hD hL hp' hB₁ c a₁ a₂ ha₁,mul_add]

/-- Actual original ThetaOne to the principal and nonprincipal Section7
arithmetic means; the remaining estimates are conclusions still to be proved. -/
theorem proposition71_original_principal_nonprincipal_reduction :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-(proposition71PrincipalMean D c a₁ a₂+
        proposition71NonprincipalMean D c a₁ a₂)‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨N,hN,hbound⟩ := proposition71_original_gcd_reduction B₁ B₂ hB₁ hB₂ ε hε
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hND := (le_max_left _ _).trans hD
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right N ⌈Real.exp 2000⌉₊).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  rw [←proposition71_gcd_eq_principal_add_nonprincipal (by have := hN.trans hND; omega)
    hL hB₁.le c a₁ a₂ ha₁]
  exact hbound D hND χ hA c a₁ a₂ ha₁ ha₂

end ZhangLS.Spec
