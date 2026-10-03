import ZhangLS.Spec.Proposition71PrincipalFiniteError
import ZhangLS.Spec.Proposition71DivisorAggregateAttachment
import ZhangLS.Spec.Proposition71PrincipalOuterDecay
import ZhangLS.Spec.FiniteFourSumBound

/-! Full exterior error summation of the genuine principal contour,
retaining all coefficient and prime factors before the original prime mean. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 700000

lemma proposition71_principal_rate_reassociate (C A B H : ℝ) :
    C*A*B*H=C*(H*A*B) := by ring

lemma proposition71_principal_floor_log_budget {D : ℕ} (hL : 2≤lemma23PaperL D) :
    1≤⌊lemma23PaperP D⌋₊ ∧
    (1+Real.log (⌊lemma23PaperP D⌋₊ : ℝ))^163937*lemma23PaperL D^3244*
      Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))≤
        lemma23PaperL D^1642614*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
  have hLp : 0< lemma23PaperL D := by linarith
  have hP : 0< lemma23PaperP D := Real.exp_pos _
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hLp.le 9)
  have hX : 1≤⌊lemma23PaperP D⌋₊ := Nat.le_floor (by exact_mod_cast hP1)
  have hXR : (1 : ℝ)≤⌊lemma23PaperP D⌋₊ := by exact_mod_cast hX
  have hlog : Real.log (⌊lemma23PaperP D⌋₊ : ℝ)≤lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by linarith : (0 : ℝ)<⌊lemma23PaperP D⌋₊) (Nat.floor_le hP.le)
    simpa only [lemma23PaperP,Real.log_exp] using hh
  have hH0 : 0≤1+Real.log (⌊lemma23PaperP D⌋₊ : ℝ) := by
    have hh := Real.log_nonneg hXR
    linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hL9 : 1≤lemma23PaperL D^9 := one_le_pow₀ (n := 9) hL1
  have hH : 1+Real.log (⌊lemma23PaperP D⌋₊ : ℝ)≤lemma23PaperL D^10 := by
    calc
      _≤1+lemma23PaperL D^9 := by linarith only [hlog]
      _≤2*lemma23PaperL D^9 := by linarith only [hL9]
      _≤lemma23PaperL D*lemma23PaperL D^9 :=
        mul_le_mul_of_nonneg_right hL (pow_nonneg hLp.le _)
      _=lemma23PaperL D^9*lemma23PaperL D := mul_comm _ _
      _=lemma23PaperL D^10 := (pow_succ (lemma23PaperL D) 9).symm
  have hgen (N : ℕ) :
      (1+Real.log (⌊lemma23PaperP D⌋₊ : ℝ))^N*lemma23PaperL D^3244*
        Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))≤
      lemma23PaperL D^(10*N+3244)*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) := by
    have hpow := pow_le_pow_left₀ hH0 hH N
    calc
      _≤(lemma23PaperL D^10)^N*lemma23PaperL D^3244*
          Real.exp (-(lemma23PaperL D)^(1/10 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow (pow_nonneg hLp.le _)) (Real.exp_pos _).le
      _=_ := by
        rw [←pow_mul,←pow_add]
  have hinst := hgen 163937
  have hexp : (10*163937+3244 : ℕ)=1642614 := by decide
  rw [hexp] at hinst
  exact ⟨hX,hinst⟩


/-- Actual per-prime principal residue error, after the complete literal
four-variable arithmetic summation. -/
theorem proposition71_principal_prime_residue_error {c : ℝ} (hc : 0<c) :
    ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀p : ℕ,p∈lemma56PaperPrimes D →
      ∀B₁ B₂ : ℝ,0≤B₁ → 0≤B₂ → ∀a₁ a₂ : ℕ → ℂ,
        Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
        ‖proposition71PrimePrincipalMean D p c a₁ a₂-
          (∑j : Fin 3,proposition71ActualR D c j*(p : ℂ)^(1-lemma83PaperBeta D c j)*
            proposition71ArithmeticSum D c j a₁ a₂)‖≤
          proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ)*
            (lemma23PaperL D^1642614*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))) := by
  obtain ⟨N,hN,hfinite⟩ := proposition71_principal_prime_finite_error hc
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD p hp B₁ B₂ hB₁ hB₂ a₁ a₂ ha₁ ha₂
  have hND := (le_max_left _ _).trans hD
  have hD2 : 2≤D := hN.trans hND
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hp0 := ((lemma56_mem_paper_primes D p).mp hp).1.pos
  let S := lemma81PolynomialIndices D
  let X := ⌊lemma23PaperP D⌋₊
  let W := proposition71PrincipalExteriorWeight D
  let F := proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ)*lemma23PaperL D^3244*
    Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))
  have hF : 0≤F := by have := proposition71_principal_contour_constant_pos; dsimp [F]; positivity
  have hW : ∀d₁ d₂ k l₂,0≤W d₁ d₂ k l₂ :=
    proposition71_principal_exterior_weight_nonneg (by linarith only [hL] : 2≤lemma23PaperL D)
  have hX := proposition71_principal_floor_log_budget (by linarith only [hL] : 2≤lemma23PaperL D)
  have houter : (∑d₁∈S,∑d₂∈S,∑k∈S,∑l₂∈S,W d₁ d₂ k l₂)≤
      (1+Real.log (X : ℝ))^163937 := by
    apply (finiteFourSum_le_of_subset S (Icc 1 X) (proposition71_indices_subset_prime_floor D) W hW).trans
    exact proposition71_principal_envelope_outer_sum X hX.1 (proposition71_principal_left_re_lower (by linarith only [hL]))
  have hb := hfinite D hND p hp B₁ B₂ hB₁ hB₂ a₁ a₂ ha₁ ha₂
  apply hb.trans
  apply (mul_le_mul_of_nonneg_left houter hF).trans
  have hh := mul_le_mul_of_nonneg_left hX.2
    (show 0≤proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ) by have := proposition71_principal_contour_constant_pos; positivity)
  calc
    F*(1+Real.log (X : ℝ))^163937=
        (proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ))*
          ((1+Real.log (X : ℝ))^163937*lemma23PaperL D^3244*
            Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))) :=
      proposition71_principal_rate_reassociate
        (proposition71PrincipalContourConstant*B₁*B₂*(p : ℝ)) (lemma23PaperL D^3244)
        (Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))) ((1+Real.log (X : ℝ))^163937)
    _≤_ := hh

end ZhangLS.Spec
