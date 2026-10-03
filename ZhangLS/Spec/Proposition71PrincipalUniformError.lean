import ZhangLS.Spec.Proposition71PrincipalPrimeError
import ZhangLS.Spec.Proposition71OriginalSevenEleven

/-! The complete prime-summed principal contour error, uniformly for the
original bounded sequences. All arithmetic losses have already been summed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000

/-- The genuine principal mean reaches the actual residue arithmetic mean
with the original full prime phase and a uniform o(actualPrimeMass) error. -/
theorem proposition71_principal_residue_little_o {c : ℝ} (hc : 0<c)
    (B₁ B₂ : ℝ) (hB₁ : 0<B₁) (hB₂ : 0<B₂) (ε : ℝ) (hε : 0<ε) :
    ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀a₁ a₂ : ℕ → ℂ,
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖proposition71PrincipalMean D c a₁ a₂-proposition71ResidueArithmeticMean D c a₁ a₂‖≤
        ε*lemma33ActualPrimeMass D := by
  obtain ⟨Np,hNp,hprime⟩ := proposition71_principal_prime_residue_error hc
  let K := proposition71PrincipalContourConstant*B₁*B₂
  have hK : 0≤K := by have := proposition71_principal_contour_constant_pos; dsimp [K]; positivity
  obtain ⟨Nr,hNr,hrate⟩ := proposition71_principal_outer_rate K hK ε hε
  refine ⟨max Np Nr,hNp.trans (le_max_left _ _),?_⟩
  intro D hD a₁ a₂ ha₁ ha₂
  have hDp := (le_max_left _ _).trans hD
  have hDr := (le_max_right _ _).trans hD
  have hD2 : 2≤D := hNp.trans hDp
  have hD1 : (1 : ℝ)<D := by exact_mod_cast (show 1<D by omega)
  have hL : 0<lemma23PaperL D := Real.log_pos hD1
  let R := lemma23PaperL D^1642614*Real.exp (-(lemma23PaperL D)^(1/10 : ℝ))
  have hterm (p : lemma33PrimeIndex D) :
      ‖-I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
          proposition71PrimePrincipalMean D p.val c a₁ a₂-
        (-I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
          (∑j : Fin 3,proposition71ActualR D c j*(p.val : ℂ)^(1-lemma83PaperBeta D c j)*
            proposition71ArithmeticSum D c j a₁ a₂))‖≤K*(p.val : ℝ)*R := by
    have hp : p.val∈lemma56PaperPrimes D := by rw [←proposition71_prime_windows_equal]; exact p.property
    have hp0 := ((lemma56_mem_paper_primes D p.val).mp hp).1.pos
    letI : NeZero p.val := ⟨hp0.ne'⟩
    rw [←mul_sub,norm_mul,norm_mul,norm_neg,norm_I,lemma81_actual_phase_norm_one c hL,one_mul,one_mul]
    exact hprime D hDp p.val hp B₁ B₂ hB₁.le hB₂.le a₁ a₂ ha₁ ha₂
  unfold proposition71PrincipalMean proposition71ResidueArithmeticMean
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun p hp => hterm p)).trans
  have he : (∑p : lemma33PrimeIndex D,K*(p.val : ℝ)*R)=(K*R)*lemma33ActualPrimeMass D := by
    rw [←sum_mul,←mul_sum]
    unfold lemma33ActualPrimeMass
    exact mul_right_comm _ _ _
  rw [he]
  have hmass : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; positivity
  exact mul_le_mul_of_nonneg_right (hrate D hDr) hmass

end ZhangLS.Spec
