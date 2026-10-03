import ZhangLS.Spec.Proposition71DivisorAggregateAttachment
import ZhangLS.Spec.Proposition71PhaseSummation

/-! Actual original (7.11), and reduction of ThetaOne to its true principal
arithmetic mean. The saving is applied only after the genuine (7.13) source
inequality, with every original beta, coefficient and strict cutoff retained. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3500000

lemma proposition71_nonprincipal_phase_factor {D : ℕ} (hL : 0<lemma23PaperL D)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71NonprincipalMean D c a₁ a₂=
      (-I*(lemma51PaperT0 D : ℂ)^lemma52PaperBetaThree D c)*
        (∑p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*
          proposition71PrimeNonprincipalMean D p c a₁ a₂) := by
  have hT : 0<lemma51PaperT0 D := pow_pos hL 519
  unfold proposition71NonprincipalMean lemma33PrimeIndex
  rw [←Finset.sum_subtype (lemma33PrimeWindow D) (fun _ => Iff.rfl)
    (fun p : ℕ => -I*(((p : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
      proposition71PrimeNonprincipalMean D p c a₁ a₂),lemma35_prime_windows_eq,mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) hT.le]
  simp only [Complex.ofReal_natCast]
  ring

lemma proposition71_nonprincipal_phase_norm {D : ℕ} (hL : 0<lemma23PaperL D)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    ‖proposition71NonprincipalMean D c a₁ a₂‖=
      ‖∑p∈lemma56PaperPrimes D,(p : ℂ)^lemma52PaperBetaThree D c*
        proposition71PrimeNonprincipalMean D p c a₁ a₂‖ := by
  have hT : 0<lemma51PaperT0 D := pow_pos hL 519
  rw [proposition71_nonprincipal_phase_factor hL c a₁ a₂,norm_mul,norm_mul,norm_neg,norm_I,
    Complex.norm_cpow_eq_rpow_re_of_pos hT]
  simp only [lemma52PaperBetaThree,Complex.mul_re,Complex.I_re,Complex.ofReal_re,
    zero_mul,Complex.I_im,Complex.ofReal_im,mul_zero,sub_self,Real.rpow_zero,one_mul]

/-- The actual printed (7.11), not merely the positive majorant on its right.
The constant c and fixed sequence bounds precede epsilon and the threshold. -/
theorem proposition71_original_seven_eleven :
    ∀c : ℝ, 0<c → ∀B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ε : ℝ, 0<ε →
      ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
        ∀χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
          ∀a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
            ‖∑p∈lemma56PaperPrimes D,(p : ℂ)^lemma52PaperBetaThree D c*
              proposition71PrimeNonprincipalMean D p c a₁ a₂‖≤ε*lemma33ActualPrimeMass D := by
  intro c hc B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨N,hN,hmajor⟩ := proposition71_original_seven_thirteen_majorant_little_o c hc B₁ hB₁
    (ε/B₂) (by positivity)
  refine ⟨max N ⌈Real.exp 2000⌉₊,hN.trans (le_max_left _ _),?_⟩
  intro D hD χ hA a₁ a₂ ha₁ ha₂
  have hND := (le_max_left _ _).trans hD
  have hD2 : 2≤D := hN.trans hND
  have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right N ⌈Real.exp 2000⌉₊).trans hD)
  have hL : 2000≤lemma23PaperL D := by
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 2000) he
  have hb := proposition71_original_seven_thirteen (by omega) hL hB₁.le hB₂.le c a₁ a₂ ha₁ ha₂.1
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left (hmajor D hND χ hA a₁ ha₁) hB₂.le
  rw [←lemma35_actual_prime_mass_eq] at hm
  convert hm using 1 <;> field_simp

/-- The same saving with the original complete -i(pt0)^beta3 phase. -/
theorem proposition71_original_nonprincipal_little_o :
    ∀c : ℝ, 0<c → ∀B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ε : ℝ, 0<ε →
      ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
        ∀χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
          ∀a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
            ‖proposition71NonprincipalMean D c a₁ a₂‖≤ε*lemma33ActualPrimeMass D := by
  intro c hc B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨N,hN,hbound⟩ := proposition71_original_seven_eleven c hc B₁ B₂ hB₁ hB₂ ε hε
  refine ⟨N,hN,?_⟩
  intro D hD χ hA a₁ a₂ ha₁ ha₂
  have hD1 : 1<(D : ℝ) := by exact_mod_cast (show 1<D by have := hN.trans hD; omega)
  rw [proposition71_nonprincipal_phase_norm (Real.log_pos hD1) c a₁ a₂]
  exact hbound D hD χ hA a₁ a₂ ha₁ ha₂

/-- Original ThetaOne is now reduced solely to its actual principal
arithmetic mean; the entire genuine nonprincipal contribution is paid. -/
theorem proposition71_original_principal_reduction :
    ∀c : ℝ, 0<c → ∀B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ε : ℝ, 0<ε →
      ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
        ∀χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
          ∀a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
            ‖lemma81ThetaOne χ c a₁ a₂-proposition71PrincipalMean D c a₁ a₂‖≤
              ε*lemma33ActualPrimeMass D := by
  intro c hc B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨Nf,hNf,hfront⟩ := proposition71_original_principal_nonprincipal_reduction B₁ B₂ hB₁ hB₂
    (ε/2) (by positivity)
  obtain ⟨Ne,hNe,herror⟩ := proposition71_original_nonprincipal_little_o c hc B₁ B₂ hB₁ hB₂
    (ε/2) (by positivity)
  refine ⟨max Nf Ne,hNf.trans (le_max_left _ _),?_⟩
  intro D hD χ hA a₁ a₂ ha₁ ha₂
  have hf := hfront D ((le_max_left _ _).trans hD) χ hA c a₁ a₂ ha₁ ha₂
  have he := herror D ((le_max_right _ _).trans hD) χ hA a₁ a₂ ha₁ ha₂
  have hsplit : lemma81ThetaOne χ c a₁ a₂-proposition71PrincipalMean D c a₁ a₂=
      (lemma81ThetaOne χ c a₁ a₂-(proposition71PrincipalMean D c a₁ a₂+
        proposition71NonprincipalMean D c a₁ a₂))+proposition71NonprincipalMean D c a₁ a₂ := by ring
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hf he).trans_eq (by ring))

end ZhangLS.Spec
