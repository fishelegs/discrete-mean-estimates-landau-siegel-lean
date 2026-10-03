import ZhangLS.Spec.Proposition71ResidueNormalization
import ZhangLS.Spec.Proposition71PhaseSummation
import ZhangLS.Spec.Lemma81KernelBoundaryGrowth

/-! The actual three local residues, summed with the original full prime
phase, give exactly the original main coefficients up to O(E). No global
principal contour formula is assumed or asserted by this module. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000

noncomputable def proposition71ResidueArithmeticMean (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑p : lemma33PrimeIndex D, -I*(((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c*
    ∑j : Fin 3, proposition71ActualR D c j*(p.val : ℂ)^(1-lemma83PaperBeta D c j)*
      proposition71ArithmeticSum D c j a₁ a₂

lemma proposition71_residue_weighted_sum (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    (∑j : Fin 3,proposition71ResidueWeight j/(lemma44PaperAlpha D : ℂ)*
      proposition71ArithmeticSum D c j a₁ a₂)=
      (lemma44PaperAlpha D : ℂ)⁻¹*((1/2 : ℂ)*proposition71ArithmeticSum D c 0 a₁ a₂+
        2*proposition71ArithmeticSum D c 1 a₁ a₂+
        (3/2 : ℂ)*proposition71ArithmeticSum D c 2 a₁ a₂) := by
  rw [Fin.sum_univ_three]
  simp only [proposition71ResidueWeight,if_true,
    if_neg (by decide : (1 : Fin 3)≠0),if_neg (by decide : (2 : Fin 3)≠0),
    if_neg (by decide : (2 : Fin 3)≠1)]
  ring

lemma proposition71_main_term_prime_sum (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71MainTerm D c a₁ a₂=
      ∑p : lemma33PrimeIndex D,(p.val : ℂ)*(∑j : Fin 3,
        proposition71ResidueWeight j/(lemma44PaperAlpha D : ℂ)*proposition71ArithmeticSum D c j a₁ a₂) := by
  simp_rw [proposition71_residue_weighted_sum]
  rw [←sum_mul]
  have hm : (∑p : lemma33PrimeIndex D,(p.val : ℂ))=(lemma33ActualPrimeMass D : ℂ) := by
    simp only [lemma33ActualPrimeMass,Complex.ofReal_sum,Complex.ofReal_natCast]
  rw [hm]
  unfold proposition71MainTerm
  ring

/-- Complete residue/phase normalization at the actual original E scale,
with one c-dependent constant chosen independently of epsilon and coefficients. -/
theorem proposition71_actual_residue_mean_error {c : ℝ} (hc : 0<c) :
    ∃C : ℝ,0<C ∧ ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀a₁ a₂ : ℕ → ℂ,
      ‖proposition71ResidueArithmeticMean D c a₁ a₂-proposition71MainTerm D c a₁ a₂‖≤
        C*proposition71ErrorScale D c a₁ a₂ := by
  obtain ⟨C,hC,Nr,hNr,hr⟩ := proposition71_actual_residue_normalization hc
  obtain ⟨Np,hp⟩ := proposition71_actual_arithmetic_phase_budget hc
  refine ⟨C+2,by positivity,max Nr (max Np ⌈Real.exp 1⌉₊),hNr.trans (le_max_left _ _),?_⟩
  intro D hD a₁ a₂
  have hDr : Nr≤D := (le_max_left _ _).trans hD
  have hDp : Np≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDe : ⌈Real.exp 1⌉₊≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hL : 1≤lemma23PaperL D := by
    have he : Real.exp 1≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hDe)
    simpa only [lemma23PaperL,Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  let S := fun j : Fin 3 => proposition71ArithmeticSum D c j a₁ a₂
  let φ := fun p : lemma33PrimeIndex D =>
    (((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c
  let M := ∑j : Fin 3,proposition71ResidueWeight j/(lemma44PaperAlpha D : ℂ)*S j
  let A := ∑p : lemma33PrimeIndex D,-φ p*(p.val : ℂ)*M
  have hSn : 0≤∑j : Fin 3,‖S j‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have hmass : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; positivity
  have hterm (p : lemma33PrimeIndex D) :
      ‖-I*φ p*(∑j : Fin 3,proposition71ActualR D c j*(p.val : ℂ)^(1-lemma83PaperBeta D c j)*S j)-
        (-φ p*(p.val : ℂ)*M)‖≤C*(p.val : ℝ)*lemma23PaperL D*(∑j : Fin 3,‖S j‖) := by
    have hpS : p.val∈lemma56PaperPrimes D := by rw [←proposition71_prime_windows_equal]; exact p.property
    have hp0 := ((lemma56_mem_paper_primes D p.val).mp hpS).1.pos
    have hpC : (p.val : ℂ)≠0 := by exact_mod_cast hp0.ne'
    letI : NeZero p.val := ⟨hp0.ne'⟩
    have hφ : ‖φ p‖=1 := lemma81_actual_phase_norm_one c (by linarith)
    have hnorm := fun j : Fin 3 => hr D hDr p.val hpS j
    have hpower (j : Fin 3) : (p.val : ℂ)^(1-lemma83PaperBeta D c j)=
        (p.val : ℂ)*(p.val : ℂ)^(-lemma83PaperBeta D c j) := by
      rw [sub_eq_add_neg,Complex.cpow_add _ _ hpC,Complex.cpow_one]
    have he : -I*φ p*(∑j : Fin 3,proposition71ActualR D c j*(p.val : ℂ)^(1-lemma83PaperBeta D c j)*S j)-
        (-φ p*(p.val : ℂ)*M)=
      -φ p*(p.val : ℂ)*∑j : Fin 3,
        (I*proposition71ActualR D c j*(p.val : ℂ)^(-lemma83PaperBeta D c j)-
          proposition71ResidueWeight j/(lemma44PaperAlpha D : ℂ))*S j := by
      dsimp only [M]
      simp only [Fin.sum_univ_three,hpower]
      ring
    rw [he,norm_mul,norm_mul,norm_neg,hφ,Complex.norm_natCast,one_mul]
    have hinner : ‖∑j : Fin 3,
        (I*proposition71ActualR D c j*(p.val : ℂ)^(-lemma83PaperBeta D c j)-
          proposition71ResidueWeight j/(lemma44PaperAlpha D : ℂ))*S j‖≤
        C*lemma23PaperL D*(∑j : Fin 3,‖S j‖) := by
      apply (norm_sum_le _ _).trans
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hnorm j) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)).trans_eq (by ring)
  have hres : ‖proposition71ResidueArithmeticMean D c a₁ a₂-A‖≤C*proposition71ErrorScale D c a₁ a₂ := by
    unfold proposition71ResidueArithmeticMean
    dsimp only [A]
    rw [←sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply le_trans (sum_le_sum (fun p hp => hterm p))
    have hs : (∑p : lemma33PrimeIndex D,C*(p.val : ℝ)*lemma23PaperL D*(∑j : Fin 3,‖S j‖))=
        C*lemma33ActualPrimeMass D*lemma23PaperL D*(∑j : Fin 3,‖S j‖) := by
      simp only [←sum_mul,←mul_sum,lemma33ActualPrimeMass]
    rw [hs]
    have hL2 : lemma23PaperL D≤lemma23PaperL D^2 := by nlinarith
    dsimp [proposition71ErrorScale,S]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hL2 (mul_nonneg hC.le hmass)) hSn
    convert hh using 1 <;> ring
  have hphase : ‖A-proposition71MainTerm D c a₁ a₂‖≤2*proposition71ErrorScale D c a₁ a₂ := by
    have hm := proposition71_main_term_prime_sum D c a₁ a₂
    have he : A-proposition71MainTerm D c a₁ a₂=
      -(∑p : lemma33PrimeIndex D,(φ p+1)*(p.val : ℂ)*M) := by
      rw [hm]
      dsimp only [A,M,S]
      rw [←sum_sub_distrib,←sum_neg_distrib]
      apply sum_congr rfl
      intro p hp
      ring
    rw [he,norm_neg]
    dsimp only [M,S]
    simp_rw [proposition71_residue_weighted_sum]
    have hb := hp D hDp a₁ a₂
    convert hb using 1 <;> dsimp [φ] <;> congr 1 <;> apply sum_congr rfl <;> intros <;> ring
  have hs : proposition71ResidueArithmeticMean D c a₁ a₂-proposition71MainTerm D c a₁ a₂=
      (proposition71ResidueArithmeticMean D c a₁ a₂-A)+(A-proposition71MainTerm D c a₁ a₂) := by ring
  rw [hs]
  exact (norm_add_le _ _).trans ((add_le_add hres hphase).trans_eq (by ring))

end ZhangLS.Spec
