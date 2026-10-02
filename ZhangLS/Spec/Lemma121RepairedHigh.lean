import ZhangLS.Spec.Lemma121PhaseBudget

/-! # Explicitly repaired normalized high-range error
The printed tolerance 10^-5 is replaced by 10^-3. The change is deliberate:
Lemma121PhaseAudit proves that the printed pure-phase budget fails.
All arithmetic data, shifts, ranges, and the normalized error scale remain
unchanged. This file does not claim the two low-range branches. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

lemma lemma121_LDeriv_norm_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ) :
    (1:ℝ)/16≤‖LDerivAtOne χ‖ := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hh := lemma57_one_sixteenth_at_explicit_threshold χ hDN hA
  have hs := lemma57Scale_ge_one hD
  have hr := Complex.re_le_norm (LDerivAtOne χ)
  rw [← realLDerivAtOne_eq_re χ hD] at hr
  linarith

lemma lemma121_normalized_analytic_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    (hlarge : 160000*lemma121ExactHighConstant≤lemma23PaperL D)
    (c : ℝ) (j : Fin 3) (d : ℝ)
    (he : ‖lemma121Sum χ c j d-lemma121ExactMain χ c j d‖≤
      lemma121ExactHighConstant*lemma23PaperL D^(-15:ℤ)) :
    ‖(lemma121Sum χ c j d-lemma121ExactMain χ c j d)/
      (LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ))‖≤(1:ℝ)/10000 := by
  have hg := lemma121_endpoint_geometry hD hL
  have hQ : 0<Real.log (lemma121P1 D) := zero_lt_one.trans_le hg.2.2.2.2.1
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hder := lemma121_LDeriv_norm_lower χ hDN hA
  have hderp : 0<‖LDerivAtOne χ‖ := by linarith
  have hQupper : Real.log (lemma121P1 D)≤lemma23PaperL D^9 := by
    rw [lemma121_log_P1]
    nlinarith only [pow_nonneg hLp.le 9]
  have hinv : Real.log (lemma121P1 D)/‖LDerivAtOne χ‖≤16*lemma23PaperL D^9 := by
    apply (div_le_iff₀ hderp).mpr
    have hh := mul_le_mul_of_nonneg_right hder (pow_nonneg hLp.le 9)
    nlinarith only [hQupper,hh]
  have hnorm : ‖(lemma121Sum χ c j d-lemma121ExactMain χ c j d)/
      (LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ))‖≤
      16*lemma121ExactHighConstant*lemma23PaperL D^(-6:ℤ) := by
    rw [norm_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ,
      div_div_eq_mul_div]
    calc
      _ = ‖lemma121Sum χ c j d-lemma121ExactMain χ c j d‖*
          (Real.log (lemma121P1 D)/‖LDerivAtOne χ‖) := by ring
      _ ≤ (lemma121ExactHighConstant*lemma23PaperL D^(-15:ℤ))*(16*lemma23PaperL D^9) :=
        mul_le_mul he hinv (by positivity) (by positivity [lemma121_exact_high_constant_pos])
      _ = _ := by
        have hp : lemma23PaperL D^(-15:ℤ)*lemma23PaperL D^9=lemma23PaperL D^(-6:ℤ) := by
          rw [← zpow_natCast (lemma23PaperL D) 9,← zpow_add₀ hLp.ne']; norm_num
        rw [show (lemma121ExactHighConstant*lemma23PaperL D^(-15:ℤ))*(16*lemma23PaperL D^9)=
          (16*lemma121ExactHighConstant)*(lemma23PaperL D^(-15:ℤ)*lemma23PaperL D^9) by ring,hp]
  have hp : lemma23PaperL D^(-6:ℤ)≤lemma23PaperL D^(-1:ℤ) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  apply hnorm.trans
  calc
    _ ≤ 16*lemma121ExactHighConstant*lemma23PaperL D^(-1:ℤ) :=
      mul_le_mul_of_nonneg_left hp (by positivity [lemma121_exact_high_constant_pos])
    _ = 16*lemma121ExactHighConstant/lemma23PaperL D := by simp [div_eq_mul_inv]
    _ ≤ (1:ℝ)/10000 := by
      apply (div_le_iff₀ hLp).mpr
      linarith only [hlarge]

/-- Corrected normalized high-range target. The only changed numerical
conclusion is |ε|<10^-3 in place of the printed |ε|<10^-5. -/
def Lemma121RepairedHighTarget : Prop :=
  ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ d : ℕ,
      lemma121PDoublePrimeOne D<(d:ℝ) → (d:ℝ)<lemma121P2 D →
      ∃ ε : ℂ, ‖ε‖<(1:ℝ)/1000 ∧
        lemma121Sum χ c j d = LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)*
          (lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
            (Real.log ((d:ℝ)/lemma121PDoublePrimeOne D))+ε)

/-- Actual repaired high-range theorem, proved from original 5.7/5.8 and
actual Abel bounds. This is not the printed 10^-5 theorem. -/
theorem lemma121_repaired_high_proved : Lemma121RepairedHighTarget := by
  intro c hc
  obtain ⟨N,hN,hh⟩ := lemma82_uniform_threshold c hc
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp lemma121_tail_absorption_eventually
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp
    (ht.eventually_ge_atTop (160000*lemma121ExactHighConstant))
  let D₀ := max (max N M) (max K lemma57ExplicitModulusThreshold)
  have hNN : N≤D₀ := (le_max_left N M).trans (le_max_left _ _)
  have hMM : M≤D₀ := (le_max_right N M).trans (le_max_left _ _)
  have hKK : K≤D₀ := (le_max_left K _).trans (le_max_right _ _)
  have hDD : lemma57ExplicitModulusThreshold≤D₀ := (le_max_right K _).trans (le_max_right _ _)
  refine ⟨D₀,hN.trans hNN,?_⟩
  intro D hDN χ hA j d hdlo hdhi
  have hn := hh D (hNN.trans hDN)
  have hm := hM D (hMM.trans hDN)
  have hk := hK D (hKK.trans hDN)
  have hdN := hDD.trans hDN
  have hD : 1<D := by omega
  have he := lemma121_high_error_absorption χ hD hn.2.1 hA hc hn.2.2.1 hm j hdlo hdhi
  have hnorm := lemma121_normalized_analytic_error χ hD hn.2.1 hdN hA hk c j d he
  have hphase := lemma121_actual_phase_budget hD hn.2.1 hc hn.2.2.1 j hdlo hdhi
  let F := LDerivAtOne χ/(Real.log (lemma121P1 D):ℂ)
  let E := (lemma121Sum χ c j d-lemma121ExactMain χ c j d)/F
  let H := lemma121Phase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
    (Real.log ((d:ℝ)/lemma121PDoublePrimeOne D))
  let H₀ := lemma121LinearPhase (lemma82SmoothingBeta D 6) (lemma82PaperBeta D c j)
    (Real.log ((d:ℝ)/lemma121PDoublePrimeOne D))
  have hder : LDerivAtOne χ≠0 := norm_pos_iff.mp (by
    have hh := lemma121_LDeriv_norm_lower χ hdN hA
    linarith)
  have hQ : (Real.log (lemma121P1 D):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt
    (zero_lt_one.trans_le (lemma121_endpoint_geometry hD hn.2.1).2.2.2.2.1))
  have hF : F≠0 := div_ne_zero hder hQ
  refine ⟨E+(H-H₀),?_,?_⟩
  · apply (norm_add_le _ _).trans_lt
    have hE : ‖E‖≤(1:ℝ)/10000 := hnorm
    have hH : ‖H-H₀‖≤(101:ℝ)/125000 := hphase
    linarith
  · change lemma121Sum χ c j d=F*(H₀+(E+(H-H₀)))
    have hm : lemma121ExactMain χ c j d=F*H := rfl
    dsimp only [E]
    rw [hm]
    field_simp
    ring

end ZhangLS.Spec
