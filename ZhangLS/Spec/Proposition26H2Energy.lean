import ZhangLS.Spec.Proposition26UniformEnergy
import ZhangLS.Spec.Proposition26Conjugation
import ZhangLS.Spec.Proposition26RampProfiles
import ZhangLS.Spec.Lemma84Section8Cutoffs

/-! The actual H₂ energy needs only the proved coarse BV norm. Its original
P₂/P₃ cutoffs, powers and iota constants are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex ComplexConjugate Finset Filter
open scoped Classical Topology

lemma proposition26_smoothing_frequency_bound {D : ℕ} (hL : 3≤lemma23PaperL D) (μ : ℕ) :
    |(lemma82SmoothingBeta D μ).im|≤lemma23PaperL D^20 := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hquarter := lemma51_alpha_le_quarter hL
  have hnorm : ‖lemma82SmoothingBeta D μ‖≤1 := by
    unfold lemma82SmoothingBeta
    split_ifs <;>
      simp only [norm_div,norm_mul,norm_ofNat,norm_I,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ha] <;> nlinarith only [hquarter]
  exact (Complex.abs_im_le_norm _).trans (hnorm.trans (one_le_pow₀ (by linarith : 1≤lemma23PaperL D)))

lemma proposition26_iota_three_norm : ‖proposition26IotaThree‖≤3 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  norm_num [proposition26IotaThree]

lemma proposition26_iota_four_norm : ‖proposition26IotaFour‖≤3 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  norm_num [proposition26IotaFour]

/-- This application takes the BV norm already proved by
proposition26_uniform_bv_energy, rather than assuming a source H₂ mean. -/
theorem proposition26_H2_energy_of_bv {c : ℝ} (hc : Lemma52CompatibleConstant c)
    (hNorm : Proposition26BVNormAt c) :
    ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
      ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
        ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
          (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
          proposition26Energy χ c Y (fun ψ s => proposition26H2 χ ψ.2 s)≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^20 := by
  obtain ⟨K,hK,Nm,hNm,hm⟩ := hNorm 1 (by norm_num)
  obtain ⟨Nw,hw⟩ := proposition26_actual_weight_data hc
  obtain ⟨Nq,hq⟩ := eventually_atTop.mp lemma84_section8_cutoffs_eventually
  refine ⟨36*K,by positivity,max Nm (max Nw (max Nq lemma23SectionFourModulusThreshold)),
    hNm.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  have hDm := (le_max_left _ _).trans hD
  have hRest := (le_max_right _ _).trans hD
  have hDw := (le_max_left _ _).trans hRest
  have hRest' := (le_max_right _ _).trans hRest
  have hDq := (le_max_left _ _).trans hRest'
  have hsection := (le_max_right _ _).trans hRest'
  have hL := (lemma44_parameters_at_explicit_threshold hsection).1
  have hLp : 0< lemma23PaperL D := by linarith
  have hweights := hw D hDw χ Y hY
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (by positivity)
  have hq6 := (hq D hDq).2.2 6
  have hq7 := (hq D hDq).2.2 7
  have hX2 : 1<proposition26PaperP2 D := by
    simpa [lemma84Section8Cutoff,lemma84Section8P2,proposition26PaperP2] using hq7.1
  have hcut2 : proposition26PaperP2 D≤lemma81Cutoff D := by
    simpa [lemma84Section8Cutoff,lemma84Section8P2,proposition26PaperP2,lemma81Cutoff] using hq7.2.1.le
  have hX3p : 0<proposition26PaperP3 D := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hX3 : 1<proposition26PaperP3 D :=
    Real.one_lt_rpow (show 1<lemma23PaperP D from
      Real.one_lt_exp_iff.mpr (pow_pos hLp 9)) (by norm_num)
  have h3P1 : proposition26PaperP3 D≤lemma84Section8P1 D :=
    Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (249/500:ℝ)≤63/125)
  have hcut3 : proposition26PaperP3 D≤lemma81Cutoff D := by
    apply h3P1.trans
    simpa [lemma84Section8Cutoff,lemma81Cutoff] using hq6.2.1.le
  have hcomp (X:ℝ) (hX:1<X) (hcut:X≤lemma81Cutoff D) (μ:ℕ) :
      proposition26Energy χ c Y (fun ψ s => proposition26HComponent χ ψ.2 X μ s)≤
        K*lemma33ActualPrimeMass D*lemma23PaperL D^20 := by
    have hp := hm D hDm χ hA (lemma82SmoothingBeta D μ).im
      (proposition26_smoothing_frequency_bound hL μ)
      (fun n => (proposition26Ramp X n:ℂ)) (proposition26_ramp_variation hX)
      (proposition26_ramp_support hX hcut) Y hY
    have he := proposition26_energy_congr_on_zeros χ c Y
      (fun ψ s => proposition26HComponent χ ψ.2 X μ s)
      (fun ψ s => lemma81Polynomial D
        (proposition26TwistedCoefficient χ (lemma82SmoothingBeta D μ).im
          (fun n => (proposition26Ramp X n:ℂ))) ψ.2 s)
      (fun ψ hψ ρ hρ => by
        dsimp only
        rw [proposition26_HComponent_polynomial χ ψ.2 ρ hX hcut μ,norm_mul,
          proposition26_HComponent_phase_norm (by linarith : 0<X),one_mul])
    exact he.le.trans hp
  have h3 := hcomp _ hX3 hcut3 6
  have h2 := hcomp _ hX2 hcut2 7
  have hadd := proposition26_energy_add χ c Y
    (fun ψ hψ ρ hρ => (hweights ψ hψ ρ hρ).2.1)
    (fun ψ s => conj proposition26IotaThree*proposition26HComponent χ ψ.2 (proposition26PaperP3 D) 6 s)
    (fun ψ s => conj proposition26IotaFour*proposition26HComponent χ ψ.2 (proposition26PaperP2 D) 7 s)
  rw [proposition26_energy_homogeneity,proposition26_energy_homogeneity,
    Complex.norm_conj,Complex.norm_conj] at hadd
  change proposition26Energy χ c Y (fun ψ s => proposition26H2 χ ψ.2 s)≤_ at hadd
  apply hadd.trans
  have hm0 : 0≤K*lemma33ActualPrimeMass D*lemma23PaperL D^20 := by
    unfold lemma33ActualPrimeMass
    positivity
  have h3sq := pow_le_pow_left₀ (norm_nonneg _) proposition26_iota_three_norm 2
  have h4sq := pow_le_pow_left₀ (norm_nonneg _) proposition26_iota_four_norm 2
  calc
    _ ≤ 2*(‖proposition26IotaThree‖^2*(K*lemma33ActualPrimeMass D*lemma23PaperL D^20)+
      ‖proposition26IotaFour‖^2*(K*lemma33ActualPrimeMass D*lemma23PaperL D^20)) := by gcongr
    _ ≤ 2*((3:ℝ)^2*(K*lemma33ActualPrimeMass D*lemma23PaperL D^20)+
      (3:ℝ)^2*(K*lemma33ActualPrimeMass D*lemma23PaperL D^20)) := by gcongr
    _ = _ := by ring

end ZhangLS.Spec

/-! The literal constant-one polynomial is a supported χ-twisted indicator.
This controls Gaussian tails with the same proved BV norm. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

lemma proposition26_unit_profile_support {D : ℕ} (hcut : 1<lemma81Cutoff D) :
    ∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → proposition26Indicator 2 n=0 := by
  intro n hn
  have hn1 : (1:ℝ)<n := hcut.trans_le hn
  have hnNat : 1<n := by exact_mod_cast hn1
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hnNat
  simp only [proposition26Indicator,if_neg (not_lt_of_ge hn2)]

lemma proposition26_unit_polynomial {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (hcut : 1<lemma81Cutoff D) :
    lemma81Polynomial D (proposition26TwistedCoefficient χ 0 (proposition26Indicator 2)) ψ s=1 := by
  unfold lemma81Polynomial
  rw [sum_eq_single 1]
  · norm_num [proposition26TwistedCoefficient,proposition26Indicator]
  · intro n hn hn1
    have hnpos := ((proposition71_mem_indices D n).mp hn).1
    have hn2 : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
    simp [proposition26TwistedCoefficient,proposition26Indicator,not_lt_of_ge hn2]
  · intro hn
    exact (hn ((proposition71_mem_indices D 1).mpr ⟨by norm_num,by simpa only [Nat.cast_one] using hcut⟩)).elim

end ZhangLS.Spec
