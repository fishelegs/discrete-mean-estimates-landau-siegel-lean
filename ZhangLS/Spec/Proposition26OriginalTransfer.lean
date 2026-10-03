import ZhangLS.Spec.Proposition26GaussianEnergy
import ZhangLS.Spec.Lemma171MainLowerBound

/-! Original Proposition 2.6 with its actual H₂, J-defect, prime mass,
character, zeros and branches. Every norm input is discharged below. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex Finset Filter
open scoped Classical Topology

lemma proposition26_energy_nonneg {D:ℕ} (χ:RealPrimitiveCharacter D)
    (c:ℝ) (Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ)
    (hw:∀ψ∈lemma81GoodFamily χ,∀ρ∈lemma81ZeroFinset D ψ.2,0≤proposition26Weight c Y ψ ρ)
    (F:(ψ:lemma33CharacterIndex D)→ℂ→ℂ) : 0≤proposition26Energy χ c Y F := by
  exact sum_nonneg (fun ψ hψ => sum_nonneg (fun ρ hρ => mul_nonneg (hw ψ hψ ρ hρ) (sq_nonneg _)))

theorem proposition26_original_defect_energy_of_bv {c:ℝ} (hc:Lemma52CompatibleConstant c)
    (hNorm:Proposition26BVNormAt c) :
    ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
      ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
        ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
          (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
          proposition26Energy χ c Y (fun ψ s => proposition26JDefect χ ψ.2 s)≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ) := by
  obtain ⟨Ku,hKu,Nu,hNu,hu⟩ := proposition26_unsmoothing_energy_of_bv hc hNorm
  obtain ⟨Ks,hKs,Ns,hNs,hs⟩ := proposition26_smoothed_energy_of_bv hc hNorm
  obtain ⟨Nt,ht⟩ := proposition26_actual_defect_energy_split hc
  refine ⟨3*(2*Ku+Ks),by positivity,max Nu (max Ns (max Nt lemma23SectionFourModulusThreshold)),
    hNu.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  have hDu := (le_max_left _ _).trans hD
  have hr := (le_max_right _ _).trans hD
  have hDs := (le_max_left _ _).trans hr
  have hr' := (le_max_right _ _).trans hr
  have hDt := (le_max_left _ _).trans hr'
  have hsection := (le_max_right _ _).trans hr'
  have hL : 1≤lemma23PaperL D := by linarith only [(lemma44_parameters_at_explicit_threshold hsection).1]
  have hu' := hu D hDu χ hA Y hY
  have hu1 := hu'.1
  have hu2 := hu'.2
  have hs' := hs D hDs χ hA Y hY
  have hpow : lemma23PaperL D^(-86:ℤ)≤lemma23PaperL D^(-28:ℤ) :=
    zpow_le_zpow_right₀ hL (by norm_num)
  have hs'' := hs'.trans (mul_le_mul_of_nonneg_left hpow (by unfold lemma33ActualPrimeMass; positivity))
  apply (ht D hDt χ Y hY).trans
  calc
    _ ≤ 3*(Ku*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ)+
      Ks*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ)+
      Ku*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ)) := by gcongr
    _ = _ := by ring

/-- One genuine c supplies both the uniform BV norm and the actual J-defect
energy. Downstream applications can use the same c without an assumed norm. -/
theorem proposition26_original_defect_energy :
    ∃c:ℝ,0<c ∧ Lemma52CompatibleConstant c ∧ Proposition26BVNormAt c ∧
      ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
        ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
          ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
            (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
            proposition26Energy χ c Y (fun ψ s => proposition26JDefect χ ψ.2 s)≤
              K*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ) := by
  obtain ⟨c,hc,hcompat,hnorm⟩ := proposition26_uniform_bv_energy
  exact ⟨c,hc,hcompat,hnorm,proposition26_original_defect_energy_of_bv hcompat hnorm⟩

theorem proposition26_original_transfer_of_bv {c:ℝ} (hc:Lemma52CompatibleConstant c)
    (hNorm:Proposition26BVNormAt c) :
    ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
      ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
        ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
          (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
          |proposition26XiThreeStar χ c Y|≤
            K*lemma33ActualPrimeMass D*lemma23PaperL D^(-4:ℤ) := by
  obtain ⟨Kj,hKj,Nj,hNj,hj⟩ := proposition26_original_defect_energy_of_bv hc hNorm
  obtain ⟨Kh,hKh,Nh,hNh,hh⟩ := proposition26_H2_energy_of_bv hc hNorm
  obtain ⟨Nw,hw⟩ := proposition26_actual_weight_data hc
  refine ⟨Kj+Kh,by positivity,max Nj (max Nh (max Nw lemma23SectionFourModulusThreshold)),
    hNj.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  have hDj := (le_max_left _ _).trans hD
  have hr := (le_max_right _ _).trans hD
  have hDh := (le_max_left _ _).trans hr
  have hr' := (le_max_right _ _).trans hr
  have hDw := (le_max_left _ _).trans hr'
  have hsection := (le_max_right _ _).trans hr'
  have hL : 0< lemma23PaperL D := by linarith only [(lemma44_parameters_at_explicit_threshold hsection).1]
  have hdata := hw D hDw χ Y hY
  have hweights := fun ψ hψ ρ hρ => (hdata ψ hψ ρ hρ).2.1
  have hj' := hj D hDj χ hA Y hY
  have hh' := hh D hDh χ hA Y hY
  have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; positivity
  have heh := proposition26_energy_nonneg χ c Y hweights (fun ψ s => proposition26H2 χ ψ.2 s)
  have hscalar : Kj*Kh≤(Kj+Kh)^2 := by nlinarith only [sq_nonneg (Kj-Kh),mul_pos hKj hKh]
  have hsq : proposition26XiThreeStar χ c Y^2≤
      ((Kj+Kh)*lemma33ActualPrimeMass D*lemma23PaperL D^(-4:ℤ))^2 := by
    apply (proposition26_original_cauchy χ c Y hweights).trans
    calc
      _ ≤ (Kj*lemma33ActualPrimeMass D*lemma23PaperL D^(-28:ℤ))*
          (Kh*lemma33ActualPrimeMass D*lemma23PaperL D^20) :=
        mul_le_mul hj' hh' heh (by positivity)
      _ = (Kj*Kh)*(lemma33ActualPrimeMass D*lemma23PaperL D^(-4:ℤ))^2 := by
        simp only [zpow_neg,zpow_ofNat]
        field_simp [hL.ne']
      _ ≤ (Kj+Kh)^2*(lemma33ActualPrimeMass D*lemma23PaperL D^(-4:ℤ))^2 :=
        mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)
      _ = _ := by ring
  have hR : 0≤(Kj+Kh)*lemma33ActualPrimeMass D*lemma23PaperL D^(-4:ℤ) := by positivity
  apply (sq_le_sq₀ (abs_nonneg (proposition26XiThreeStar χ c Y)) hR).mp
  simpa only [sq_abs] using hsq

/-- The original quantitative Xi₃ estimate has no norm assumption. -/
theorem proposition26_original_quantitative :
    ∃c:ℝ,0<c ∧ Lemma52CompatibleConstant c ∧
      ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
        ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
          ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
            (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
            |proposition26XiThreeStar χ c Y|≤
              K*lemma33ActualPrimeMass D*lemma23PaperL D^(-4:ℤ) := by
  obtain ⟨c,hc,hcompat,hnorm,_hdefect⟩ := proposition26_original_defect_energy
  exact ⟨c,hc,hcompat,proposition26_original_transfer_of_bv hcompat hnorm⟩

/-- Original Proposition 2.6, uniformly relative to the actual a and actual
prime mass, using the proved original Section 17 lower bound for a. -/
theorem proposition26_proved : Proposition26Target := by
  obtain ⟨c,hc,hcompat,K,hK,Nq,hNq,hq⟩ := proposition26_original_quantitative
  obtain ⟨Na,hNa,ha⟩ := lemma171_actual_main_gt_half
  refine ⟨c,hc,hcompat,?_⟩
  intro ε hε
  have hlog : Tendsto (fun D:ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨Nl,hl⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop (max 1 (2*K/ε)))
  refine ⟨max Nq (max Na Nl),hNq.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  have hDq := (le_max_left _ _).trans hD
  have hr := (le_max_right _ _).trans hD
  have hDa := (le_max_left _ _).trans hr
  have hDl := (le_max_right _ _).trans hr
  have hLbig := hl D hDl
  have hL1 : 1≤lemma23PaperL D := (le_max_left _ _).trans hLbig
  have hLp : 0< lemma23PaperL D := by linarith
  have hpow : lemma23PaperL D≤lemma23PaperL D^4 := le_self_pow₀ hL1 (by norm_num)
  have hlarge : 2*K/ε≤lemma23PaperL D^4 := ((le_max_right _ _).trans hLbig).trans hpow
  have hbudget : K*lemma23PaperL D^(-4:ℤ)≤ε/2 := by
    rw [zpow_neg,zpow_ofNat,←div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos hLp 4)).mpr
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith only [h]
  have ha' := ha D hDa χ hA
  have hM : 0≤lemma33ActualPrimeMass D := by unfold lemma33ActualPrimeMass; positivity
  apply (hq D hDq χ hA Y hY).trans
  calc
    _ = (K*lemma23PaperL D^(-4:ℤ))*lemma33ActualPrimeMass D := by ring
    _ ≤ (ε/2)*lemma33ActualPrimeMass D := mul_le_mul_of_nonneg_right hbudget hM
    _ ≤ ε*lemma171MainTerm χ*lemma33ActualPrimeMass D := by
      apply mul_le_mul_of_nonneg_right _ hM
      calc
        ε/2 = ε*((1:ℝ)/2) := by ring
        _ ≤ ε*lemma171MainTerm χ := mul_le_mul_of_nonneg_left ha'.le hε.le

end ZhangLS.Spec
