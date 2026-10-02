import ZhangLS.Spec.Proposition71ExceptionalMoments
import ZhangLS.Spec.Proposition71PhaseSummation
import ZhangLS.Spec.Lemma56ActualPrimeMassNormalization

/-! # Original (7.5), for the actual exceptional character family

The cardinality bound is original Proposition 2.1; both moments and the prime
mass are actual proved inputs. The resulting error is uniform in c, s and both
bounded sequences, and normalized by the original prime mass.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable def proposition71ExceptionalPolynomialMean {D : ℕ}
    (χ : RealPrimitiveCharacter D) (c : ℝ) (a₁ a₂ : ℕ → ℂ) (s : ℂ) : ℝ :=
  ∑ ψ ∈ proposition21ActualPsi2Family χ,
    ‖proposition71TruncatedKappaPolynomial D c a₁ ψ.2 s‖*
      ‖lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)‖

lemma proposition71_exceptional_mean_nonneg {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) (s : ℂ) :
    0≤proposition71ExceptionalPolynomialMean χ c a₁ a₂ s :=
  sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Quantitative fourth-power budget: the original exceptional mean has a
saving ℒ⁻²² after taking the fourth power and normalizing by prime mass⁴. -/
theorem proposition71_exceptional_fourth_power_budget :
    ∃ K : ℝ, 0<K ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ c B₁ B₂ : ℝ, 0≤B₁ → 0≤B₂ → ∀ a₁ a₂ : ℕ → ℂ,
          Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
          ∀ s : ℂ, s.re=1/2 →
            proposition71ExceptionalPolynomialMean χ c a₁ a₂ s^4*lemma23PaperL D^22 ≤
              K*B₁^4*B₂^4*lemma33ActualPrimeMass D^4 := by
  obtain ⟨C,hC,Dc,hcount⟩ := proposition21_proved
  obtain ⟨Dm,hmass⟩ := lemma56_uniform_actual_prime_mass_lower
  let Cf : ℝ := (32+Real.pi^2)*3^25
  let Cg : ℝ := lemma81FourthMomentConstant
  have hCf : 0<Cf := by dsimp [Cf]; positivity
  have hCg : 0<Cg := lemma81_fourth_moment_constant_pos
  refine ⟨64*Cf^2*Cg*C,by positivity,
    max 2 (max Dc (max Dm lemma23SectionFourModulusThreshold)),le_max_left _ _,?_⟩
  intro D hD χ hA c B₁ B₂ hB₁ hB₂ a₁ a₂ ha₁ ha₂ s hs
  have h2 : 2≤D := (le_max_left _ _).trans hD
  have hDc : Dc≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDm : Dm≤D := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hDs : lemma23SectionFourModulusThreshold≤D := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hL := (lemma44_parameters_at_explicit_threshold hDs).1
  have hLp : 0<lemma23PaperL D := by linarith
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hM : 0≤lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hcard := hcount D hDc χ hA
  have hcard' : ((proposition21ActualPsi2Family χ).card : ℝ)*lemma23PaperL D^739 ≤
      C*lemma33ActualPrimeMass D := by
    have hh := mul_le_mul_of_nonneg_right hcard (pow_nonneg hLp.le 739)
    apply hh.trans_eq
    simp only [zpow_neg,zpow_ofNat,mul_assoc]
    rw [inv_mul_cancel₀ (pow_ne_zero 739 hLp.ne'),mul_one]
  have hm := hmass χ hDm (by omega) hA
  rw [←proposition71_actual_prime_masses_equal] at hm
  have hPm : lemma23PaperP D^2≤4*lemma33ActualPrimeMass D*lemma23PaperL D^77 := by
    have hh := (div_le_iff₀ (pow_pos hLp 77)).mp hm
    linarith
  have hP6 : lemma23PaperP D^6≤64*lemma33ActualPrimeMass D^3*lemma23PaperL D^231 := by
    have hh := pow_le_pow_left₀ (sq_nonneg (lemma23PaperP D)) hPm 3
    norm_num only [mul_pow,←pow_mul] at hh
    exact hh
  let f : lemma33CharacterIndex D → ℂ := fun ψ => proposition71TruncatedKappaPolynomial D c a₁ ψ.2 s
  let g : lemma33CharacterIndex D → ℂ := fun ψ => lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)
  let F : ℝ := ∑ ψ ∈ lemma33ActualFamily D, ‖f ψ‖^2
  let G : ℝ := ∑ ψ ∈ lemma33ActualFamily D, ‖g ψ‖^4
  have hF0 : 0≤F := sum_nonneg (fun _ _ => sq_nonneg _)
  have hG0 : 0≤G := sum_nonneg (fun _ _ => by positivity)
  have hf : F≤Cf*B₁^2*lemma23PaperP D^2*lemma23PaperL D^225 :=
    proposition71_actual_kappa_second_moment c hB₁ hL3 a₁ ha₁.1 hs
  have hg : G≤Cg*B₂^4*lemma23PaperP D^2*lemma23PaperL D^36 :=
    lemma81_actual_A_inverse_fourth_moment hB₂ hL3 a₂ ha₂
      (by rw [hs,sub_self,abs_zero]; exact (lemma44_alpha_pos_le_one hL3).1.le)
  have hhold := proposition71_exceptional_holder (proposition21ActualPsi2Family χ)
    (lemma33ActualFamily D) (filter_subset _ _) f g
  change proposition71ExceptionalPolynomialMean χ c a₁ a₂ s^4 ≤
    F^2*G*((proposition21ActualPsi2Family χ).card : ℝ) at hhold
  have hbig : proposition71ExceptionalPolynomialMean χ c a₁ a₂ s^4*lemma23PaperL D^739 ≤
      (64*Cf^2*Cg*C)*B₁^4*B₂^4*lemma33ActualPrimeMass D^4*lemma23PaperL D^717 := by
    calc
      _≤(F^2*G*((proposition21ActualPsi2Family χ).card : ℝ))*lemma23PaperL D^739 :=
        mul_le_mul_of_nonneg_right hhold (pow_nonneg hLp.le 739)
      _=F^2*G*(((proposition21ActualPsi2Family χ).card : ℝ)*lemma23PaperL D^739) := by ring
      _≤F^2*G*(C*lemma33ActualPrimeMass D) := by gcongr
      _≤(Cf*B₁^2*lemma23PaperP D^2*lemma23PaperL D^225)^2*
          (Cg*B₂^4*lemma23PaperP D^2*lemma23PaperL D^36)*(C*lemma33ActualPrimeMass D) := by gcongr
      _=(Cf^2*Cg*C*B₁^4*B₂^4*lemma33ActualPrimeMass D)*
          lemma23PaperP D^6*lemma23PaperL D^486 := by ring
      _≤(Cf^2*Cg*C*B₁^4*B₂^4*lemma33ActualPrimeMass D)*
          (64*lemma33ActualPrimeMass D^3*lemma23PaperL D^231)*lemma23PaperL D^486 := by gcongr
      _=_ := by ring
  apply (mul_le_mul_iff_right₀ (pow_pos hLp 717)).mp
  convert hbig using 1 <;> ring

/-- Original (7.5), with its actual family, original sequences and strict m<P²
support, uniformly for the entire critical line and normalized by prime mass. -/
theorem proposition71_original_seven_five :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
        ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
          ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ →
            Lemma81AdmissibleSequence D B₂ a₂ → ∀ s : ℂ, s.re=1/2 →
              proposition71ExceptionalPolynomialMean χ c a₁ a₂ s ≤ ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨K,hK,Db,hDb,hbudget⟩ := proposition71_exceptional_fourth_power_budget
  let H : ℝ := max 3 (K*B₁^4*B₂^4/ε^4)
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp H)
  refine ⟨max Db N,hDb.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂ s hs
  have hDbD := (le_max_left _ _).trans hD
  have hND := (le_max_right _ _).trans hD
  have hLD : H≤lemma23PaperL D := by
    have he : Real.exp H≤(D : ℝ) := hN.le.trans (by exact_mod_cast hND)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos H) he
  have hL : 3≤lemma23PaperL D := (le_max_left _ _).trans hLD
  have hLp : 0<lemma23PaperL D := by linarith
  have hL22 : lemma23PaperL D≤lemma23PaperL D^22 := le_self_pow₀ (by linarith) (by norm_num)
  have hKeps : K*B₁^4*B₂^4≤ε^4*lemma23PaperL D^22 := by
    have hh := (div_le_iff₀ (pow_pos hε 4)).mp ((le_max_right _ _).trans hLD)
    exact hh.trans (by nlinarith [pow_pos hε 4])
  have hb := hbudget D hDbD χ hA c B₁ B₂ hB₁.le hB₂.le a₁ a₂ ha₁ ha₂ s hs
  have hM : 0≤lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hp : proposition71ExceptionalPolynomialMean χ c a₁ a₂ s^4 ≤
      (ε*lemma33ActualPrimeMass D)^4 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hLp 22)).mp
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_right hKeps (pow_nonneg hM 4)
    convert hh using 1 <;> ring
  exact le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (mul_nonneg hε.le hM) hp

end ZhangLS.Spec
