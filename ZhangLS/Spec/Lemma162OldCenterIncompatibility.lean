import ZhangLS.Spec.Lemma162OldMainLower
import ZhangLS.Spec.Lemma162ActualOldValueWitness

/-! Bounded quantitative audit of the original unshifted quotient.
These are universal conditional statements. They assert neither existence of
an (A)-character nor failure of the paper's main theorem. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_old_main_eventually_large (C : ℝ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → 1< lemma23PaperL D ∧
      C/lemma23PaperL D^4 <
        lemma162OldMainLowerConstant/(1+Real.log (lemma23PaperL D))^12 := by
  let K := lemma162OldMainLowerConstant
  let Cplus := max C 0
  have hK : 0<K := lemma162_old_main_lower_constant_pos
  have hCplus : 0≤Cplus := le_max_right _ _
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := ht.eventually ((Real.isLittleO_pow_log_id_atTop (n:=12)).bound
    (by norm_num : (0:ℝ)<1))
  have hLL := (Real.tendsto_log_atTop.comp ht).eventually (eventually_ge_atTop 1)
  have hL := ht.eventually (eventually_ge_atTop (Cplus*4096/K+2))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (hlog.and (hLL.and hL))
  refine ⟨D₀,?_⟩
  intro D hD
  obtain ⟨hlog,hLL,hlarge⟩ := hD₀ D hD
  let L := lemma23PaperL D
  change 1≤Real.log L at hLL
  change ‖Real.log L^12‖≤1*‖L‖ at hlog
  have hL2 : 2≤L := by
    have hn : 0≤Cplus*4096/K := by positivity
    dsimp [L]
    linarith
  have hLp : 0<L := by linarith
  have hH : 0<1+Real.log L := by linarith
  have hlogpow : Real.log L^12≤L := by
    simpa only [id_eq,one_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by linarith : 0≤Real.log L) 12),
      abs_of_nonneg hLp.le] using hlog
  have hHpow : (1+Real.log L)^12 ≤ 4096*L := by
    calc
      _ ≤ (2*Real.log L)^12 := by gcongr; linarith
      _ = 4096*Real.log L^12 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogpow (by norm_num)
  have hstrict : Cplus*4096<K*L := by
    have hh := mul_le_mul_of_nonneg_left hlarge hK.le
    have he : K*(Cplus*4096/K+2) = Cplus*4096+2*K := by field_simp [hK.ne']
    rw [he] at hh
    change Cplus*4096+2*K≤K*L at hh
    linarith
  have hpower : L^2≤L^4 := by
    have hsq : 1≤L^2 := by nlinarith
    nlinarith [sq_nonneg (L^2-1)]
  have hcross : Cplus*(1+Real.log L)^12<K*L^4 := by
    calc
      _ ≤ Cplus*(4096*L) := mul_le_mul_of_nonneg_left hHpow hCplus
      _ < K*L^2 := by nlinarith [mul_lt_mul_of_pos_right hstrict hLp]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower hK.le
  refine ⟨by change 1<L; linarith,?_⟩
  have hh : Cplus/L^4 < K/(1+Real.log L)^12 :=
    (div_lt_div_iff₀ (pow_pos hLp 4) (pow_pos hH 12)).mpr hcross
  exact (div_le_div_of_nonneg_right (le_max_left C 0) (pow_nonneg hLp.le 4)).trans_lt hh

/-- C and the fixed positive c′ both precede one modulus threshold.
Every continuous extension of the actual old quotient then violates the
printed error bound, for each of the two original nonzero shifts. -/
theorem lemma162_paper_old_center_strict_error (C c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        ∀ U : ℂ → ℂ, ContinuousAt U 1 →
          (∀ s : ℂ, 1<s.re → U s =
            lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
              (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
                (riemannZeta s^3*dirichletLFunction χ s^3)) →
          C/lemma23PaperL D^4 < ‖U 1-lemma162CorrectedCenterMain χ‖ := by
  obtain ⟨D₁,hD₁,hzero⟩ := lemma162_paper_old_center_forced_zero c hc
  obtain ⟨D₂,hlarge⟩ := lemma162_old_main_eventually_large C
  refine ⟨max 3 (max lemma23SectionFourModulusThreshold (max D₁ D₂)),
    le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),?_⟩
  intro D hD χ j U hU hquot
  have h12 : max D₁ D₂≤D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hz := hzero D ((le_max_left _ _).trans h12) χ j U hU hquot
  have hh := hlarge D ((le_max_right _ _).trans h12)
  rw [hz,zero_sub,norm_neg]
  exact hh.2.trans_le (lemma162_old_main_lower χ hh.1)

/-- Source-scoped conditional incompatibility: assumption (A) is retained.
No witness satisfying (A), at any modulus, is asserted or constructed. -/
theorem lemma162_source_A_old_center_incompatibility (C c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 2, ∀ U : ℂ → ℂ, ContinuousAt U 1 →
          (∀ s : ℂ, 1<s.re → U s =
            lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
              (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
                (riemannZeta s^3*dirichletLFunction χ s^3)) →
          ¬ ‖U 1-lemma162CorrectedCenterMain χ‖≤C/lemma23PaperL D^4 := by
  obtain ⟨D₀,hD₀,hsection,h⟩ := lemma162_paper_old_center_strict_error C c hc
  refine ⟨D₀,hD₀,hsection,?_⟩
  intro D hD χ _hA j U hU hquot
  exact not_le_of_gt (h D hD χ j U hU hquot)

/-- The actual original analytic-continuation formulation implies the same
conditional failure at its center; no holomorphy of old U is supplied here. -/
theorem lemma162_source_A_old_continuation_incompatibility (C c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 2, ∀ U : ℂ → ℂ,
          Lemma162OriginalContinuation χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
            (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) U →
          ¬ ‖U 1-lemma162CorrectedCenterMain χ‖≤C/lemma23PaperL D^4 := by
  obtain ⟨D₀,hD₀,hsection,h⟩ := lemma162_source_A_old_center_incompatibility C c hc
  refine ⟨D₀,hD₀,hsection,?_⟩
  intro D hD χ hA j U hcont
  apply h D hD χ hA j U ((hcont.1 1 (by norm_num)).continuousAt)
  intro s hs
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hz : riemannZeta s≠0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hl : dirichletLFunction χ s≠0 := by
    unfold dirichletLFunction
    rw [DirichletCharacter.LFunction_eq_LSeries χ.chi hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ.chi hs
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 3 hz) (pow_ne_zero 3 hl))).mpr
  simpa only [mul_assoc] using (hcont.2 s hs).2

/-- The old quotient has an explicit continuous center extension, so the
continuous-extension premise is constructed for every actual character. -/
theorem lemma162_paper_old_actual_extension_strict_error (C c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        ContinuousAt (lemma162OldActualExtension χ (lemma52PaperBetaOne D c)
          (lemma162PaperShift D c j)) 1 ∧
        (∀ s : ℂ, 1<s.re →
          lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s =
            lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
              (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
                (riemannZeta s^3*dirichletLFunction χ s^3)) ∧
        C/lemma23PaperL D^4 <
          ‖lemma162OldActualExtension χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) 1-
            lemma162CorrectedCenterMain χ‖ := by
  obtain ⟨D₁,hD₁,hsection,herror⟩ := lemma162_paper_old_center_strict_error C c hc
  obtain ⟨D₂,hD₂,hext⟩ := lemma162_paper_corrected_analytic_bridge c hc
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),hsection.trans (le_max_left _ _),?_⟩
  intro D hD χ j
  have h1 := (le_max_left _ _).trans hD
  have h2 := (le_max_right _ _).trans hD
  have hh := hext D h2 χ j
  exact ⟨hh.2.2.1,hh.2.2.2.2,herror D h1 χ j _ hh.2.2.1 hh.2.2.2.2⟩

/-- The selected constant can be the very same compatible c′ of Lemma 5.2.
Compatibility does not provide existence of an (A)-character. -/
theorem lemma162_old_center_shared_constant :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∀ C : ℝ, ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
        ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
          ∀ j : Fin 2, ∀ U : ℂ → ℂ, ContinuousAt U 1 →
            (∀ s : ℂ, 1<s.re → U s =
              lemma162DirichletSeries χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
                (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c)) s /
                  (riemannZeta s^3*dirichletLFunction χ s^3)) →
            ¬ ‖U 1-lemma162CorrectedCenterMain χ‖≤C/lemma23PaperL D^4 := by
  obtain ⟨c,hc,hcompatible,C,hC,D₀,hrest⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,fun C => lemma162_source_A_old_center_incompatibility C c hc⟩

end ZhangLS.Spec
