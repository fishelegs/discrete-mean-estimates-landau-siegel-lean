import ZhangLS.Spec.ActualPhaseObjects

/-! The actual original zero sum with an analytic phase test, on a genuinely
constructed finite rectangle. Boundary separation, exact zero membership,
M simplicity, residue values and contour analyticity are proved internally.
The chosen rectangle is independent of the coefficient sequences and test.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set Filter MeasureTheory
open scoped Real Topology Classical
set_option maxHeartbeats 2000000

theorem actualPhase_rectangle_residue_identity {c : ℝ} (hc : 0 < c)
    (hcompatible : Lemma52CompatibleConstant c) :
    ∃ N : ℕ, lemma23SectionFourModulusThreshold ≤ N ∧ ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), N ≤ D → Lemma23InPsi1 χ ψ →
      ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y →
      ∃ lo hi : ℝ,
      |lo-((lemma23PaperCenter D).im-lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4 ∧
      |hi-((lemma23PaperCenter D).im+lemma23PaperL D ^ 405)| ≤ lemma44PaperAlpha D/4 ∧
      lo < hi ∧
      (∀ s : ℂ, Lemma81RectangleBoundary D lo hi s → Lemma59ZeroSeparated (D := D) ψ s (1/4)) ∧
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f {s : ℂ | 0 < s.im} →
      (2*(Real.pi : ℂ)*I)⁻¹ * lemma81RectangleIntegral
        (actualPhaseIntegrand D c ψ Y f)
        (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) lo hi =
        ∑ ρ ∈ lemma81ZeroFinset D ψ, actualPhaseResidue D c ψ Y f ρ := by
  obtain ⟨Nb,hbound⟩ := lemma81_uniform_actual_rectangle_boundaries
  obtain ⟨Nc,hcomp⟩ := hcompatible
  obtain ⟨Ns,hsection,hsmall⟩ := lemma52_exists_shift_threshold hc
  refine ⟨max Nb (max Nc Ns),hsection.trans
    ((le_max_right Nc Ns).trans (le_max_right Nb (max Nc Ns))),?_⟩
  intro D p _ χ ψ hD hψ Y hY
  have hDb := (le_max_left Nb (max Nc Ns)).trans hD
  have hDc := (le_max_left Nc Ns).trans ((le_max_right Nb (max Nc Ns)).trans hD)
  have hDs := (le_max_right Nc Ns).trans ((le_max_right Nb (max Nc Ns)).trans hD)
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hDs)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have ha := (lemma44_alpha_pos_le_one hL).1
  have haq := lemma51_alpha_le_quarter hL
  obtain ⟨lo,hi,hlo,hhi,horder,hzeros,hsep⟩ := hbound χ ψ hDb hψ
  refine ⟨lo,hi,hlo,hhi,horder,hsep,?_⟩
  intro f hf
  let K := Icc (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) ×ℂ Icc lo hi
  let Num := actualPhaseNumerator D c ψ Y f
  let M := lemma23DirichletNormalizedM ψ Y
  let S := lemma81ZeroFinset D ψ
  have hdom {s : ℂ} (hs : s ∈ K) : 0 < s.im ∧
      0 < s.im+lemma23PaperOffsetOne D c ∧
      0 < s.im+lemma23PaperOffsetTwo D c ∧
      0 < s.im+lemma23PaperOffsetThree D c := by
    have hclosed := lemma81_closed_rectangle_iff.mp hs
    have hh := lemma81_closed_rectangle_height hlo hhi hclosed
    have hsExt : Lemma51InExtendedRegion D s := ⟨hclosed.1,by
      linarith only [hh,haq,pow_nonneg hLp.le 405]⟩
    have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
    have hspos := hT.trans_le (lemma51_extended_region_data hL hsExt).2.2.1
    have hb := lemma52_offset_bounds hL hc (hsmall D hDs)
    exact ⟨hspos,by linarith only [hspos,hb.1.1],
      by linarith only [hspos,hb.2.1.1],by linarith only [hspos,hb.2.2.1]⟩
  have hNum : AnalyticOnNhd ℂ Num K := by
    intro s hs
    have hh := hdom hs
    exact actualPhase_numerator_analytic c ψ hψ.1.2.1 hψ.1.1.ne_one Y f hY
      (hf s hh.1) hh.2.1 hh.2.2.1 hh.2.2.2
  have hMa : AnalyticOnNhd ℂ M K := by
    intro s hs
    exact lemma81_actual_M_analytic ψ hψ.1.2.1 hψ.1.1.ne_one Y hY s (hdom hs).1
  have hmember (ρ : ℂ) : ρ ∈ S ↔ Lemma23InZeroWindow D ρ ∧ ψ.LFunction ρ = 0 :=
    lemma81_mem_original_zero_finset ψ (lemma59_family_character_nonprincipal ψ hψ.1) ρ
  have hzeroSet : ∀ s ∈ K, M s = 0 ↔ s ∈ S := by
    intro s hs
    have hYne := lemma52_actual_branch_ne_zero ψ hψ.1.2.1 hψ.1.1.ne_one Y hY (hdom hs).1
    constructor
    · intro hzM
      have hzL : ψ.LFunction s = 0 := (mul_eq_zero.mp hzM).resolve_left hYne
      have hopen : Lemma81OpenRectangle D lo hi s := by
        by_contra hnot
        have hboundary := lemma81_closed_not_open_is_boundary (lemma81_closed_rectangle_iff.mp hs) hnot
        have hbad := hsep s hboundary s hzL
        simp only [sub_self,norm_zero] at hbad
        linarith only [hbad,ha]
      exact (hmember s).mpr ⟨(hzeros s hzL).mp hopen,hzL⟩
    · intro hmem
      have hz := ((hmember s).mp hmem).2
      change Y s * ψ.LFunction s = 0
      rw [hz,mul_zero]
  have hinside : ∀ ρ ∈ S, ρ ∈ Ioo (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) ×ℂ Ioo lo hi := by
    intro ρ hρ
    have hh := (hmember ρ).mp hρ
    exact lemma81_open_rectangle_iff.mpr ((hzeros ρ hh.2).mpr hh.1)
  have hsimple : ∀ ρ ∈ S, deriv M ρ ≠ 0 := by
    intro ρ hρ
    have hh := (hmember ρ).mp hρ
    exact ((hcomp χ ψ hDc hψ).2.2 Y hY ρ hh.1 hh.2).1
  have hres := lemma81_finite_rectangle_residue_theorem Num M S
    (by linarith only [ha]) horder hNum hMa hzeroSet hinside hsimple
  have he : (fun s => Num s/M s) = actualPhaseIntegrand D c ψ Y f := by
    funext s
    exact (actualPhase_integrand_eq_quotient D c ψ Y f s).symm
  rw [he] at hres
  have hsum : (∑ ρ ∈ S, Num ρ/deriv M ρ) =
      ∑ ρ ∈ S, actualPhaseResidue D c ψ Y f ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact actualPhase_numerator_div_deriv D c ψ Y f ρ
  rw [hsum] at hres
  rw [hres]
  have hfactor : 2*(Real.pi : ℂ)*I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  rw [← mul_assoc,inv_mul_cancel₀ hfactor,one_mul]


/-- Original zero sum for a single C1 character, with the actual weight. -/
noncomputable def actualPhaseCZeroSum {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (Y : ℂ → ℂ) (a b : ℕ → ℂ) : ℂ :=
  ∑ ρ ∈ lemma81ZeroFinset D ψ,
    lemma23ActualCoefficient ψ Y D c ρ *
      (actualPhaseRoot χ ψ * (actualPhaseTwistZ χ ψ ρ)⁻¹ *
        lemma81Polynomial D a ψ ρ * lemma81Polynomial D b ψ ρ) * lemma81Omega D ρ

/-- Original T1 zero sum, with literal conjugation of J at the zero. -/
noncomputable def actualPhaseTZeroSum {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (Y : ℂ → ℂ) (a j : ℕ → ℂ) : ℂ :=
  ∑ ρ ∈ lemma81ZeroFinset D ψ,
    lemma23ActualCoefficient ψ Y D c ρ *
      (actualPhaseRoot χ ψ * lemma81Polynomial D a ψ ρ *
        conj (lemma81Polynomial D j ψ ρ)) * lemma81Omega D ρ

/-- Actual normalized C1: original good family, a, prime mass and c-star weights. -/
noncomputable def actualPhaseCOne {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ)
    (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (a b : ℕ → ℂ) : ℂ :=
  (∑ ψ ∈ lemma81GoodFamily χ, actualPhaseCZeroSum χ c ψ.2 (Y ψ) a b) /
    ((lemma171MainTerm χ * lemma33ActualPrimeMass D : ℝ) : ℂ)

/-- Actual normalized T1, without assuming normalization positivity or an energy estimate. -/
noncomputable def actualPhaseTOne {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ)
    (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (a j : ℕ → ℂ) : ℂ :=
  (∑ ψ ∈ lemma81GoodFamily χ, actualPhaseTZeroSum χ c ψ.2 (Y ψ) a j) /
    ((lemma171MainTerm χ * lemma33ActualPrimeMass D : ℝ) : ℂ)

/-- Upward finite vertical integral, with the exact complex normalization. -/
noncomputable def actualPhaseVertical (f : ℂ → ℂ) (σ lo hi : ℝ) : ℂ :=
  (2*(Real.pi : ℂ)*I)⁻¹ * I * ∫ t in lo..hi, f ((σ : ℂ)+(t : ℂ)*I)

/-- The two genuine horizontal edges, retaining the source Gaussian. -/
noncomputable def actualPhaseHorizontal (f : ℂ → ℂ) (a b lo hi : ℝ) : ℂ :=
  (2*(Real.pi : ℂ)*I)⁻¹ *
    ((∫ x in a..b, f ((x : ℂ)+(lo : ℂ)*I)) -
      (∫ x in a..b, f ((x : ℂ)+(hi : ℂ)*I)))

/-- Both vertical integrals are upward: the exact orientation is right minus left. -/
theorem actualPhase_rectangle_orientation (f : ℂ → ℂ) (a b lo hi : ℝ) :
    (2*(Real.pi : ℂ)*I)⁻¹ * lemma81RectangleIntegral f a b lo hi =
      actualPhaseVertical f b lo hi - actualPhaseVertical f a lo hi +
        actualPhaseHorizontal f a b lo hi := by
  unfold lemma81RectangleIntegral actualPhaseVertical actualPhaseHorizontal
  ring

/-- Criticality is recovered for the actual finite source zeros, rather than imposed. -/
theorem actualPhase_uniform_zero_critical :
    ∃ N : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), N ≤ D → Lemma23InPsi1 χ ψ →
      ∀ ρ ∈ lemma81ZeroFinset D ψ, ρ.re = 1/2 := by
  obtain ⟨c,hc,N,hzero⟩ := lemma59_uniform_extended_actual_product_zeros
  refine ⟨N,?_⟩
  intro D p _ χ ψ hD hψ ρ hρ
  have hz := (lemma81_mem_original_zero_finset ψ
    (lemma59_family_character_nonprincipal ψ hψ.1) ρ).mp hρ
  have hw : Lemma59ExtendedZeroOmega D ρ := ⟨hz.1.1,by linarith only [hz.1.2]⟩
  have hp : lemma48ActualProduct χ ψ ρ = 0 := by
    simp only [lemma48ActualProduct,hz.2,zero_mul]
  exact ((hzero χ ψ hD hψ).2.2 hw hp).1

/-- Simultaneous exact C1/T1 attachment for every coefficient pair on one
actual zero-avoiding rectangle. The only fixed choice is the source-compatible
shift constant. No contour identity, residue value, analytic estimate or
criticality assertion appears among the input hypotheses. -/
theorem actualPhase_uniform_C_T_rectangle {c : ℝ} (hc : 0 < c)
    (hcompatible : Lemma52CompatibleConstant c) :
    ∃ N : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), N ≤ D → Lemma23InPsi1 χ ψ →
      ∀ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y → ∃ lo hi : ℝ,
      |lo-((lemma23PaperCenter D).im-lemma23PaperL D^405)| ≤ lemma44PaperAlpha D/4 ∧
      |hi-((lemma23PaperCenter D).im+lemma23PaperL D^405)| ≤ lemma44PaperAlpha D/4 ∧
      lo < hi ∧
      (∀ s : ℂ, Lemma81RectangleBoundary D lo hi s →
        Lemma59ZeroSeparated (D := D) ψ s (1/4)) ∧
      ∀ a b j : ℕ → ℂ,
      (actualPhaseCZeroSum χ c ψ Y a b =
        actualPhaseVertical (actualPhaseIntegrand D c ψ Y (actualPhaseCTest χ ψ a b))
          (1/2+lemma44PaperAlpha D) lo hi -
        actualPhaseVertical (actualPhaseIntegrand D c ψ Y (actualPhaseCTest χ ψ a b))
          (1/2-lemma44PaperAlpha D) lo hi +
        actualPhaseHorizontal (actualPhaseIntegrand D c ψ Y (actualPhaseCTest χ ψ a b))
          (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) lo hi) ∧
      (actualPhaseTZeroSum χ c ψ Y a j =
        actualPhaseVertical (actualPhaseIntegrand D c ψ Y (actualPhaseTTest χ ψ a j))
          (1/2+lemma44PaperAlpha D) lo hi -
        actualPhaseVertical (actualPhaseIntegrand D c ψ Y (actualPhaseTTest χ ψ a j))
          (1/2-lemma44PaperAlpha D) lo hi +
        actualPhaseHorizontal (actualPhaseIntegrand D c ψ Y (actualPhaseTTest χ ψ a j))
          (1/2-lemma44PaperAlpha D) (1/2+lemma44PaperAlpha D) lo hi) := by
  obtain ⟨Nr,hNr,hr⟩ := actualPhase_rectangle_residue_identity hc hcompatible
  obtain ⟨Nz,hz⟩ := actualPhase_uniform_zero_critical
  refine ⟨max Nr Nz,?_⟩
  intro D p _ χ ψ hD hψ Y hY
  have hDr := (le_max_left Nr Nz).trans hD
  have hDz := (le_max_right Nr Nz).trans hD
  have hL := (lemma44_parameters_at_explicit_threshold (hNr.trans hDr)).1
  obtain ⟨lo,hi,hlo,hhi,horder,hsep,hres⟩ := hr χ ψ hDr hψ Y hY
  refine ⟨lo,hi,hlo,hhi,horder,hsep,?_⟩
  intro a b j
  constructor
  · have hh := hres (actualPhaseCTest χ ψ a b)
      (fun s hs => actualPhase_CTest_analytic χ ψ hL hψ.1 a b hs)
    rw [actualPhase_rectangle_orientation] at hh
    exact hh.symm
  · have hh := hres (actualPhaseTTest χ ψ a j)
      (fun s _ => actualPhase_TTest_analytic χ ψ a j s)
    rw [actualPhase_rectangle_orientation] at hh
    have he : (∑ ρ ∈ lemma81ZeroFinset D ψ,
        actualPhaseResidue D c ψ Y (actualPhaseTTest χ ψ a j) ρ) =
        actualPhaseTZeroSum χ c ψ Y a j := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      unfold actualPhaseResidue
      rw [actualPhase_TTest_on_critical_line χ ψ a j (hz χ ψ hDz hψ ρ hρ)]
    rw [he] at hh
    exact hh.symm

/-- The source provides a compatible shift constant; none needs to be postulated. -/
theorem actualPhase_exists_compatible_shift :
    ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c := by
  obtain ⟨c,hc,hcompatible,_⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible⟩

end ZhangLS.Spec
