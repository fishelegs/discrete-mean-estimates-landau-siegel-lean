import ZhangLS.Spec.Section15PaperBridge
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter Metric Set
open scoped Topology
set_option maxHeartbeats 2000000

/-- The punctured-limit coefficient equals the genuine normalized contour
residue on every sufficiently small circle around the original pole. -/
lemma section15_actual_small_circle_residue {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (β : Fin 3 → ℂ) (hβ : ∀ k, (β k).re=0)
    {B : ℝ} (hB : 0<B) (j : Fin 3) (hβ0 : β j≠0)
    (hinj : Function.Injective β)
    (hZ : zetaPoleRemoved (1-β j)≠0) (hL : dirichletLFunction χ (1-β j)≠0) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      (2*Real.pi*I:ℂ)⁻¹*circleIntegral (section15ActualIntegrand χ β B) (-β j) r=
        section15ActualR χ β B j := by
  let a := -β j
  let N := section15PoleNumerator χ β B j
  have hg1 : β (j+1)-β j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hinj he; fin_cases j <;> simp at he')
  have hg2 : β (j+2)-β j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hinj he; fin_cases j <;> simp at he')
  have hN : AnalyticAt ℂ N a := section15_pole_numerator_analytic χ hD β hβ hB j hZ hL hg1 hg2
  obtain ⟨R,hR,hNR⟩ := hN.exists_ball_analyticOnNhd
  have heq := section15_actual_local_factorization χ β hβ B j hβ0 hinj
  obtain ⟨S,hS,hES⟩ := Metric.mem_nhdsWithin_iff.mp heq
  refine ⟨min R S/2,by positivity,?_⟩
  intro r hr hsmall
  have hrR : r<R := by have := min_le_left R S; linarith
  have hrS : r<S := by have := min_le_right R S; linarith
  have hd : DifferentiableOn ℂ N (closedBall a r) := by
    intro s hs
    exact (hNR s (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hs).trans_lt hrR))).differentiableAt.differentiableWithinAt
  have hci := hd.circleIntegral_sub_inv_smul (w := a) (by simp [hr])
  have hpi : (2*Real.pi*I:ℂ)≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hcongr : circleIntegral (section15ActualIntegrand χ β B) a r=
      circleIntegral (fun s : ℂ => (s-a)⁻¹ • N s) a r := by
    apply circleIntegral.integral_congr hr.le
    intro s hs
    have hsd : dist s a=r := Metric.mem_sphere.mp hs
    have hsa : s≠a := by intro he; simp [he] at hsd; linarith
    have hsS : s∈ball a S := Metric.mem_ball.mpr (hsd.trans_lt hrS)
    have hh := hES ⟨hsS,by simpa [a] using hsa⟩
    change section15ActualIntegrand χ β B s=N s/(s+β j) at hh
    rw [hh]
    simp only [a,sub_neg_eq_add,smul_eq_mul,div_eq_mul_inv,mul_comm]
  change (2*Real.pi*I:ℂ)⁻¹*circleIntegral (section15ActualIntegrand χ β B) a r=_
  rw [hcongr,hci,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hpi,one_mul]
  exact (section15_actual_residue_limit χ hD β hβ hB j hβ0 hinj hZ hL).limUnder_eq.symm

lemma section15_actual_geometric_nonzero {D : ℕ} {c : ℝ}
    (hD : 1<D) (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    section15Geometric (lemma83PaperBeta D c) (lemma61PaperP4 D) j≠0 := by
  have hdata := section15_actual_shift_data hL hc hsmall
  have hg1 : lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hdata.2 he; fin_cases j <;> simp at he')
  have hg2 : lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hdata.2 he; fin_cases j <;> simp at he')
  unfold section15Geometric
  apply mul_ne_zero (div_ne_zero (mul_ne_zero (hdata.1 0) (hdata.1 1)) (mul_ne_zero hg1 hg2))
  intro he
  exact (Complex.ofReal_ne_zero.mpr (lemma61_P4_pos hD).ne') ((Complex.cpow_eq_zero_iff _ _).mp he).1

/-- For the genuine shifts the contour residue is nonzero: these are true
simple poles, not removable singularities disguised by an algebraic formula. -/
lemma section15_actual_pole_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hδ : ‖lemma54PaperDeltaMellin D 1-1‖≤(lemma54Constant*Real.pi)*lemma23PaperL D^(-6:ℤ))
    (hbudget : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/1024) (j : Fin 3) :
    section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j≠0 := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 3≤lemma23PaperL D := by
    have := lemma57_log_ge_ten_million hDN
    dsimp [lemma23PaperL]
    linarith only [this]
  have hb : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2 := hbudget.trans (by norm_num)
  have hdata := section15_actual_shift_data hL hc hsmall
  have hn := section15_actual_denominators_nonzero χ hDN hA hc hsmall hb j
  have herr := section15_actual_correction_error χ hDN hA hc hsmall hδ hb j
  have he1 : (255*section15FactorConstant)*lemma23PaperL D^(-6:ℤ)<1 := by nlinarith only [hbudget]
  have hcorr := section15_ne_zero_of_near_one herr he1
  have he := section15_exact_residue_product χ hD (lemma83PaperBeta D c) (lemma83_beta_re D c)
    (lemma61_P4_pos hD) j hdata.1 hdata.2 hn.2.2 hn.2.1 hn.1
  have hg := section15_actual_geometric_nonzero hD hL hc hsmall j
  exact (mul_ne_zero_iff.mp (he ▸ mul_ne_zero hg hcorr)).2

/-- Full local certificate: an analytic, nonvanishing pole numerator gives the
original (15.16) on a punctured neighborhood; every small contour has exactly
this actual residue. All denominator conditions follow from original (A). -/
theorem section15_actual_simple_pole_certificates {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      let β := lemma83PaperBeta D c
      let B := lemma61PaperP4 D
      AnalyticAt ℂ (section15PoleNumerator χ β B j) (-β j) ∧
      section15PoleNumerator χ β B j (-β j)=section15ActualR χ β B j ∧
      section15ActualR χ β B j≠0 ∧
      (section15ActualIntegrand χ β B =ᶠ[𝓝[≠] (-β j)]
        (fun s => section15PoleNumerator χ β B j s/(s+β j))) ∧
      ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
        (2*Real.pi*I:ℂ)⁻¹*circleIntegral (section15ActualIntegrand χ β B) (-β j) r=
          section15ActualR χ β B j := by
  obtain ⟨D₁,hsection,hshift⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨D₂,hδ⟩ := section15_actual_delta_error_threshold
  obtain ⟨D₃,hbudget⟩ := section15_budget_threshold
  refine ⟨max 3 (max lemma57ExplicitModulusThreshold (max D₁ (max D₂ D₃))),le_max_left _ _,?_⟩
  intro D hD χ hA j
  dsimp only
  have hDN : lemma57ExplicitModulusThreshold≤D := by omega
  have hD1 : D₁≤D := by omega
  have hD2 : D₂≤D := by omega
  have hD3 : D₃≤D := by omega
  have hD' := lemma57_one_lt_of_explicit_threshold hDN
  have hb := hbudget D hD3
  have hsmall := hshift D hD1
  have hdata := section15_actual_shift_data (hδ D hD2).1 hc hsmall
  have hn := section15_actual_denominators_nonzero χ hDN hA hc hsmall (hb.trans (by norm_num)) j
  have hg1 : lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hdata.2 he; fin_cases j <;> simp at he')
  have hg2 : lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have he' := hdata.2 he; fin_cases j <;> simp at he')
  refine ⟨section15_pole_numerator_analytic χ hD' _ (lemma83_beta_re D c) (lemma61_P4_pos hD') j hn.2.2 hn.2.1 hg1 hg2,?_,?_,?_,?_⟩
  · exact (section15_actual_residue_limit χ hD' _ (lemma83_beta_re D c) (lemma61_P4_pos hD') j (hdata.1 j) hdata.2 hn.2.2 hn.2.1).limUnder_eq.symm
  · exact section15_actual_pole_nonzero χ hDN hA hc hsmall (hδ D hD2).2 hb j
  · exact section15_actual_local_factorization χ _ (lemma83_beta_re D c) _ j (hdata.1 j) hdata.2
  · exact section15_actual_small_circle_residue χ hD' _ (lemma83_beta_re D c) (lemma61_P4_pos hD') j (hdata.1 j) hdata.2 hn.2.2 hn.2.1

end ZhangLS.Spec
