import ZhangLS.Spec.Lemma84BoundaryInnerBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def lemma84BoundaryTotalExponent : ℕ := lemma84BoundaryInnerExponent+42
noncomputable def lemma84BoundaryTotalConstant : ℝ :=
  24*lemma84CompanionConstant*lemma84BoundaryInnerConstant*(1+‖lemma84Section8Iota‖)^2*
    Real.exp (12/Real.log 2)*Real.exp (2/Real.log 2)
lemma lemma84_boundary_total_constant_pos : 0< lemma84BoundaryTotalConstant := by
  unfold lemma84BoundaryTotalConstant
  positivity [lemma84_companion_constant_pos,lemma84_boundary_inner_constant_pos]

/-- Full two-layer boundary estimate for the actual Section 8 second-factor
replacement. The first factor and all mixed-cutoff/iota terms are kept actual. -/
theorem lemma84_boundary_total_quantitative :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      1≤lemma23PaperL D ∧ ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 3, ‖lemma84Section8Boundary χ c j‖≤
          lemma84BoundaryTotalConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryTotalExponent*
            (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) := by
  intro c hc
  obtain ⟨Di,hDi,hi⟩ := lemma84_section8_inner_bounds c hc
  obtain ⟨Dc,hDc,hcparams⟩ := lemma82_uniform_threshold c hc
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      Di≤D ∧ Dc≤D ∧ 2≤D ∧ 1< lemma23PaperL D ∧
      ∀ μ : ℕ, 1< lemma84Section8Cutoff D μ ∧
        lemma84Section8Cutoff D μ< lemma23PaperP D*lemma56PaperT D^(-2:ℤ) ∧
        lemma84Section8Cutoff D μ< lemma23PaperP D ∧
        (1/4)*lemma23PaperL D^9≤Real.log (lemma84Section8Cutoff D μ) from by
    filter_upwards [eventually_ge_atTop Di,eventually_ge_atTop Dc,lemma84_section8_cutoffs_eventually]
      with D hi hc hq
    exact ⟨hi,hc,hq⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).2.2.1,?_⟩
  intro D hDD
  obtain ⟨hDiD,hDcD,hD2,hL,hQs⟩ := hD₀ D hDD
  obtain ⟨_,hL2000,hsmall,_⟩ := hcparams D hDcD
  refine ⟨hL.le,?_⟩
  intro χ hA j
  have hLp : 0< lemma23PaperL D := by linarith
  have hH : 1≤Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]
    exact Real.one_le_rpow hL.le (by norm_num)
  have hT : 1≤lemma56PaperT D := by
    rw [lemma56PaperT,Real.one_le_exp_iff]
    positivity
  have hB0 : 0≤1+9*Real.log (lemma23PaperL D) := by linarith [Real.log_nonneg hL.le]
  let F := 4*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)*lemma23PaperL D^(-6:ℤ)
  let E := lemma84BoundaryInnerConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryInnerExponent*
    (Real.log (lemma56PaperT D))^4*lemma23PaperL D^(-9:ℤ)
  have hF0 : 0≤F := by dsimp [F]; positivity [lemma84_companion_constant_pos]
  have hE0 : 0≤E := by dsimp [E]; positivity [lemma84_boundary_inner_constant_pos]
  have hF (n : ℕ) (hn : 0<n) : ‖lemma84Section8FirstCombined χ c j n‖≤F := by
    have hh6 := ((hi D hDiD).2 χ hA j 6).1 n hn
    have hh7 := ((hi D hDiD).2 χ hA j 7).1 n hn
    unfold lemma84Section8FirstCombined
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left hh7 (norm_nonneg lemma84Section8Iota)
    dsimp [F]
    nlinarith only [hh6,hh]
  have hE (μ d r : ℕ) (hd : 0<d) (hr : 0<r) :
      ‖lemma84Section8BoundaryInner χ c j μ d r‖≤E :=
    lemma84_boundary_inner_bound χ (by omega) (by linarith) hc hsmall j μ d r hd hr
      (hQs μ).1 (hQs μ).2.1 (hQs μ).2.2.1 (hQs μ).2.2.2
  let W := lemma84WeightScale (lemma23PaperL D^9)
  let H := Real.log (lemma56PaperT D)
  let term := fun μ => ∑ a∈lemma84Section8Pairs D,
    lemma84Section8Weight χ c j a.1 a.2*lemma84Section8FirstCombined χ c j (a.1*a.2)*
      lemma84Section8BoundaryInner χ c j μ a.1 a.2
  have hterm (μ : ℕ) : ‖term μ‖≤(2*W*(2+H))*F*E := by
    let S := (lemma84Section8Pairs D).filter (fun a =>
      lemma84Section8Cutoff D μ/lemma56PaperT D≤(a.1*a.2:ℕ) ∧
      ((a.1*a.2:ℕ):ℝ)< lemma84Section8Cutoff D μ)
    have hid : term μ=∑ a∈S, lemma84Section8Weight χ c j a.1 a.2*
        lemma84Section8FirstCombined χ c j (a.1*a.2)*lemma84Section8BoundaryInner χ c j μ a.1 a.2 := by
      dsimp [term,S]
      rw [sum_filter]
      apply sum_congr rfl
      intro a ha
      split_ifs with hb
      · rfl
      · simp only [lemma84Section8BoundaryInner,if_neg hb,mul_zero]
    have hm := lemma84_actual_weight_layer χ c j S ⌊lemma84Section8P1 D⌋₊
      (fun a ha => (mem_filter.mp (mem_filter.mp ha).1).1)
      (lemma84_section8_cutoff_pos D μ) hT
      (show 1<lemma23PaperL D^9 from one_lt_pow₀ hL (by norm_num)) (by
        have hh := Real.log_lt_log (lemma84_section8_cutoff_pos D μ) (hQs μ).2.2.1
        simpa only [lemma23PaperP,Real.log_exp] using hh.le)
      (fun a ha => (mem_filter.mp ha).2)
    rw [hid]
    calc
      _ ≤ ∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖*F*E := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro a ha
        obtain ⟨hd,hr,_⟩ := (lemma84_section8_pairs_exact D a.1 a.2).mp (mem_filter.mp ha).1
        rw [norm_mul,norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hF _ (Nat.mul_pos hd hr)) (norm_nonneg _))
          (hE μ a.1 a.2 hd hr) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hF0)
      _ = (∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖)*F*E := by rw [sum_mul,sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hF0) hE0
  have hid : lemma84Section8Boundary χ c j=term 6+star lemma84Section8Iota*term 7 := by
    rw [lemma84_section8_boundary_exact]
    dsimp [term]
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    ring
  rw [hid]
  calc
    _ ≤ (2*W*(2+H))*F*E+‖lemma84Section8Iota‖*((2*W*(2+H))*F*E) := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_star]
      exact add_le_add (hterm 6) (mul_le_mul_of_nonneg_left (hterm 7) (norm_nonneg _))
    _ ≤ (2*W*(3*H))*F*E+‖lemma84Section8Iota‖*((2*W*(3*H))*F*E) := by
      have hW : 0≤W := lemma84_weight_scale_nonneg _
      have hpart := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (show 2+H≤3*H by dsimp [H]; linarith) (by positivity : 0≤2*W)) hF0) hE0
      exact add_le_add hpart (mul_le_mul_of_nonneg_left hpart (norm_nonneg _))
    _ = _ := by
      dsimp [W,H,F,E,lemma84WeightScale,lemma84BoundaryTotalConstant,lemma84BoundaryTotalExponent]
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      rw [pow_add]
      simp only [zpow_neg,zpow_ofNat]
      field_simp
      ring

end ZhangLS.Spec
