import ZhangLS.Spec.Lemma84BoundaryTotalBound
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Filter Topology
set_option maxHeartbeats 3000000

/-- The square of the log-T fifth power has the exact integer L exponent 11. -/
theorem lemma84_boundary_logT_tenth {D : ℕ} (hL : 0< lemma23PaperL D) :
    (Real.log (lemma56PaperT D))^10=lemma23PaperL D^11 := by
  rw [lemma56PaperT,Real.log_exp,←Real.rpow_natCast (lemma23PaperL D^(11/10:ℝ)) 10,
    ←Real.rpow_mul hL.le]
  norm_num only [Nat.cast_ofNat,show (11/10:ℝ)*10=11 by norm_num]
  exact Real.rpow_natCast _ 11

lemma lemma84_boundary_budget_square (L H B C : ℝ) (K : ℕ)
    (hL : L≠0) (hH : H^10=L^11) :
    (C*B^K*H^5*L^(-15:ℤ))^2=C^2*B^(2*K)*L^(-19:ℤ) := by
  have hb : (B^K)^2=B^(2*K) := by rw [←pow_mul]; congr 1; omega
  have hh : (H^5)^2=H^10 := by ring
  rw [mul_pow,mul_pow,mul_pow,hb,hh,hH]
  simp only [zpow_neg,zpow_ofNat]
  field_simp <;> ring

/-- Both original cutoff layers are o(α), using only genuine Perron, true
arithmetic band weights, actual G and the proved L′/Π bounds. -/
theorem lemma84_section8_boundary_little_o : Lemma84Section8BoundaryTarget := by
  intro c hc ε hε
  obtain ⟨Db,hDb,hbound⟩ := lemma84_boundary_total_quantitative c hc
  let C := lemma84BoundaryTotalConstant
  let K := lemma84BoundaryTotalExponent
  have hC : 0<C := lemma84_boundary_total_constant_pos
  have hep : 0<ε*Real.pi := mul_pos hε Real.pi_pos
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp := ht.eventually (lemma83_polylog_eventually_le (C^2/(ε*Real.pi)^2) (by positivity) (2*K))
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2≤D ∧ Db≤D ∧ 1≤lemma23PaperL D ∧
        (C^2/(ε*Real.pi)^2)*(1+9*Real.log (lemma23PaperL D))^(2*K)≤lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Db,ht.eventually_ge_atTop 1,hp]
      with D h2 hb h1 hp
    exact ⟨h2,hb,h1,hp⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hDD χ hA j
  obtain ⟨hD2,hDbD,hL1,hpoly⟩ := hD₀ D hDD
  have hLp : 0< lemma23PaperL D := by linarith
  have hB0 : 0≤1+9*Real.log (lemma23PaperL D) := by linarith [Real.log_nonneg hL1]
  have hpoly' : C^2*(1+9*Real.log (lemma23PaperL D))^(2*K)≤(ε*Real.pi)^2*lemma23PaperL D := by
    have hh := mul_le_mul_of_nonneg_left hpoly (sq_nonneg (ε*Real.pi))
    have he : (ε*Real.pi)^2*((C^2/(ε*Real.pi)^2)*(1+9*Real.log (lemma23PaperL D))^(2*K))=
        C^2*(1+9*Real.log (lemma23PaperL D))^(2*K) := by field_simp
    rwa [he] at hh
  have hbudgetSq :
      (C*(1+9*Real.log (lemma23PaperL D))^K*(Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ))^2≤
        (ε*lemma44PaperAlpha D)^2 := by
    rw [lemma84_boundary_budget_square _ _ _ _ _ hLp.ne' (lemma84_boundary_logT_tenth hLp)]
    have hh := mul_le_mul_of_nonneg_right hpoly' (show 0≤lemma23PaperL D^(-19:ℤ) by positivity)
    apply hh.trans_eq
    rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    simp only [zpow_neg,zpow_ofNat]
    field_simp <;> ring
  have hraw := (hbound D hDbD).2 χ hA j
  have halpha : 0≤ε*lemma44PaperAlpha D := by
    rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    positivity
  have hbudget0 : 0≤C*(1+9*Real.log (lemma23PaperL D))^K*
      (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) := by
    rw [lemma56PaperT,Real.log_exp]
    positivity
  have hbudget := (sq_le_sq₀ hbudget0 halpha).mp hbudgetSq
  exact hraw.trans hbudget

/-- The complete second-inner replacement is now proved for the actual source
S_j. This closes the effect of the weakened 8.4 error on this step only. -/
theorem lemma84_section8_full_xi_replacement_little_o :
    ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ j : Fin 3,
          ‖lemma84Section8SourceSum χ c j-lemma84Section8FullSecondMain χ c j‖≤ε*lemma44PaperAlpha D := by
  intro c hc ε hε
  obtain ⟨Di,hDi,hi⟩ := lemma84_section8_full_second_of_boundary lemma84_section8_boundary_little_o c hc ε hε
  obtain ⟨Dq,hDq⟩ := eventually_atTop.mp lemma84_section8_cutoffs_eventually
  refine ⟨max Di Dq,le_trans hDi (le_max_left _ _),?_⟩
  intro D hD χ hA j
  have hq := hDq D (le_trans (le_max_right _ _) hD)
  rw [←lemma84_section8_raw_source_exact χ c j (hq.2.2 6).1 (hq.2.2 7).1]
  exact hi D (le_trans (le_max_left _ _) hD) χ hA j

end ZhangLS.Spec
