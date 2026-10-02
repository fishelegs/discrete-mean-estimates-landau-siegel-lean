import ZhangLS.Spec.Lemma84Section8WeightedInterior
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter Topology
set_option maxHeartbeats 2000000

/-- The repaired L^-5 estimate is fully compatible with the true Section 8
weighted interior: for every ε, its change in S_j is at most εα, uniformly in
χ and j with one threshold. Boundary replacement is deliberately not claimed. -/
theorem lemma84_section8_repaired_interior_little_o :
    ∀ c : ℝ, 0<c → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3,
        ‖lemma84Section8Raw χ c j-lemma84Section8Hybrid χ c j‖≤ε*lemma44PaperAlpha D := by
  intro c hc ε hε
  obtain ⟨Di,hDi,hi⟩ := lemma84_section8_interior_quantitative c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  let C : ℝ := lemma84InteriorConstant*Real.exp (12/Real.log 2)*Real.exp (2/Real.log 2)
  have hC : 0<C := by dsimp [C]; positivity [lemma84_interior_constant_pos]
  have hp := ht.eventually (lemma83_polylog_eventually_le C hC 42)
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2≤D ∧ Di≤D ∧ 1≤lemma23PaperL D ∧ (ε*Real.pi)⁻¹≤lemma23PaperL D ∧
      C*(1+9*Real.log (lemma23PaperL D))^42≤lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Di,
      ht.eventually_ge_atTop 1,ht.eventually_ge_atTop ((ε*Real.pi)⁻¹),hp] with D h2 hi h1 he hp
    exact ⟨h2,hi,h1,he,hp⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hDD χ hA j
  obtain ⟨hD2,hDiD,hL1,hεL,hpoly⟩ := hD₀ D hDD
  have hLp : 0<lemma23PaperL D := by linarith
  have hbudget : lemma84InteriorConstant*lemma84WeightScale (lemma23PaperL D^9)≤lemma23PaperL D := by
    simpa only [lemma84WeightScale,Real.log_pow,Nat.cast_ofNat,C,mul_assoc] using hpoly
  have hpow : lemma23PaperL D*lemma23PaperL D^(-11:ℤ)=lemma23PaperL D^(-10:ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 1 (-11)).symm
  have hpow' : lemma23PaperL D*lemma23PaperL D^(-10:ℤ)=lemma23PaperL D^(-9:ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 1 (-10)).symm
  have hone : 1≤ε*Real.pi*lemma23PaperL D := by
    have hh := mul_le_mul_of_nonneg_left hεL (mul_pos hε Real.pi_pos).le
    rw [mul_inv_cancel₀ (mul_pos hε Real.pi_pos).ne'] at hh
    exact hh
  calc
    _ ≤ lemma84InteriorConstant*lemma84WeightScale (lemma23PaperL D^9)*lemma23PaperL D^(-11:ℤ) := hi D hDiD χ hA j
    _ ≤ lemma23PaperL D*lemma23PaperL D^(-11:ℤ) := mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = lemma23PaperL D^(-10:ℤ) := hpow
    _ ≤ (ε*Real.pi*lemma23PaperL D)*lemma23PaperL D^(-10:ℤ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (show 0≤lemma23PaperL D^(-10:ℤ) by positivity)
    _ = ε*lemma44PaperAlpha D := by
      rw [mul_assoc (ε*Real.pi),hpow',lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
      simp only [zpow_neg,zpow_ofNat]
      ring

end ZhangLS.Spec
