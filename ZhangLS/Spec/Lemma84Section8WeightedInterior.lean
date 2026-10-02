import ZhangLS.Spec.Lemma84Section8InnerBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

/-- Actual outer support has only harmonic mass (up to a fixed log-log power). -/
theorem lemma84_section8_weight_mass {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (hL : 1<lemma23PaperL D) :
    (∑ a∈lemma84Section8Pairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
      4*lemma84WeightScale (lemma23PaperL D^9)*lemma23PaperL D^9 := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hy : 1<lemma23PaperL D^9 := one_lt_pow₀ hL (by norm_num)
  have hP1 : 0<Real.log (lemma84Section8P1 D) := by rw [lemma84_section8_log_p1]; positivity
  have hQ : 0<lemma84Section8P1 D := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hQ1 : 1≤lemma84Section8P1 D := ((Real.log_pos_iff hQ.le).mp hP1).le
  have hN1 : 1≤⌊lemma84Section8P1 D⌋₊ := (Nat.le_floor_iff hQ.le).mpr (by simpa using hQ1)
  have hN : (⌊lemma84Section8P1 D⌋₊:ℝ)≤lemma84Section8P1 D := Nat.floor_le hQ.le
  have hlogN : Real.log (⌊lemma84Section8P1 D⌋₊:ℝ)≤lemma23PaperL D^9 := by
    apply (Real.log_le_log (by exact_mod_cast (show 0<⌊lemma84Section8P1 D⌋₊ by omega)) hN).trans
    rw [lemma84_section8_log_p1]
    nlinarith [pow_pos hLp 9]
  have hH : (harmonic ⌊lemma84Section8P1 D⌋₊:ℝ)≤2*lemma23PaperL D^9 :=
    (harmonic_le_one_add_log _).trans (by linarith)
  have hm := lemma84_actual_weight_mass χ c j (lemma84Section8Pairs D)
    ⌊lemma84Section8P1 D⌋₊ (filter_subset _ _) hy (by
      intro a ha
      obtain ⟨hab,hcut⟩ := mem_filter.mp ha
      have hpos := mem_product.mp hab
      have hd : 0<a.1 := (mem_Icc.mp hpos.1).1
      have hr : 0<a.2 := (mem_Icc.mp hpos.2).1
      have hh := Real.log_lt_log (by exact_mod_cast Nat.mul_pos hd hr) hcut
      rw [lemma84_section8_log_p1] at hh
      nlinarith [pow_pos hLp 9])
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left hH
    (show 0≤2*lemma84WeightScale (lemma23PaperL D^9) from mul_nonneg (by norm_num) (lemma84_weight_scale_nonneg _))
  nlinarith only [hh]

noncomputable def lemma84InteriorConstant : ℝ :=
  192*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)^2

lemma lemma84_interior_constant_pos : 0<lemma84InteriorConstant := by
  unfold lemma84InteriorConstant
  positivity [lemma84_companion_constant_pos]

/-- The true weighted interior error from the repaired 8.4, with both smoothing
cutoffs and the actual fixed iota cross terms. No weighted-error hypothesis. -/
theorem lemma84_section8_interior_quantitative :
    ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ j : Fin 3,
        ‖lemma84Section8Raw χ c j-lemma84Section8Hybrid χ c j‖≤
          lemma84InteriorConstant*lemma84WeightScale (lemma23PaperL D^9)*lemma23PaperL D^(-11:ℤ) := by
  intro c hc
  obtain ⟨D₀,hD02,hinner⟩ := lemma84_section8_inner_bounds c hc
  refine ⟨D₀,hD02,?_⟩
  intro D hDD χ hA j
  obtain ⟨hL,hbounds⟩ := hinner D hDD
  have hLp : 0<lemma23PaperL D := by linarith
  have hb6 := hbounds χ hA j 6
  have hb7 := hbounds χ hA j 7
  let F : ℝ := 4*lemma84CompanionConstant*(1+‖lemma84Section8Iota‖)*lemma23PaperL D^(-6:ℤ)
  let E : ℝ := 12*(1+‖lemma84Section8Iota‖)*lemma23PaperL D^(-14:ℤ)
  have hF0 : 0≤F := by dsimp [F]; positivity [lemma84_companion_constant_pos]
  have hE0 : 0≤E := by dsimp [E]; positivity
  have hF (n : ℕ) (hn : 0<n) : ‖lemma84Section8FirstCombined χ c j n‖≤F := by
    unfold lemma84Section8FirstCombined
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hh := add_le_add (hb6.1 n hn) (mul_le_mul_of_nonneg_left (hb7.1 n hn) (norm_nonneg lemma84Section8Iota))
    dsimp [F]
    nlinarith only [hh]
  have hE (d r : ℕ) (hd : 0<d) (hr : 0<r) :
      ‖(lemma84Section8Second χ c j 6 d r-lemma84Section8SecondHybrid χ c j 6 d r)+
        star lemma84Section8Iota*(lemma84Section8Second χ c j 7 d r-lemma84Section8SecondHybrid χ c j 7 d r)‖≤E := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_star]
    have hh := add_le_add (hb6.2 d r hd hr)
      (mul_le_mul_of_nonneg_left (hb7.2 d r hd hr) (norm_nonneg lemma84Section8Iota))
    dsimp [E]
    nlinarith only [hh]
  have hid : lemma84Section8Raw χ c j-lemma84Section8Hybrid χ c j=
      ∑ a∈lemma84Section8Pairs D, lemma84Section8Weight χ c j a.1 a.2*
        lemma84Section8FirstCombined χ c j (a.1*a.2)*
        ((lemma84Section8Second χ c j 6 a.1 a.2-lemma84Section8SecondHybrid χ c j 6 a.1 a.2)+
          star lemma84Section8Iota*(lemma84Section8Second χ c j 7 a.1 a.2-lemma84Section8SecondHybrid χ c j 7 a.1 a.2)) := by
    rw [lemma84Section8Raw,lemma84Section8Hybrid,←sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    ring
  rw [hid]
  calc
    _ ≤ ∑ a∈lemma84Section8Pairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖*F*E := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro a ha
      have hp := mem_product.mp (mem_filter.mp ha).1
      have hd : 0<a.1 := (mem_Icc.mp hp.1).1
      have hr : 0<a.2 := (mem_Icc.mp hp.2).1
      rw [norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF _ (Nat.mul_pos hd hr)) (norm_nonneg _))
        (hE a.1 a.2 hd hr) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hF0)
    _ = (∑ a∈lemma84Section8Pairs D, ‖lemma84Section8Weight χ c j a.1 a.2‖)*F*E := by
      rw [sum_mul,sum_mul]
    _ ≤ (4*lemma84WeightScale (lemma23PaperL D^9)*lemma23PaperL D^9)*F*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lemma84_section8_weight_mass χ c j hL) hF0) hE0
    _ = _ := by
      dsimp [F,E,lemma84InteriorConstant]
      simp only [zpow_neg,zpow_ofNat]
      field_simp
      ring

end ZhangLS.Spec
