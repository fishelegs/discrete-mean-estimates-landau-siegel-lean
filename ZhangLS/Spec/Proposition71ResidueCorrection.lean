import ZhangLS.Spec.Proposition71LocalResidues

/-! The true analytic correction for Proposition 7.1. Its Mellin factor is
δ_D(1−β_j), whose approximation to one is precisely Lemma 5.4(ii). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology
set_option maxHeartbeats 2000000

noncomputable def proposition71ResidueCorrection (D : ℕ) (c : ℝ) (j : Fin 3) : ℂ :=
  lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j) *
    zetaPoleRemoved (1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+1)) *
    zetaPoleRemoved (1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+2)) *
    (zetaPoleRemoved (1-lemma83PaperBeta D c j))⁻¹

noncomputable def proposition71ResidueFactorConstant : ℝ := 30+lemma54Constant

lemma proposition71_residue_factor_constant_pos : 0<proposition71ResidueFactorConstant := by
  unfold proposition71ResidueFactorConstant
  linarith [lemma54_constant_pos]

lemma proposition71_actual_residue_regular_formula {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    I*proposition71ActualR D c j =
      (I*(-lemma83PaperBeta D c j) /
        ((lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j)*
         (lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j))) *
        proposition71ResidueCorrection D c j := by
  have hL3 : 3≤lemma23PaperL D := by linarith
  have hd := section15_actual_shift_data hL3 hc hsmall
  have hb := hd.1 j
  have hβ := lemma83_beta_re D c
  have hg1 : lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have hh := hd.2 he; fin_cases j <;> simp at hh)
  have hg2 : lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j≠0 := sub_ne_zero.mpr (by
    intro he; have hh := hd.2 he; fin_cases j <;> simp at hh)
  have hz0 : 1-lemma83PaperBeta D c j≠0 := by
    intro he; have := congrArg Complex.re he; simp [hβ] at this
  have hz1 : 1-lemma83PaperBeta D c j≠1 := by intro he; apply hb; linear_combination -he
  have hgap0 (k : Fin 3) : 1-lemma83PaperBeta D c j+lemma83PaperBeta D c k≠0 := by
    intro he; have := congrArg Complex.re he; simp [hβ] at this
  have hgap1 : 1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+1)≠1 := by
    intro he; apply hg1; linear_combination he
  have hgap2 : 1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+2)≠1 := by
    intro he; apply hg2; linear_combination he
  rw [proposition71_actual_residue_formula hD hL hc hsmall j]
  unfold proposition71ResidueCorrection
  rw [zetaPoleRemoved_eq_mul_riemannZeta hz0 hz1,
    zetaPoleRemoved_eq_mul_riemannZeta (hgap0 _) hgap1,
    zetaPoleRemoved_eq_mul_riemannZeta (hgap0 _) hgap2]
  have hz := (proposition71_actual_zeta_denominator_nonzero hL3 hc hsmall j).2
  rw [show 1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+1)=
      1+lemma83PaperBeta D c (j+1)-lemma83PaperBeta D c j by ring,
    show 1-lemma83PaperBeta D c j+lemma83PaperBeta D c (j+2)=
      1+lemma83PaperBeta D c (j+2)-lemma83PaperBeta D c j by ring]
  field_simp [hb,hg1,hg2,hz]
  ring

/-- The actual three poles lie inside the open 10α disk required by Lemma 5.4(ii). -/
lemma proposition71_actual_poles_in_delta_disk {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖(1-lemma83PaperBeta D c j)-1‖<10*lemma44PaperAlpha D := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hb := lemma83_paper_beta_norm hL hc hsmall j
  simpa using (show ‖lemma83PaperBeta D c j‖<10*lemma44PaperAlpha D by linarith)

/-- The precise Lemma 5.4(ii) estimate at the actual poles. -/
lemma proposition71_actual_delta_log_error_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ c : ℝ, 0<c →
      3≤lemma23PaperL D → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ j : Fin 3, ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤
        lemma54Constant*lemma44PaperAlpha D*Real.log (lemma23PaperL D) := by
  obtain ⟨D₀,hD₀⟩ := lemma54_uniform_constants
  refine ⟨D₀,?_⟩
  intro D hD c hc hL hsmall j
  exact (hD₀ D hD).2.2 _ (proposition71_actual_poles_in_delta_disk hL hc hsmall j)

lemma proposition71_actual_delta_error_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ c : ℝ, 0<c →
      3≤lemma23PaperL D → c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 →
      ∀ j : Fin 3, ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤
        lemma54Constant*lemma44PaperAlpha D*lemma23PaperL D := by
  obtain ⟨D₀,hD₀⟩ := proposition71_actual_delta_log_error_threshold
  refine ⟨D₀,?_⟩
  intro D hD c hc hL hsmall j
  apply (hD₀ D hD c hc hL hsmall j).trans
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith))
    (mul_nonneg lemma54_constant_pos.le (lemma44_alpha_pos_le_one hL).1.le)

lemma proposition71_actual_zeta_factor_errors {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j k : Fin 3) :
    ‖zetaPoleRemoved (1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1‖≤
      30*lemma44PaperAlpha D ∧
    ‖(zetaPoleRemoved (1-lemma83PaperBeta D c j))⁻¹-1‖≤30*lemma44PaperAlpha D := by
  have ha := (lemma44_alpha_pos_le_one hL).1
  have has := lemma152_alpha_le_hundredth hL
  have hj := lemma83_paper_beta_norm hL hc hsmall j
  have hk := lemma83_paper_beta_norm hL hc hsmall k
  have hdiff : ‖(1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1‖≤6*lemma44PaperAlpha D := by
    rw [show (1-lemma83PaperBeta D c j+lemma83PaperBeta D c k)-1=
      lemma83PaperBeta D c k-lemma83PaperBeta D c j by ring]
    exact (norm_sub_le _ _).trans (by linarith)
  have hb : ‖(1-lemma83PaperBeta D c j)-1‖≤3*lemma44PaperAlpha D := by simpa using hj
  have hz := section15_zeta_regular_error (hdiff.trans (by linarith))
  have hz0 := section15_zeta_regular_error (hb.trans (by linarith))
  have hbase : ‖zetaPoleRemoved (1-lemma83PaperBeta D c j)-1‖≤15*lemma44PaperAlpha D := by linarith
  have hi := section15_inverse_error hbase (by linarith)
  constructor <;> linarith

lemma proposition71_actual_correction_error {D : ℕ} {c : ℝ}
    (hL : 3≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hδ : ∀ j : Fin 3, ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤
      lemma54Constant*lemma44PaperAlpha D*lemma23PaperL D)
    (hbudget : proposition71ResidueFactorConstant*lemma44PaperAlpha D*lemma23PaperL D≤1)
    (j : Fin 3) :
    ‖proposition71ResidueCorrection D c j-1‖≤
      15*proposition71ResidueFactorConstant*lemma44PaperAlpha D*lemma23PaperL D := by
  let e := proposition71ResidueFactorConstant*lemma44PaperAlpha D*lemma23PaperL D
  have ha := (lemma44_alpha_pos_le_one hL).1
  have hC : 30≤proposition71ResidueFactorConstant := by
    unfold proposition71ResidueFactorConstant; linarith [lemma54_constant_pos]
  have hCd : lemma54Constant≤proposition71ResidueFactorConstant := by
    unfold proposition71ResidueFactorConstant; linarith
  have he : 30*lemma44PaperAlpha D≤e := by
    dsimp [e]
    have hCL : 30≤proposition71ResidueFactorConstant*lemma23PaperL D := by
      nlinarith [proposition71_residue_factor_constant_pos]
    nlinarith
  have hz (k : Fin 3) := proposition71_actual_zeta_factor_errors hL hc hsmall j k
  have hd : ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤e := by
    apply (hδ j).trans
    dsimp [e]
    gcongr
  have h1 := section15_mul_error (a := 1) (by simpa using hd) ((hz (j+1)).1.trans he) hbudget
  have h2 := section15_mul_error h1 ((hz (j+2)).1.trans he) hbudget
  have h3 := section15_mul_error h2 ((hz 0).2.trans he) hbudget
  norm_num at h3
  simpa only [proposition71ResidueCorrection,e,mul_assoc] using h3

/-- One threshold, after the original shift parameter c has been fixed. -/
theorem proposition71_residue_parameters_threshold {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 ∧
      (∀ j : Fin 3, ‖lemma54PaperDeltaMellin D (1-lemma83PaperBeta D c j)-1‖≤
        lemma54Constant*lemma44PaperAlpha D*lemma23PaperL D) ∧
      proposition71ResidueFactorConstant*lemma44PaperAlpha D*lemma23PaperL D≤1 := by
  obtain ⟨Ds,hs,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨Dk,hk,hbudget⟩ := lemma52_exists_shift_threshold proposition71_residue_factor_constant_pos
  obtain ⟨Dd,hdelta⟩ := proposition71_actual_delta_error_threshold
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Dl,hlog⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2000:ℝ)))
  refine ⟨max 2 (max Ds (max Dk (max Dd Dl))),le_max_left _ _,?_⟩
  intro D hD
  have hsD : Ds≤D := by omega
  have hkD : Dk≤D := by omega
  have hdD : Dd≤D := by omega
  have hlD : Dl≤D := by omega
  have hL := hlog D hlD
  refine ⟨hL,hsmall D hsD,hdelta D hdD c hc (by linarith) (hsmall D hsD),?_⟩
  linarith [hbudget D hkD]

end ZhangLS.Spec
