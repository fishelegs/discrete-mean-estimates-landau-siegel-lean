import ZhangLS.Spec.AppendixBKernelFullComparison
import ZhangLS.Spec.Lemma84Section8Cutoffs
import ZhangLS.Spec.Lemma83

/-! Uniform original Appendix B cutoffs and finite-D shifts. Index 0 is the
full, untruncated P1 kernel; indices 1 and 2 are P2 and P3. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ZhangLS.Spec
open Complex Filter

noncomputable def appendixBOriginalCutoff (D : ℕ) (μ : Fin 3) : ℝ :=
  if μ=0 then lemma151P1 D else if μ=1 then lemma151P2 D else lemma151P3 D
noncomputable def appendixBOriginalGamma (D : ℕ) (μ : Fin 3) : ℂ :=
  if μ=1 then lemma151Beta7 D else lemma151Beta6 D
noncomputable def appendixBOriginalExponent (μ : Fin 3) : ℝ :=
  if μ=0 then 0.504 else if μ=1 then 0.5 else 0.498
noncomputable def appendixBOriginalFrequency (μ : Fin 3) : ℝ :=
  if μ=1 then 5/2 else 3/2
noncomputable def appendixBOriginalTCost (μ : Fin 3) : ℝ := if μ=1 then 10 else 0

lemma appendixB_original_cutoff_pos (D : ℕ) (μ : Fin 3) :
    0<appendixBOriginalCutoff D μ := by
  unfold appendixBOriginalCutoff lemma151P1 lemma151P2 lemma151P3
  split_ifs <;> positivity [Real.exp_pos (lemma23PaperL D^9),lemma56_paper_T_pos D]

lemma appendixB_original_cutoff_log (D : ℕ) (μ : Fin 3) :
    Real.log (appendixBOriginalCutoff D μ)=
      appendixBOriginalExponent μ*lemma23PaperL D^9-
        appendixBOriginalTCost μ*Real.log (lemma56PaperT D) := by
  fin_cases μ
  · change Real.log (lemma151P1 D)=0.504*lemma23PaperL D^9-0*_
    rw [lemma151P1,lemma23PaperP,Real.log_rpow (Real.exp_pos _),Real.log_exp]
    ring
  · change Real.log (lemma151P2 D)=0.5*lemma23PaperL D^9-10*_
    have he : lemma151P2 D=lemma84Section8P2 D := by
      unfold lemma151P2 lemma84Section8P2
      norm_num
    rw [he,lemma84_section8_log_p2,lemma56PaperT,Real.log_exp]
    norm_num
  · change Real.log (lemma151P3 D)=0.498*lemma23PaperL D^9-0*_
    rw [lemma151P3,lemma23PaperP,Real.log_rpow (Real.exp_pos _),Real.log_exp]
    ring

lemma appendixB_original_cutoffs_eventually :
    ∀ᶠ D : ℕ in atTop, 1<lemma23PaperL D ∧ ∀ μ : Fin 3,
      1<appendixBOriginalCutoff D μ ∧
      lemma56PaperT D^2<appendixBOriginalCutoff D μ ∧
      appendixBOriginalCutoff D μ<lemma23PaperP D ∧
      (1/4)*lemma23PaperL D^9≤Real.log (appendixBOriginalCutoff D μ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hs := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<79/10)).comp ht).eventually_ge_atTop 100
  filter_upwards [ht.eventually_gt_atTop 1,hs] with D hL hs
  have hLp : 0<lemma23PaperL D := by linarith
  change 100≤lemma23PaperL D^(79/10:ℝ) at hs
  have hscale : 100*Real.log (lemma56PaperT D)≤lemma23PaperL D^9 := by
    have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLp.le (11/10))
    rw [←Real.rpow_add hLp,show (79/10:ℝ)+11/10=9 by norm_num] at hh
    have he : lemma23PaperL D^(9:ℝ)=lemma23PaperL D^(9:ℕ) := Real.rpow_natCast _ 9
    rw [he] at hh
    simpa [lemma56PaperT,Real.log_exp] using hh
  have hTp : 0<Real.log (lemma56PaperT D) := by
    rw [lemma56PaperT,Real.log_exp]; positivity
  have hPp : 0<lemma23PaperL D^9 := by positivity
  refine ⟨hL,?_⟩
  intro μ
  have hQp := appendixB_original_cutoff_pos D μ
  have hlog : 2*Real.log (lemma56PaperT D)<Real.log (appendixBOriginalCutoff D μ) ∧
      Real.log (appendixBOriginalCutoff D μ)<lemma23PaperL D^9 ∧
      (1/4)*lemma23PaperL D^9≤Real.log (appendixBOriginalCutoff D μ) := by
    rw [appendixB_original_cutoff_log]
    fin_cases μ <;> norm_num only [appendixBOriginalExponent,appendixBOriginalTCost,Fin.mk.injEq,
      OfNat.ofNat,ite_true,ite_false,zero_mul,sub_zero] <;> norm_num
    all_goals constructor
    all_goals first | constructor <;> nlinarith | nlinarith
  refine ⟨(Real.log_pos_iff hQp.le).mp (by linarith [hlog.1]),?_,?_,hlog.2.2⟩
  · apply (Real.log_lt_log_iff (by positivity [lemma56_paper_T_pos D]) hQp).mp
    simpa [Real.log_pow] using hlog.1
  · apply (Real.log_lt_log_iff hQp (Real.exp_pos _)).mp
    simpa [lemma23PaperP,Real.log_exp] using hlog.2.1

lemma appendixB_original_gamma (D : ℕ) (μ : Fin 3)
    (hα : 0<lemma44PaperAlpha D) :
    (appendixBOriginalGamma D μ).re=0 ∧ appendixBOriginalGamma D μ≠0 ∧
      ‖appendixBOriginalGamma D μ‖≤3*lemma44PaperAlpha D := by
  have hαC : (lemma44PaperAlpha D : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hα.ne'
  unfold appendixBOriginalGamma lemma151Beta7 lemma151Beta6
  split_ifs
  all_goals refine ⟨by simp,?_,?_⟩
  all_goals try exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hαC) (by norm_num)
  all_goals simp only [norm_div,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hα,norm_ofNat]
  all_goals linarith

/-- One threshold, fixed before j, μ and l1; finite-D beta and the T^-10
correction are preserved exactly in both the sum and the residue. -/
theorem appendixB_original_full_kernels_uniform {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2000≤lemma23PaperL D ∧ ∀ j μ : Fin 3, ∀ l₁ : ℕ,
      0<l₁ → (l₁ : ℝ)<lemma56PaperT D →
      ‖appendixBFullKernelSum (appendixBOriginalCutoff D μ) (lemma83PaperBeta D c j)
          (appendixBOriginalGamma D μ) l₁-
        appendixBModelLeading (appendixBOriginalCutoff D μ)
          (appendixBOriginalCutoff D μ/l₁) (lemma83PaperBeta D c j)
          (appendixBOriginalGamma D μ)‖≤
        4*(appendixBContourBudget D+275*Real.exp (5*Real.pi))/lemma23PaperL D^9 := by
  obtain ⟨N,hN,hfull⟩ := appendixB_full_kernel_quantitative
  obtain ⟨M,hM,hsmall⟩ := lemma52_exists_shift_threshold hc
  obtain ⟨K,hK⟩ := eventually_atTop.mp appendixB_original_cutoffs_eventually
  refine ⟨max N (max M K),hN.trans (le_max_left _ _),?_⟩
  intro D hD
  obtain ⟨hL,hfullD⟩ := hfull D ((le_max_left _ _).trans hD)
  have hMK : max M K≤D := (le_max_right _ _).trans hD
  obtain ⟨hL1,hcuts⟩ := hK D ((le_max_right _ _).trans hMK)
  refine ⟨hL,?_⟩
  intro j μ l₁ hl hlT
  have hα := (lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)).1
  obtain ⟨hgRe,hg0,hg⟩ := appendixB_original_gamma D μ hα
  obtain ⟨hX,hXT,hXP,hlog⟩ := hcuts μ
  have hlr : 0<(l₁ : ℝ) := Nat.cast_pos.mpr hl
  have hT := lemma56_paper_T_pos D
  have hxT : lemma56PaperT D<appendixBOriginalCutoff D μ/l₁ := by
    apply (lt_div_iff₀ hlr).mpr
    exact (mul_lt_mul_of_pos_left hlT hT).trans (by simpa [pow_two] using hXT)
  have hxP : appendixBOriginalCutoff D μ/l₁<lemma23PaperP D :=
    (div_le_self (by linarith only [hX]) (by exact_mod_cast hl)).trans_lt hXP
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3≤lemma23PaperL D)
    hc (hsmall D ((le_max_left _ _).trans hMK)) j
  have hh := hfullD (lemma83PaperBeta D c j) (appendixBOriginalGamma D μ)
    (lemma83_beta_re D c j) hb hgRe hg0 hg _ hX l₁ hl hxT hxP
  apply hh.trans
  have hB : 0≤appendixBContourBudget D+275*Real.exp (5*Real.pi) := by
    unfold appendixBContourBudget appendixBContourMajorant appendixBContourHeight
    have hLp : 0<lemma23PaperL D := by linarith
    have hY := proposition71_zeta_aux_height_pos D
    positivity
  have hp : 0<lemma23PaperL D^9 := by positivity
  apply (div_le_div_iff₀ (Real.log_pos hX) hp).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hlog hB]

/-- The shift logarithm is genuinely controlled on the entire original range. -/
theorem appendixB_original_log_l1 {D l₁ : ℕ} (hl : 0<l₁)
    (hlT : (l₁ : ℝ)<lemma56PaperT D) :
    0≤Real.log (l₁ : ℝ) ∧ Real.log (l₁ : ℝ)<lemma23PaperL D^(11/10:ℝ) := by
  refine ⟨Real.log_nonneg (by exact_mod_cast hl),?_⟩
  simpa [lemma56PaperT,Real.log_exp] using Real.log_lt_log (Nat.cast_pos.mpr hl) hlT

end ZhangLS.Spec
