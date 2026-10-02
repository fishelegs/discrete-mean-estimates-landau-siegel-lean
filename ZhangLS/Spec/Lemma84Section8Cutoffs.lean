import ZhangLS.Spec.Lemma84CompanionBounds

/-! Exact Section 8 cutoffs and fixed coefficient, from (2.21),(2.26).
The logarithmic lower bounds are uniform in the varying modulus D. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter Topology
set_option maxHeartbeats 2000000

noncomputable def lemma84Section8P1 (D : ℕ) : ℝ :=
  (lemma23PaperP D)^(63/125:ℝ)
noncomputable def lemma84Section8P2 (D : ℕ) : ℝ :=
  (lemma23PaperP D)^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ)
noncomputable def lemma84Section8Iota : ℂ :=
  (94977/100000:ℝ) - (138995/100000:ℝ)*Complex.I
noncomputable def lemma84Section8Cutoff (D μ : ℕ) : ℝ :=
  if μ=6 then lemma84Section8P1 D else lemma84Section8P2 D

lemma lemma84_section8_cutoff_pos (D μ : ℕ) : 0<lemma84Section8Cutoff D μ := by
  unfold lemma84Section8Cutoff lemma84Section8P1 lemma84Section8P2
  split_ifs <;> positivity [Real.exp_pos (lemma23PaperL D^9),lemma56_paper_T_pos D]

lemma lemma84_section8_log_p1 (D : ℕ) :
    Real.log (lemma84Section8P1 D)=(63/125)*lemma23PaperL D^9 := by
  rw [lemma84Section8P1,lemma23PaperP,Real.log_rpow (Real.exp_pos _),Real.log_exp]

lemma lemma84_section8_log_p2 (D : ℕ) :
    Real.log (lemma84Section8P2 D)=(1/2)*lemma23PaperL D^9-10*lemma23PaperL D^(11/10:ℝ) := by
  rw [lemma84Section8P2,Real.log_mul (by positivity [Real.exp_pos (lemma23PaperL D^9)])
    (by positivity [lemma56_paper_T_pos D]),lemma23PaperP,Real.log_rpow (Real.exp_pos _),Real.log_zpow,
    lemma56PaperT,Real.log_exp,Real.log_exp]
  norm_num
  ring

/-- All numerical cutoff restrictions needed by the actual repaired inner sum. -/
theorem lemma84_section8_cutoffs_eventually :
    ∀ᶠ D : ℕ in atTop, 2≤D ∧ 1<lemma23PaperL D ∧
      ∀ μ : ℕ, 1<lemma84Section8Cutoff D μ ∧
        lemma84Section8Cutoff D μ<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) ∧
        lemma84Section8Cutoff D μ<lemma23PaperP D ∧
        (1/4)*lemma23PaperL D^9≤Real.log (lemma84Section8Cutoff D μ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hs := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<79/10)).comp ht).eventually_ge_atTop 100
  filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually_gt_atTop 1,hs] with D hD hL hs
  refine ⟨hD,hL,?_⟩
  intro μ
  have hLp : 0<lemma23PaperL D := by linarith
  change 100≤lemma23PaperL D^(79/10:ℝ) at hs
  have hscale : 100*lemma23PaperL D^(11/10:ℝ)≤lemma23PaperL D^9 := by
    have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLp.le (11/10))
    rw [←Real.rpow_add hLp] at hh
    rw [show (79/10:ℝ)+11/10=9 by norm_num] at hh
    have he : lemma23PaperL D^(9:ℝ)=lemma23PaperL D^(9:ℕ) := Real.rpow_natCast _ 9
    rwa [he] at hh
  have hp9 : 0<lemma23PaperL D^9 := by positivity
  have htlog : 0≤lemma23PaperL D^(11/10:ℝ) := by positivity
  have hQ := lemma84_section8_cutoff_pos D μ
  have hlog : (1/4)*lemma23PaperL D^9≤Real.log (lemma84Section8Cutoff D μ) ∧
      Real.log (lemma84Section8Cutoff D μ)<lemma23PaperL D^9-2*lemma23PaperL D^(11/10:ℝ) := by
    unfold lemma84Section8Cutoff
    split_ifs
    · rw [lemma84_section8_log_p1]
      constructor <;> nlinarith
    · rw [lemma84_section8_log_p2]
      constructor <;> nlinarith
  have hcutp : 0<lemma23PaperP D*lemma56PaperT D^(-2:ℤ) := by
    positivity [lemma56_paper_T_pos D,Real.exp_pos (lemma23PaperL D^9)]
  have hcLog : Real.log (lemma23PaperP D*lemma56PaperT D^(-2:ℤ))=
      lemma23PaperL D^9-2*lemma23PaperL D^(11/10:ℝ) := by
    rw [Real.log_mul (by positivity [Real.exp_pos (lemma23PaperL D^9)])
      (by positivity [lemma56_paper_T_pos D]),lemma23PaperP,Real.log_exp,
      Real.log_zpow,lemma56PaperT,Real.log_exp]
    norm_num
    ring
  refine ⟨(Real.log_pos_iff hQ.le).mp (by nlinarith [hlog.1]),?_,?_,hlog.1⟩
  · exact (Real.log_lt_log_iff hQ hcutp).mp (by rw [hcLog]; exact hlog.2)
  · apply (Real.log_lt_log_iff hQ (Real.exp_pos _)).mp
    simpa only [lemma23PaperP,Real.log_exp] using (show Real.log (lemma84Section8Cutoff D μ)<lemma23PaperL D^9 by linarith [hlog.2])

/-- P₂ really lies inside the P₁ outer support, uniformly for log D>0. -/
theorem lemma84_section8_p2_lt_p1 {D : ℕ} (hL : 0<lemma23PaperL D) :
    lemma84Section8P2 D<lemma84Section8P1 D := by
  have h1 : 0<lemma84Section8P1 D := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have h2 : 0<lemma84Section8P2 D := by
    unfold lemma84Section8P2
    positivity [Real.exp_pos (lemma23PaperL D^9),lemma56_paper_T_pos D]
  apply (Real.log_lt_log_iff h2 h1).mp
  rw [lemma84_section8_log_p1,lemma84_section8_log_p2]
  nlinarith [pow_pos hL 9,Real.rpow_nonneg hL.le (11/10)]

end ZhangLS.Spec
