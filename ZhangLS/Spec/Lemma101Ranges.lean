import ZhangLS.Spec.Lemma101WeightedBounds

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology
open scoped Real

lemma lemma101_P_gt_one {D : ℕ} (hD : 1<D) : 1<lemma23PaperP D := by
  unfold lemma23PaperP
  exact Real.one_lt_exp_iff.mpr (pow_pos (Real.log_pos (by exact_mod_cast hD)) _)

lemma lemma101_T_gt_one {D : ℕ} (hD : 1<D) : 1<lemma56PaperT D := by
  unfold lemma56PaperT
  exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hD)) _)

lemma lemma101_cutoff_lt_P {D : ℕ} (hD : 1<D) {y a : ℝ}
    (hy : 1≤y) (ha : a<1) : lemma101Cutoff D y a < lemma23PaperP D := by
  have hp := lemma101_P_gt_one hD
  calc
    lemma101Cutoff D y a ≤ lemma23PaperP D^a := div_le_self
      (Real.rpow_nonneg (by linarith) _) hy
    _ < lemma23PaperP D^1 := Real.rpow_lt_rpow_of_exponent_lt hp ha
    _ = _ := Real.rpow_one _

lemma lemma101_cutoff_ge_T {D : ℕ} {y a : ℝ} (hy : 0<y)
    (hyT : y≤lemma23PaperP D^a/lemma56PaperT D) :
    lemma56PaperT D≤lemma101Cutoff D y a := by
  have hT : 0<lemma56PaperT D := Real.exp_pos _
  apply (le_div_iff₀ hy).mpr
  have hh := (le_div_iff₀ hT).mp hyT
  simpa only [mul_comm] using hh

lemma lemma101_cutoff_le_one {D : ℕ} {y a : ℝ} (hy : 0<y)
    (ha : lemma23PaperP D^a≤y) : lemma101Cutoff D y a≤1 :=
  (div_le_one hy).mpr ha

lemma lemma101_half_power_le_power {D : ℕ} (hD : 1<D) {a : ℝ} (ha : 1/2≤a) :
    lemma23PaperP D^(1/2:ℝ)≤lemma23PaperP D^a :=
  Real.rpow_le_rpow_of_exponent_le (lemma101_P_gt_one hD).le ha

lemma lemma101_half_power_gt_one {D : ℕ} (hD : 1<D) :
    1<lemma23PaperP D^(1/2:ℝ) := by
  exact Real.one_lt_rpow (lemma101_P_gt_one hD) (by norm_num)

lemma lemma101_T_le_half_power {D : ℕ} (hL : 2000≤lemma23PaperL D) :
    lemma56PaperT D≤lemma23PaperP D^(1/2:ℝ) := by
  let L := lemma23PaperL D
  have hLp : 0<L := by dsimp [L]; linarith
  have hL1 : 1≤L := by dsimp [L]; linarith
  have hr : L^(11/10:ℝ)≤L^2 := by
    rw [← Real.rpow_natCast L 2]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hp : 2*L^2≤L^9 := by
    have h7 : 2≤L^7 := (show 2≤L by dsimp [L]; linarith).trans
      (by simpa using pow_le_pow_right₀ hL1 (show 1≤7 by norm_num))
    have hh := mul_le_mul_of_nonneg_right h7 (sq_nonneg L)
    nlinarith only [hh]
  unfold lemma56PaperT lemma23PaperP
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  apply Real.exp_le_exp.mpr
  change L^(11/10:ℝ)≤L^9*(1/2)
  linarith

lemma lemma101_transition_ge_one {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {y : ℝ} (hy : Lemma101Transition D y) : 1≤y := by
  have hT : 0<lemma56PaperT D := Real.exp_pos _
  have hl : ∀ a : ℝ, 1/2≤a → 1≤lemma23PaperP D^a/lemma56PaperT D := by
    intro a ha
    apply (le_div_iff₀ hT).mpr
    simpa only [one_mul] using (lemma101_T_le_half_power hL).trans
      (lemma101_half_power_le_power hD ha)
  rcases hy with ((hy|hy)|hy)
  · exact (hl (1/2) (by norm_num)).trans hy.1.le
  · exact (hl (251/500) (by norm_num)).trans hy.1.le
  · exact (hl (63/125) (by norm_num)).trans hy.1.le

lemma lemma101_prefactor_norm {D : ℕ} (hL : 0<lemma23PaperL D) :
    ‖500/(Real.log (lemma23PaperP D):ℂ)‖ = 500/lemma23PaperL D^9 := by
  rw [norm_div, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    lemma23PaperP, Real.log_exp, abs_of_pos (pow_pos hL 9)]

lemma lemma101_uniform_threshold (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      2≤D ∧ 2000≤lemma23PaperL D ∧
      c*lemma44PaperAlpha D*lemma23PaperL D≤1/10 ∧
      (D:ℝ)/lemma56PaperT D≤2*lemma23PaperL D^(-6:ℤ) ∧
      (D:ℝ)/lemma56PaperT D≤lemma56PaperT D^(-(1/2:ℝ)) := by
  obtain ⟨N,hN,hh⟩ := lemma82_uniform_threshold c hc
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp ht).eventually_ge_atTop 2
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp hr
  refine ⟨max N M, le_trans hN (le_max_left _ _), ?_⟩
  intro D hD
  have hN' := (le_max_left N M).trans hD
  have hs := hh D hN'
  have hLp : 0<lemma23PaperL D := by linarith [hs.2.1]
  have hTp : 0<lemma56PaperT D := Real.exp_pos _
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_,?_⟩
  · have hb := hs.2.2.2 (2*lemma56PaperT D) (by linarith)
    have he : (D:ℝ)/lemma56PaperT D = 2*((D:ℝ)/(2*lemma56PaperT D)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  · have hb : 2≤lemma23PaperL D^(1/10:ℝ) := hM D ((le_max_right N M).trans hD)
    have hp : lemma23PaperL D≤lemma23PaperL D^(11/10:ℝ)*(1/2) := by
      rw [show (11/10:ℝ)=1+1/10 by norm_num,Real.rpow_add hLp,Real.rpow_one]
      nlinarith
    have hDp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
    have hd : (D:ℝ)≤lemma56PaperT D^(1/2:ℝ) := by
      rw [lemma56PaperT,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      conv_lhs => rw [← Real.exp_log hDp]
      exact Real.exp_le_exp.mpr hp
    calc
      (D:ℝ)/lemma56PaperT D ≤ lemma56PaperT D^(1/2:ℝ)/lemma56PaperT D :=
        div_le_div_of_nonneg_right hd hTp.le
      _ = lemma56PaperT D^(-(1/2:ℝ)) := by
        calc
          _ = lemma56PaperT D^(1/2:ℝ)/lemma56PaperT D^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hTp]; norm_num

end ZhangLS.Spec
