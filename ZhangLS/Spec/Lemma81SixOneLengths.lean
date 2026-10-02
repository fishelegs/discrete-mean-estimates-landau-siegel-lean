import ZhangLS.Spec.Lemma81ActualPolynomialMoments
import ZhangLS.Spec.Lemma61

/-! # Actual Lemma 6.1 polynomial lengths for the fourth-moment argument

The original K length includes t₀. Its domination by P is proved uniformly;
N and the short error polynomial retain their original T² and T³ cutoffs.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Filter
open scoped Real Topology
set_option maxHeartbeats 2000000

lemma lemma81_T_log_le_square {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    Real.log (lemma56PaperT D) ≤ lemma23PaperL D^2 := by
  unfold lemma56PaperT
  rw [Real.log_exp]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
    (by linarith only [hL] : 1 ≤ lemma23PaperL D) (by norm_num : (11/10 : ℝ) ≤ (2 : ℕ))

lemma lemma81_three_T_cube_le_P {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    3*lemma56PaperT D^3 ≤ lemma23PaperP D := by
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hL2 : 1 ≤ lemma23PaperL D^2 := one_le_pow₀ hL1
  have hL7 : 9 ≤ lemma23PaperL D^7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 7
    norm_num at hh
    linarith only [hh]
  have h9 : 9*lemma23PaperL D^2 ≤ lemma23PaperL D^9 := by
    calc
      _ ≤ lemma23PaperL D^7 * lemma23PaperL D^2 := mul_le_mul_of_nonneg_right hL7 (sq_nonneg _)
      _ = _ := by ring
  have hbudget : Real.log 3+3*Real.log (lemma56PaperT D) ≤ lemma23PaperL D^9 := by
    have hh := lemma81_T_log_le_square hL
    have hlog3 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
    linarith only [hh,hlog3,h9,hL2]
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  calc
    _ = Real.exp (Real.log 3+3*Real.log (lemma56PaperT D)) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      have he : Real.exp (3*Real.log (lemma56PaperT D)) = lemma56PaperT D^3 := by
        simpa only [Nat.cast_ofNat,Real.exp_log hT] using Real.exp_nat_mul (Real.log (lemma56PaperT D)) 3
      rw [he]
    _ ≤ _ := Real.exp_le_exp.mpr hbudget

lemma lemma81_T_inverse_square_le_exp_neg_log {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma56PaperT D^(-2 : ℤ) ≤ Real.exp (-lemma23PaperL D) := by
  have hTp : 0 < lemma56PaperT D := Real.exp_pos _
  have hT1 : 1 ≤ lemma56PaperT D := Real.one_le_exp_iff.mpr
    (Real.rpow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) _)
  have heT : Real.exp (lemma23PaperL D) ≤ lemma56PaperT D := by
    simpa only [Real.exp_log hTp] using Real.exp_le_exp.mpr (lemma61_T_log_bounds hL).1
  have hT2 : lemma56PaperT D ≤ lemma56PaperT D^2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT1 (by norm_num : (1 : ℕ) ≤ 2)
  rw [zpow_neg,zpow_ofNat,Real.exp_neg]
  exact (inv_le_inv₀ (pow_pos hTp 2) (Real.exp_pos _)).mpr (heT.trans hT2)

lemma lemma81_uniform_six_one_lengths :
    ∃ N : ℕ, lemma61ModulusThreshold ≤ N ∧ ∀ D : ℕ, N ≤ D →
      ⌈2*lemma61PaperP4 D⌉₊ ≤ ⌊lemma23PaperP D⌋₊ ∧
      ⌈2*lemma56PaperT D^2⌉₊ ≤ ⌊lemma23PaperP D⌋₊ ∧
      ⌈lemma56PaperT D^3⌉₊ ≤ ⌊lemma23PaperP D⌋₊ := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 519).comp ht
  have he : ∀ᶠ D : ℕ in atTop,
      lemma23PaperL D^519 * Real.exp (-lemma23PaperL D) < 1/4 :=
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  refine ⟨max N₀ lemma61ModulusThreshold,le_max_right _ _,?_⟩
  intro D hD
  have hN := (le_max_left N₀ lemma61ModulusThreshold).trans hD
  have h61 := (le_max_right N₀ lemma61ModulusThreshold).trans hD
  have hL : 3 ≤ lemma23PaperL D := by linarith only [(lemma61_parameters_at_threshold h61).2]
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have hT1 : 1 ≤ lemma56PaperT D := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLp.le _)
  have hT2 : lemma56PaperT D^2 ≤ lemma56PaperT D^3 := pow_le_pow_right₀ hT1 (by norm_num)
  have hT3 : 1 ≤ lemma56PaperT D^3 := one_le_pow₀ hT1
  have hPp : 0 < lemma23PaperP D := Real.exp_pos _
  have hP2 : 2 ≤ lemma23PaperP D := by
    have hh := lemma81_three_T_cube_le_P hL
    linarith only [hh,hT3]
  have hP4 : lemma61PaperP4 D ≤ lemma23PaperP D/4 := by
    have hh := mul_le_mul_of_nonneg_left (lemma81_T_inverse_square_le_exp_neg_log hL)
      (pow_nonneg hLp.le 519)
    have hsmall : lemma56PaperT D^(-2 : ℤ)*lemma51PaperT0 D ≤ 1/4 := by
      unfold lemma51PaperT0
      linarith only [hh,(hN₀ D hN).le]
    unfold lemma61PaperP4
    have hb := mul_le_mul_of_nonneg_left hsmall hPp.le
    nlinarith only [hb]
  refine ⟨Nat.le_floor ?_,Nat.le_floor ?_,Nat.le_floor ?_⟩
  · have hnonneg : 0 ≤ 2*lemma61PaperP4 D :=
      mul_nonneg (by norm_num) (lemma61_P4_pos (lemma61_parameters_at_threshold h61).1).le
    have hh := (Nat.ceil_lt_add_one hnonneg).le
    linarith only [hh,hP4,hP2]
  · have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*lemma56PaperT D^2)).le
    have hbound := lemma81_three_T_cube_le_P hL
    linarith only [hh,hT2,hT3,hbound]
  · have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ lemma56PaperT D^3)).le
    have hbound := lemma81_three_T_cube_le_P hL
    linarith only [hh,hT3,hbound]

end ZhangLS.Spec
