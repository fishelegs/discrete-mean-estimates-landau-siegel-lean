import ZhangLS.Spec.Lemma51GammaFactors

/-! # The original Lemma 5.1 region and its uniform height error -/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

noncomputable def lemma51PaperT0 (D : ℕ) : ℝ := lemma23PaperL D ^ 519

def Lemma51InRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| ≤ lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2

def Lemma51InExtendedRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| ≤ lemma44PaperAlpha D ∧
    |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3

theorem lemma51_alpha_le_quarter {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma44PaperAlpha D ≤ 1 / 4 := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpow : (3 : ℝ) ^ 3 ≤ lemma23PaperL D ^ 9 :=
    (pow_le_pow_left₀ (by norm_num) hL 3).trans
      (pow_le_pow_right₀ hL1 (by norm_num))
  norm_num at hpow
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  apply (div_le_iff₀ (by positivity : 0 < lemma23PaperL D ^ 9)).mpr
  nlinarith [Real.pi_le_four]

theorem lemma51_extended_region_data {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    0 < s.re ∧ s.re < 1 ∧ lemma51PaperT0 D ≤ s.im ∧
      |s.im - (lemma23PaperCenter D).im| ≤ 3 * lemma23PaperL D ^ 405 ∧
      Lemma44InExtendedGammaRegion D s := by
  have ha := lemma51_alpha_le_quarter hL
  have hre := abs_le.mp hs.1
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpow : lemma23PaperL D ^ 405 ≤ lemma23PaperL D ^ 519 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hpow3 : 3 ≤ lemma23PaperL D ^ 405 :=
    hL.trans (le_self_pow₀ hL1 (by norm_num))
  have ht := (abs_le.mp hs.2).1
  change -(2 * lemma23PaperL D ^ 405 + 3) ≤
    s.im - 2 * Real.pi * lemma23PaperL D ^ 519 at ht
  refine ⟨by linarith, by linarith, ?_, ?_, ⟨by linarith [hs.1], hs.2⟩⟩
  · unfold lemma51PaperT0
    nlinarith [Real.one_le_pi_div_two]
  · exact hs.2.trans (by linarith)

theorem lemma51_abs_log_sub_le {a b m : ℝ} (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have hpos (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x :=
    hm.trans_le ((le_min ha hb).trans hx.1)
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivWithinAt Real.log x⁻¹ (uIcc a b) x :=
    (Real.hasDerivAt_log (hpos x hx).ne').hasDerivWithinAt
  have hn (x : ℝ) (hx : x ∈ uIcc a b) : ‖x⁻¹‖ ≤ 1 / m := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hpos x hx), one_div]
    exact (inv_le_inv₀ (hpos x hx) hm).mpr ((le_min ha hb).trans hx.1)
  have ht := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hn
    (convex_uIcc a b) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs, abs_sub_comm, div_eq_mul_inv, mul_comm] using ht

theorem lemma51_height_log_error {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    |Real.log (s.im / (2 * Real.pi)) - Real.log (lemma51PaperT0 D)| ≤
      3 * lemma23PaperL D ^ (-114 : ℤ) := by
  have hh := lemma51_extended_region_data hL hs
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have ht : 0 < s.im := hT.trans_le hh.2.2.1
  have hc : lemma51PaperT0 D ≤ (lemma23PaperCenter D).im := by
    change lemma23PaperL D ^ 519 ≤ 2 * Real.pi * lemma23PaperL D ^ 519
    nlinarith [Real.one_le_pi_div_two, pow_pos hLpos 519]
  have hb := lemma51_abs_log_sub_le hT hh.2.2.1 hc
  have he : Real.log (s.im / (2 * Real.pi)) - Real.log (lemma51PaperT0 D) =
      Real.log s.im - Real.log (lemma23PaperCenter D).im := by
    rw [Real.log_div ht.ne' (by positivity : 2 * Real.pi ≠ 0)]
    change _ = Real.log s.im - Real.log (2 * Real.pi * lemma51PaperT0 D)
    rw [Real.log_mul (by positivity) hT.ne']
    ring
  rw [he]
  apply hb.trans
  calc
    _ ≤ 3 * lemma23PaperL D ^ 405 / lemma51PaperT0 D :=
      div_le_div_of_nonneg_right hh.2.2.2.1 hT.le
    _ = 3 * lemma23PaperL D ^ (-114 : ℤ) := by
      unfold lemma51PaperT0
      rw [div_eq_mul_inv, mul_assoc, ← zpow_natCast (lemma23PaperL D) 405,
        ← zpow_natCast (lemma23PaperL D) 519, ← zpow_neg,
        ← zpow_add₀ hLpos.ne']
      norm_num

theorem lemma51_DirichletZ_logDeriv_at_T0 {D N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma51InExtendedRegion D s) :
    ‖logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (lemma51PaperT0 D) : ℂ)‖ ≤ 21 * lemma23PaperL D ^ (-114 : ℤ) := by
  have hh := lemma51_extended_region_data hL hs
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hT : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hT3 : 3 ≤ lemma51PaperT0 D :=
    hL.trans (le_self_pow₀ hL1 (by norm_num))
  have ht : 0 < s.im := hT.trans_le hh.2.2.1
  have hg := lemma51_DirichletZ_logDeriv_sharp θ hθ hN hh.1 hh.2.1
    (by linarith [hh.2.2.1])
  have hlog := lemma51_height_log_error hL hs
  have hi : 1 / s.im ≤ lemma23PaperL D ^ (-114 : ℤ) := by
    calc
      1 / s.im ≤ 1 / lemma51PaperT0 D :=
        one_div_le_one_div_of_le hT hh.2.2.1
      _ = lemma23PaperL D ^ (-519 : ℤ) := by
        change 1 / lemma23PaperL D ^ (519 : ℕ) = (lemma23PaperL D ^ (519 : ℕ))⁻¹
        exact one_div _
      _ ≤ lemma23PaperL D ^ (-114 : ℤ) := zpow_le_zpow_right₀ hL1 (by norm_num)
  have hn : ‖((Real.log (lemma51PaperT0 D) - Real.log (s.im / (2 * Real.pi)) : ℝ) : ℂ)‖ ≤
      3 * lemma23PaperL D ^ (-114 : ℤ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] using hlog
  have he : logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (lemma51PaperT0 D) : ℂ) =
      (logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
        (Real.log (s.im / (2 * Real.pi)) : ℂ)) +
      ((Real.log (lemma51PaperT0 D) - Real.log (s.im / (2 * Real.pi)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hgi : 18 / s.im ≤ 18 * lemma23PaperL D ^ (-114 : ℤ) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 18)
  linarith

theorem lemma51_family_log_error {D p : ℕ}
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ) :
    0 ≤ Real.log (p : ℝ) - Real.log (lemma23PaperP D) ∧
      Real.log (p : ℝ) - Real.log (lemma23PaperP D) ≤ lemma23PaperL D ^ (-68 : ℤ) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp : (0 : ℝ) < p := hP.trans hψ.2.2.1
  have hlo := Real.log_le_log hP hψ.2.2.1.le
  have hratio : (p : ℝ) / lemma23PaperP D ≤ 1 + lemma23PaperL D ^ (-68 : ℤ) :=
    (div_le_iff₀ hP).mpr (by nlinarith [hψ.2.2.2])
  have hl := Real.log_le_sub_one_of_pos (div_pos hp hP)
  rw [Real.log_div hp.ne' hP.ne'] at hl
  exact ⟨by linarith, by linarith⟩

theorem lemma51_family_conductor_logs {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    Real.log (p : ℝ) ≤ 2 * lemma23PaperL D ^ 9 ∧
      Real.log ((D * p : ℕ) : ℝ) ≤ 2 * lemma23PaperL D ^ 9 := by
  have hlogp := (lemma44_family_log_bound hL ψ hψ).2
  simp only [lemma23PaperP, Real.log_exp] at hlogp
  have hlogDp : Real.log ((D * p : ℕ) : ℝ) = lemma23PaperL D + Real.log (p : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul
      (by exact_mod_cast χ.modulus_ne_zero) (by exact_mod_cast NeZero.ne p)]
    rfl
  have hpow : lemma23PaperL D ^ 2 ≤ lemma23PaperL D ^ 9 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  rw [hlogDp]
  constructor <;> nlinarith

end ZhangLS.Spec
