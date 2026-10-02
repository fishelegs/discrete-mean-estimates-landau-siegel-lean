import ZhangLS.Spec.Lemma82LocalMainTerm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ZhangLS.Spec
open Filter Topology
open scoped Real
set_option maxHeartbeats 1000000

lemma lemma82_tail_absorption_eventually :
    ∀ᶠ D : ℕ in atTop, ∀ x : ℝ, lemma56PaperT D < x →
      (D:ℝ)/x ≤ lemma23PaperL D^(-6:ℤ) := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp ht).eventually_ge_atTop 2
  have he := ht.eventually ((Real.isLittleO_pow_exp_atTop (n := 6)).bound (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop (2:ℕ), ht.eventually_ge_atTop 1, hr, he]
    with D hD hL hr he
  intro x hx
  have hDp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  have hLp : 0 < lemma23PaperL D := by linarith
  have heD : Real.exp (lemma23PaperL D) = (D:ℝ) := Real.exp_log hDp
  change 2 ≤ lemma23PaperL D^(1/10:ℝ) at hr
  have hpow : lemma23PaperL D^6 ≤ (D:ℝ) := by
    simpa only [heD, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hLp.le 6),
      abs_of_pos hDp, one_mul] using he
  have hpower : 2*lemma23PaperL D ≤ lemma23PaperL D^(11/10:ℝ) := by
    rw [show (11/10:ℝ)=1+1/10 by norm_num, Real.rpow_add hLp, Real.rpow_one]
    nlinarith
  have hTsq : (D:ℝ)^2 ≤ lemma56PaperT D := by
    have hh := Real.exp_le_exp.mpr hpower
    rw [two_mul, Real.exp_add, heD] at hh
    simpa only [pow_two, lemma56PaperT] using hh
  have hTp : 0 < lemma56PaperT D := Real.exp_pos _
  have hxp : 0 < x := hTp.trans hx
  rw [zpow_neg,← one_div]
  norm_num only [zpow_ofNat]
  apply (div_le_div_iff₀ hxp (pow_pos hLp 6)).mpr
  have hm := mul_le_mul_of_nonneg_left hpow hDp.le
  nlinarith

lemma lemma82_uniform_threshold (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      2 ≤ D ∧ 2000 ≤ lemma23PaperL D ∧
      c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10 ∧
      ∀ x : ℝ, lemma56PaperT D < x → (D:ℝ)/x ≤ lemma23PaperL D^(-6:ℤ) := by
  obtain ⟨Dc,_,hsmall⟩ := lemma46_exists_contraction_threshold (c := 5*c) (by positivity)
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨D₀,hD₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ Dc ≤ D ∧ 2000 ≤ lemma23PaperL D ∧
      (∀ x : ℝ, lemma56PaperT D < x → (D:ℝ)/x ≤ lemma23PaperL D^(-6:ℤ)) from by
    filter_upwards [eventually_ge_atTop (2:ℕ),eventually_ge_atTop Dc,
      ht.eventually_ge_atTop 2000, lemma82_tail_absorption_eventually] with D h2 hc hL htail
    exact ⟨h2,hc,hL,htail⟩)
  refine ⟨D₀,(hD₀ D₀ le_rfl).1,?_⟩
  intro D hD
  have hh := hD₀ D hD
  refine ⟨hh.1,hh.2.2.1,?_,hh.2.2.2⟩
  have hs := hsmall D hh.2.1
  nlinarith only [hs]

end ZhangLS.Spec
