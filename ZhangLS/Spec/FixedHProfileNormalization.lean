import ZhangLS.Spec.FixedHProfileBump
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The literal supremum normalization and positive fixed-H energy. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHProfile
open Set Function
open scoped Classical ContDiff
set_option maxHeartbeats 2000000

noncomputable def normalization : ℝ := sSup (Set.range (fun v => |iteratedDeriv 3 beta v|))
noncomputable def F0 (v : ℝ) : ℝ := iteratedDeriv 3 beta v / normalization

lemma beta_third_abs_bddAbove : BddAbove (Set.range (fun v => |iteratedDeriv 3 beta v|)) := by
  have hc := (beta_derivative_hasCompactSupport 3).isCompact_range
    (beta_derivative_contDiff 3).continuous
  have hi := hc.image continuous_abs
  have he : abs '' Set.range (iteratedDeriv 3 beta) =
      Set.range (fun v => |iteratedDeriv 3 beta v|) := by
    ext x
    constructor
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩; exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩; exact ⟨iteratedDeriv 3 beta v, ⟨v, rfl⟩, rfl⟩
  rw [he] at hi
  exact hi.bddAbove

lemma beta_third_abs_le_normalization (v : ℝ) : |iteratedDeriv 3 beta v| ≤ normalization := by
  exact le_csSup beta_third_abs_bddAbove (Set.mem_range_self v)

lemma normalization_pos : 0 < normalization := by
  obtain ⟨v, hv⟩ := beta_third_derivative_not_zero
  exact (abs_pos.mpr hv).trans_le (beta_third_abs_le_normalization v)

lemma F0_contDiff : ContDiff ℝ ∞ F0 := by
  exact (beta_derivative_contDiff 3).div_const normalization

lemma F0_abs_le_one (v : ℝ) : |F0 v| ≤ 1 := by
  rw [F0, abs_div, abs_of_pos normalization_pos]
  exact (div_le_one normalization_pos).mpr (beta_third_abs_le_normalization v)

lemma F0_tsupport : tsupport F0 ⊆ Set.Icc (0 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  have hg : iteratedDeriv 3 beta v ≠ 0 := by
    intro hz
    exact hv (by simp [F0, hz])
  exact beta_derivative_tsupport 3 (subset_tsupport _ hg)

lemma F0_hasCompactSupport : HasCompactSupport F0 := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) F0_tsupport

lemma F0_not_zero : ∃ v : ℝ, F0 v ≠ 0 := by
  obtain ⟨v, hv⟩ := beta_third_derivative_not_zero
  exact ⟨v, div_ne_zero hv normalization_pos.ne'⟩

lemma F0_square_integral_pos : 0 < ∫ v in (0 : ℝ)..1, |F0 v| ^ 2 := by
  obtain ⟨v, hv⟩ := F0_not_zero
  apply intervalIntegral.integral_pos (by norm_num)
    ((F0_contDiff.continuous.abs.pow 2).continuousOn)
  · intro x hx; positivity
  · exact ⟨v, F0_tsupport (subset_tsupport _ hv), pow_pos (abs_pos.mpr hv) 2⟩

lemma F0_square_intervalIntegrable :
    IntervalIntegrable (fun v => |F0 v| ^ 2) MeasureTheory.volume 0 1 := by
  exact (F0_contDiff.continuous.abs.pow 2).intervalIntegrable _ _

lemma F0_deriv_square_intervalIntegrable :
    IntervalIntegrable (fun v => |deriv F0 v| ^ 2) MeasureTheory.volume 0 1 := by
  exact ((F0_contDiff.iterate_deriv 1).continuous.abs.pow 2).intervalIntegrable _ _

noncomputable def fixedLambda : ℝ :=
  (16000 / Real.pi) * (∫ v in (0 : ℝ)..1, |deriv F0 v| ^ 2) +
    (11 * Real.pi / 250) * (∫ v in (0 : ℝ)..1, |F0 v| ^ 2)

lemma fixedLambda_pos : 0 < fixedLambda := by
  have hderiv : 0 ≤ ∫ v in (0 : ℝ)..1, |deriv F0 v| ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)
  have hfirst : 0 ≤ (16000 / Real.pi) * (∫ v in (0 : ℝ)..1, |deriv F0 v| ^ 2) :=
    mul_nonneg (by positivity) hderiv
  have hsecond : 0 < (11 * Real.pi / 250) * (∫ v in (0 : ℝ)..1, |F0 v| ^ 2) :=
    mul_pos (by positivity) F0_square_integral_pos
  exact add_pos_of_nonneg_of_pos hfirst hsecond

end ZhangLS.Spec.FixedHProfile
