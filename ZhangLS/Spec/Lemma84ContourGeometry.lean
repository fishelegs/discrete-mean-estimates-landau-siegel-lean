import ZhangLS.Spec.Lemma84ActualPoleStructure
import ZhangLS.Spec.Lemma44LocalRectangle
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
open scoped Topology
set_option maxHeartbeats 1500000

lemma lemma84_exceptional_zero_within_alpha {D : ℕ} (hL : 100 ≤ lemma23PaperL D)
    {ρ : ℝ} (hρ : 0 < 1-ρ) (hclose : 1-ρ ≤ 64*lemma23PaperL D^(-2022 : ℤ)) :
    ‖(ρ:ℂ)-1‖ ≤ lemma44PaperAlpha D := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hp := zpow_le_zpow_right₀ hL1 (by norm_num : (-2022:ℤ) ≤ -10)
  have hsc : 64/lemma23PaperL D ≤ Real.pi := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith only [hL,Real.two_le_pi]
  have he : 64*lemma23PaperL D^(-10 : ℤ) =
      (64/lemma23PaperL D)*lemma23PaperL D^(-9 : ℤ) := by
    rw [div_eq_mul_inv,← zpow_neg_one,mul_assoc,
      ← zpow_add₀ hLp.ne']
    norm_num
  have hnorm : ‖(ρ:ℂ)-1‖ = 1-ρ := by
    rw [← Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_neg (by linarith only [hρ] : ρ-1 < 0)]
    ring
  rw [hnorm,lemma58_alpha_eq_log_power]
  exact hclose.trans ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans
    (he.le.trans (mul_le_mul_of_nonneg_right hsc (zpow_nonneg hLp.le _))))

lemma lemma84_paper_rectangle_geometry {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    0 < lemma44PaperAlpha D ∧
      5*lemma44PaperAlpha D < -(-1/lemma23PaperL D) ∧
      5*lemma44PaperAlpha D < 6*lemma44PaperAlpha D ∧
      5*lemma44PaperAlpha D < (D:ℝ) ∧
      6*lemma44PaperAlpha D ≤ 1/lemma23PaperL D := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hα := lemma83_alpha_small (by linarith only [hL] : 100 ≤ lemma23PaperL D)
  have hsmall := lemma58_original_radius_in_taylor_disk hL
  have hquarter : 1/(4*lemma23PaperL D) < 1/lemma23PaperL D :=
    one_div_lt_one_div_of_lt hLp (by linarith)
  have hDpos : (1:ℝ) < D := by exact_mod_cast hD
  refine ⟨hα.1,?_,by linarith only [hα.1],by linarith only [hα.2,hDpos],?_⟩
  · simp only [neg_div,neg_neg]
    change 10*lemma44PaperAlpha D ≤ 1/(4*lemma23PaperL D) at hsmall
    linarith only [hsmall,hquarter,hα.1]
  · change 10*lemma44PaperAlpha D ≤ 1/(4*lemma23PaperL D) at hsmall
    linarith only [hsmall,hquarter,hα.1]

lemma lemma84_ball_subset_rectangle {a b T R : ℝ}
    (ha : R < -a) (hb : R < b) (hT : R < T) :
    closedBall (0:ℂ) R ⊆ lemma44ClosedRectangle a b T := by
  intro s hs
  have hn : ‖s‖ ≤ R := by simpa using mem_closedBall_iff_norm.mp hs
  have hre := abs_le.mp ((Complex.abs_re_le_norm s).trans hn)
  have him := abs_le.mp ((Complex.abs_im_le_norm s).trans hn)
  exact ⟨⟨by linarith only [hre.1,ha],by linarith only [hre.2,hb]⟩,
    ⟨by linarith only [him.1,hT],by linarith only [him.2,hT]⟩⟩

lemma lemma84_rectangle_inside_analytic_region {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    lemma44ClosedRectangle (-1/lemma23PaperL D) (6*lemma44PaperAlpha D) D ⊆
      lemma84AnalyticRegion D := by
  intro s hs
  have hLp : 0 < lemma23PaperL D := by linarith
  have hinv : 1/lemma23PaperL D ≤ (1:ℝ)/100 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
  have hinvp : 0 < 1/lemma23PaperL D := by positivity
  have hDpos : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hre : -(1/lemma23PaperL D) ≤ s.re := by simpa only [neg_div] using hs.1.1
  have him : |s.im| ≤ D := abs_le.mpr hs.2
  constructor
  · simp only [Complex.add_re,Complex.one_re]
    linarith only [hre,hinv]
  · constructor
    · simp only [Complex.add_re,Complex.one_re]
      change 1-2/lemma23PaperL D < 1+s.re
      have he : 2/lemma23PaperL D = 2*(1/lemma23PaperL D) := by ring
      rw [he]
      linarith only [hre,hinvp]
    · simp only [Complex.add_im,Complex.one_im,zero_add]
      linarith only [him,hDpos]

lemma lemma84_paper_ball_inside_analytic_region {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    closedBall (0:ℂ) (5*lemma44PaperAlpha D) ⊆ lemma84AnalyticRegion D := by
  have h := lemma84_paper_rectangle_geometry hD hL
  exact (lemma84_ball_subset_rectangle h.2.1 h.2.2.1 h.2.2.2.1).trans
    (lemma84_rectangle_inside_analytic_region hD hL)

end ZhangLS.Spec
