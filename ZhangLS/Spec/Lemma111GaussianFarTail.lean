import ZhangLS.Spec.Lemma111StrictVariation
import ZhangLS.Spec.Lemma112ShortCutoff
import ZhangLS.Spec.Lemma112SumExchange
import ZhangLS.Spec.Lemma82Definitions

/-! Actual infinite Gaussian tails at the strict cutoff `2 P^(63/125)`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset MeasureTheory
open scoped BigOperators Real Topology

lemma lemma111_gaussian_interval_tail {D : ℕ} (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) {q a b c B : ℝ} (hq : 0 < q)
    (hab : a ≤ b) (hbc : b ≤ c) (hB : lemma23PaperP D ^ c * q ≤ B)
    (hlogB : Real.log B ≤ 2 * lemma23PaperL D ^ 9)
    {n : ℕ} (hn : 0 < n) (hcut : 2 * B ≤ (n : ℝ)) :
    |∫ z in a..b, zhangGaussianWeight D (lemma23PaperP D ^ z * q / n)| ≤
      (Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ)^2)⁻¹) * (b-a) := by
  have hP : 1 ≤ lemma23PaperP D := by
    exact Real.one_le_exp_iff.mpr (pow_nonneg (Real.log_natCast_nonneg D) _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBp : 0 < B := lt_of_lt_of_le
    (mul_pos (Real.rpow_pos_of_pos (Real.exp_pos _) c) hq) hB
  have hbnd : ∀ z ∈ Set.uIoc a b,
      ‖zhangGaussianWeight D (lemma23PaperP D ^ z * q / n)‖ ≤
        Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ)^2)⁻¹ := by
    intro z hz
    have hz' : z ≤ c := (by simpa only [Set.uIoc_of_le hab] using hz : z ∈ Set.Ioc a b).2.trans hbc
    have hzp : 0 < lemma23PaperP D ^ z * q :=
      mul_pos (Real.rpow_pos_of_pos (Real.exp_pos _) z) hq
    have hzb : lemma23PaperP D ^ z * q ≤ B :=
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hP hz') hq.le).trans hB
    rw [Real.norm_eq_abs, abs_of_nonneg (zhangGaussianWeight_nonneg hD (div_pos hzp hnR))]
    exact lemma61_cutoff_gaussian_weight_bound hL hzp
      ((Real.log_le_log hzp hzb).trans hlogB) hn
      ((mul_le_mul_of_nonneg_left hzb (by norm_num)).trans hcut)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbnd

lemma lemma111_smoothed_one_far_bound {D : ℕ} (hD : 1 < D)
    (hL : 3 ≤ lemma23PaperL D) {n : ℕ} (hn : 0 < n)
    (hcut : 2 * lemma112PaperP1 D ≤ (n : ℝ)) :
    |lemma111SmoothedOne D n| ≤
      2 * Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ)^2)⁻¹ := by
  have hlog : Real.log (lemma112PaperP1 D) ≤ 2 * lemma23PaperL D ^ 9 := by
    rw [lemma112PaperP1, Real.log_rpow (show 0 < lemma23PaperP D from Real.exp_pos _), lemma23PaperP, Real.log_exp]
    have h : 0 ≤ lemma23PaperL D ^ 9 := pow_nonneg (Real.log_natCast_nonneg D) 9
    nlinarith
  have hi (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 63/125) :=
    lemma111_gaussian_interval_tail hD hL (q := 1) (c := 63/125)
      (by norm_num) hab hb (B := lemma112PaperP1 D) (by simp [lemma112PaperP1]) hlog hn hcut
  have h₁ := hi (1/2) (251/500) (by norm_num) (by norm_num)
  have h₂ := hi (251/500) (63/125) (by norm_num) (by norm_num)
  simp only [mul_one] at h₁ h₂
  unfold lemma111SmoothedOne
  have h := abs_add_le
    (-500 * (∫ z in (1/2:ℝ)..(251/500:ℝ), zhangGaussianWeight D (lemma23PaperP D ^ z / n)))
    (500 * (∫ z in (251/500:ℝ)..(63/125:ℝ), zhangGaussianWeight D (lemma23PaperP D ^ z / n)))
  simp only [abs_mul] at h
  norm_num at h₁ h₂ h
  simp only [neg_mul]
  linarith

lemma lemma111_smoothed_two_far_bound {D : ℕ} (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {n : ℕ} (hn : 0 < n)
    (hcut : 2 * lemma112PaperP1 D ≤ (n : ℝ)) :
    |lemma111SmoothedTwo D n| ≤
      2 * Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ)^2)⁻¹ := by
  have hlog : Real.log (lemma112PaperP1 D) ≤ 2 * lemma23PaperL D ^ 9 := by
    rw [lemma112PaperP1, Real.log_rpow (show 0 < lemma23PaperP D from Real.exp_pos _), lemma23PaperP, Real.log_exp]
    have h : 0 ≤ lemma23PaperL D ^ 9 := pow_nonneg (Real.log_natCast_nonneg D) 9
    nlinarith
  have hB : lemma23PaperP D ^ (1/2:ℝ) * lemma111ShiftScale D ≤ lemma112PaperP1 D := by
    have hx := lemma112_dual_scale_twice_below_cutoff hD hL (z := 1/2) le_rfl
    have hp := lemma112_dual_scale_pos hD (1/2)
    have he : lemma112DualScale D (1/2) =
        lemma23PaperP D ^ (1/2:ℝ) * lemma111ShiftScale D := by
      norm_num [lemma112DualScale, lemma51PaperT0, lemma111ShiftScale] <;> ring
    rw [he] at hx hp
    linarith
  have hi (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 1/2) :=
    lemma111_gaussian_interval_tail hD (by linarith) (lemma111_shift_scale_pos hD)
      (c := 1/2) hab hb (B := lemma112PaperP1 D) hB hlog hn hcut
  have h₁ := hi (62/125) (249/500) (by norm_num) (by norm_num)
  have h₂ := hi (249/500) (1/2) (by norm_num) (by norm_num)
  have he (z : ℝ) : lemma23PaperP D ^ z * lemma111ShiftScale D / (n:ℝ) =
      lemma23PaperP D ^ z * (D:ℝ) * lemma23PaperL D ^ 519 / n := by
    dsimp [lemma111ShiftScale]
    ring
  simp_rw [he] at h₁ h₂
  unfold lemma111SmoothedTwo
  have h := abs_add_le
    (-500 * (∫ z in (62/125:ℝ)..(249/500:ℝ), zhangGaussianWeight D
      (lemma23PaperP D ^ z * (D:ℝ) * lemma23PaperL D ^ 519 / n)))
    (500 * (∫ z in (249/500:ℝ)..(1/2:ℝ), zhangGaussianWeight D
      (lemma23PaperP D ^ z * (D:ℝ) * lemma23PaperL D ^ 519 / n)))
  simp only [abs_mul] at h
  norm_num at h₁ h₂ h
  simp only [neg_mul]
  linarith

lemma lemma111_series_strict_tail_reduction {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : 0 ≤ s.re) (w : ℝ → ℝ)
    (hsum : Summable (fun n : ℕ => LSeries.term (lemma112Coefficient χ ψ) s n * (w n : ℂ)))
    {X : ℝ} (hX : 0 ≤ X)
    (hfar : ∀ n : ℕ, 0 < n → X ≤ (n : ℝ) →
      |w n| ≤ 2 * Real.exp (-(lemma23PaperL D ^ 10)) * ((n : ℝ)^2)⁻¹) :
    ‖(∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n * (w n : ℂ)) -
      ∑ n ∈ lemma82StrictCutoff X, LSeries.term (lemma112Coefficient χ ψ) s n * (w n : ℂ)‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  classical
  let f : ℕ → ℂ := fun n => LSeries.term (lemma112Coefficient χ ψ) s n * (w n : ℂ)
  let short : ℕ → ℂ := fun n => if n ∈ lemma82StrictCutoff X then f n else 0
  have hshort : Summable short := summable_of_ne_finset_zero
    (s := lemma82StrictCutoff X) (fun n hn => by simp [short, hn])
  have hshortsum : (∑' n, short n) = ∑ n ∈ lemma82StrictCutoff X, f n := by
    rw [tsum_eq_sum (s := lemma82StrictCutoff X) (fun n hn => by simp [short, hn])]
    apply sum_congr rfl
    intro n hn
    simp [short, hn]
  have hp (n : ℕ) : ‖f n - short n‖ ≤
      (2 * Real.exp (-(lemma23PaperL D ^ 10))) * ((n : ℝ)^2)⁻¹ := by
    by_cases hn0 : n = 0
    · subst n
      simp [f, short]
    by_cases hm : n ∈ lemma82StrictCutoff X
    · simp only [short, if_pos hm, sub_self, norm_zero]
      positivity
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnX : X ≤ (n : ℝ) := le_of_not_gt
      (fun h => hm ((lemma82_mem_strictCutoff hX n).mpr ⟨hn,h⟩))
    have ht : ‖LSeries.term (lemma112Coefficient χ ψ) s n‖ ≤ 1 := by
      rw [LSeries.norm_term_eq, if_neg hn0]
      exact (div_le_self (norm_nonneg _) (Real.one_le_rpow (by exact_mod_cast hn) hs)).trans
        (lemma112_coefficient_norm_le_one χ ψ n)
    simp only [short, if_neg hm, sub_zero, f, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans
      (by simpa only [one_mul] using hfar n hn hnX)
  change ‖(∑' n, f n) - ∑ n ∈ lemma82StrictCutoff X, f n‖ ≤ _
  rw [← hshortsum, ← hsum.tsum_sub hshort]
  have hn := summable_norm_iff.mpr (hsum.sub hshort)
  apply (norm_tsum_le_tsum_norm hn).trans
  exact (hn.tsum_le_tsum hp (lemma44_inverse_square_summable.mul_left _)).trans_eq (by
    rw [tsum_mul_left]
    unfold lemma44InverseSquareMass
    ring)

/-- Full Gaussian series minus its positive strict finite cutoff, including
`n = 0` via the literal `LSeries.term_zero` convention. -/
lemma lemma111_smoothed_one_strict_tail {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma112JtildeOne χ ψ s -
      ∑ n ∈ lemma82StrictCutoff (2 * lemma112PaperP1 D),
        LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedOne D n : ℂ)‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  apply lemma111_series_strict_tail_reduction χ ψ hs (lemma111SmoothedOne D)
    (lemma112_JtildeOne_integral χ ψ s hD).1
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  · exact fun n hn hcut => lemma111_smoothed_one_far_bound hD hL hn hcut

lemma lemma111_smoothed_two_strict_tail {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma112JtildeTwo χ ψ s -
      ∑ n ∈ lemma82StrictCutoff (2 * lemma112PaperP1 D),
        LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedTwo D n : ℂ)‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  apply lemma111_series_strict_tail_reduction χ ψ hs (lemma111SmoothedTwo D)
    (lemma112_JtildeTwo_integral χ ψ s hD).1
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  · exact fun n hn hcut => lemma111_smoothed_two_far_bound hD hL hn hcut


lemma lemma111_tent_zero_of_ge {u : ℝ} (hu : 63/125 ≤ u) : lemma111Tent u = 0 := by
  rw [lemma111_tent_second_difference]
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma lemma111_tent_one_zero_of_cutoff {D : ℕ} (hD : 1 < D)
    {y : ℝ} (hcut : 2 * lemma112PaperP1 D ≤ y) :
    lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) = 0 := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hP1 : 0 < lemma112PaperP1 D := Real.rpow_pos_of_pos hP _
  have hlogP : 0 < Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP, Real.log_exp]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  apply lemma111_tent_zero_of_ge
  apply (le_div_iff₀ hlogP).mpr
  have h := Real.log_le_log hP1 (show lemma112PaperP1 D ≤ y by linarith)
  rw [lemma112PaperP1, Real.log_rpow hP] at h
  exact h

lemma lemma111_tent_two_zero_of_cutoff {D : ℕ} (hD : 1 < D)
    (hL : 64 ≤ lemma23PaperL D) {y : ℝ} (hcut : 2 * lemma112PaperP1 D ≤ y) :
    lemma111Tent (Real.log (y / lemma111ShiftScale D) /
      Real.log (lemma23PaperP D) + 1/250) = 0 := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hP1 : 0 < lemma112PaperP1 D := Real.rpow_pos_of_pos hP _
  have hq := lemma111_shift_scale_pos hD
  have hB := lemma112_dual_scale_twice_below_cutoff hD hL (z := 1/2) le_rfl
  have hBp := lemma112_dual_scale_pos hD (1/2)
  have he : lemma112DualScale D (1/2) =
      lemma23PaperP D ^ (1/2:ℝ) * lemma111ShiftScale D := by
    norm_num [lemma112DualScale, lemma51PaperT0, lemma111ShiftScale] <;> ring
  rw [he] at hB hBp
  have hby : lemma23PaperP D ^ (1/2:ℝ) ≤ y / lemma111ShiftScale D := by
    apply (le_div_iff₀ hq).mpr
    linarith
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hP (1/2:ℝ)) hby
  rw [Real.log_rpow hP] at hl
  have hlogP : 0 < Real.log (lemma23PaperP D) := by
    rw [lemma23PaperP, Real.log_exp]
    exact pow_pos (Real.log_pos (by exact_mod_cast hD)) _
  have hu : (1/2:ℝ) ≤ Real.log (y / lemma111ShiftScale D) / Real.log (lemma23PaperP D) :=
    (le_div_iff₀ hlogP).mpr hl
  apply lemma111_tent_zero_of_ge
  linarith

lemma lemma111_tent_one_series_strict_finite {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (s : ℂ) :
    (∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
      (lemma111Tent (Real.log n / Real.log (lemma23PaperP D)) : ℂ)) =
      ∑ n ∈ lemma82StrictCutoff (2 * lemma112PaperP1 D),
        LSeries.term (lemma112Coefficient χ ψ) s n *
          (lemma111Tent (Real.log n / Real.log (lemma23PaperP D)) : ℂ) := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hX : 0 ≤ 2 * lemma112PaperP1 D := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hcut : 2 * lemma112PaperP1 D ≤ (n:ℝ) := le_of_not_gt
    (fun h => hn ((lemma82_mem_strictCutoff hX n).mpr ⟨hnpos,h⟩))
  rw [lemma111_tent_one_zero_of_cutoff hD hcut]
  simp

lemma lemma111_tent_two_series_strict_finite {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) (s : ℂ) :
    (∑' n : ℕ, LSeries.term (lemma112Coefficient χ ψ) s n *
      (lemma111Tent (Real.log (n / lemma111ShiftScale D) /
        Real.log (lemma23PaperP D) + 1/250) : ℂ)) =
      ∑ n ∈ lemma82StrictCutoff (2 * lemma112PaperP1 D),
        LSeries.term (lemma112Coefficient χ ψ) s n *
          (lemma111Tent (Real.log (n / lemma111ShiftScale D) /
            Real.log (lemma23PaperP D) + 1/250) : ℂ) := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hX : 0 ≤ 2 * lemma112PaperP1 D := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hcut : 2 * lemma112PaperP1 D ≤ (n:ℝ) := le_of_not_gt
    (fun h => hn ((lemma82_mem_strictCutoff hX n).mpr ⟨hnpos,h⟩))
  rw [lemma111_tent_two_zero_of_cutoff hD hL hcut]
  simp


lemma lemma111_twice_P1_le_transfer_cutoff {D : ℕ} (hL : 64 ≤ lemma23PaperL D) :
    2 * lemma112PaperP1 D ≤ lemma23PaperP D ^ (101/200 : ℝ) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have h9 : (1000:ℝ) ≤ lemma23PaperL D ^ 9 := by
    have h := (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 64) hL 2).trans
      (pow_le_pow_right₀ h1 (by norm_num : 2 ≤ 9))
    norm_num at h
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    exact h
  apply (Real.log_le_log_iff
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hP _))
    (Real.rpow_pos_of_pos hP _)).mp
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hP (63/125:ℝ)).ne',
    Real.log_rpow hP, Real.log_rpow hP, lemma23PaperP, Real.log_exp]
  linarith

lemma lemma111_smoothed_one_P505_tail {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma112JtildeOne χ ψ s -
      ∑ n ∈ lemma82StrictCutoff (lemma23PaperP D ^ (101/200:ℝ)),
        LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedOne D n : ℂ)‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  apply lemma111_series_strict_tail_reduction χ ψ hs (lemma111SmoothedOne D)
    (lemma112_JtildeOne_integral χ ψ s hD).1
  · exact Real.rpow_nonneg (Real.exp_nonneg _) _
  · intro n hn hcut
    exact lemma111_smoothed_one_far_bound hD (by linarith) hn
      ((lemma111_twice_P1_le_transfer_cutoff hL).trans hcut)

lemma lemma111_smoothed_two_P505_tail {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma112JtildeTwo χ ψ s -
      ∑ n ∈ lemma82StrictCutoff (lemma23PaperP D ^ (101/200:ℝ)),
        LSeries.term (lemma112Coefficient χ ψ) s n * (lemma111SmoothedTwo D n : ℂ)‖ ≤
      2 * lemma44InverseSquareMass * Real.exp (-(lemma23PaperL D ^ 10)) := by
  apply lemma111_series_strict_tail_reduction χ ψ hs (lemma111SmoothedTwo D)
    (lemma112_JtildeTwo_integral χ ψ s hD).1
  · exact Real.rpow_nonneg (Real.exp_nonneg _) _
  · intro n hn hcut
    exact lemma111_smoothed_two_far_bound hD hL hn
      ((lemma111_twice_P1_le_transfer_cutoff hL).trans hcut)

end ZhangLS.Spec
