import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The reference exponential model in Proposition 2.2

Zhang's local zero-counting argument compares the normalized Dirichlet product with
`1 - P ^ (-2 w)`.  This file isolates the exact zero lattice of the model, independently of the
Rouché theorem that must transfer its zero count to the analytic function being approximated.
-/

namespace ZhangLS.Spec

/-- The exponential form of the reference function `1 - P ^ (-2w)`, with `L = log P`. -/
noncomputable def lemma23ExponentialGapModel (L : ℝ) (w : ℂ) : ℂ :=
  1 - Complex.exp (-2 * w * (L : ℂ))

/-- The zeros of the reference exponential model form the expected imaginary lattice. -/
theorem lemma23_exponential_gap_model_zero_iff
    {L : ℝ} (hL : 0 < L) (w : ℂ) :
    lemma23ExponentialGapModel L w = 0 ↔
      w.re = 0 ∧ ∃ n : ℤ, w.im = -(n : ℝ) * (Real.pi / L) := by
  constructor
  · intro hw
    have hexp : Complex.exp (-2 * w * (L : ℂ)) = 1 := by
      exact (sub_eq_zero.mp (by simpa [lemma23ExponentialGapModel] using hw)).symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨?_, n, ?_⟩
    · have hRe := congrArg Complex.re hn
      norm_num [Complex.mul_re, Complex.mul_im] at hRe
      rcases hRe with hRe | hLzero
      · exact hRe
      · exact (hL.ne' hLzero).elim
    · have hIm := congrArg Complex.im hn
      norm_num [Complex.mul_re, Complex.mul_im] at hIm
      have hLne : L ≠ 0 := hL.ne'
      have hmul : w.im * L = -(n : ℝ) * Real.pi := by nlinarith [hIm]
      calc
        w.im = w.im * L / L := by field_simp [hLne]
        _ = (-(n : ℝ) * Real.pi) / L := by rw [hmul]
        _ = -(n : ℝ) * (Real.pi / L) := by ring
  · rintro ⟨hre, n, him⟩
    have harg : -2 * w * (L : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp [Complex.mul_re, hre]
      · simp [Complex.mul_im, hre, him]
        field_simp [hL.ne']
    rw [lemma23ExponentialGapModel, harg]
    have hperiod := Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩
    rw [hperiod]
    simp

/-- The reference exponential model has a nonzero derivative at each of its zeros, so all its
zeros have multiplicity one. -/
theorem lemma23_exponential_gap_model_simple_zero
    {L : ℝ} (hL : 0 < L) {w : ℂ}
    (hzero : lemma23ExponentialGapModel L w = 0) :
    deriv (fun z : ℂ => lemma23ExponentialGapModel L z) w ≠ 0 := by
  have harg : HasDerivAt (fun z : ℂ => -2 * z * (L : ℂ))
      (-2 * (L : ℂ)) w := by
    convert (hasDerivAt_id (x := w)).const_mul (-2 * (L : ℂ)) using 1
    · ext z
      simp only [id_eq]
      ring
    · ring
  have hexp := harg.cexp
  have hmodel := (hasDerivAt_const (x := w) (1 : ℂ)).sub hexp
  have hderiv : HasDerivAt (fun z : ℂ => lemma23ExponentialGapModel L z)
      (-(Complex.exp (-2 * w * (L : ℂ)) * (-2 * (L : ℂ)))) w := by
    simpa [lemma23ExponentialGapModel] using hmodel
  have hexp_eq : Complex.exp (-2 * w * (L : ℂ)) = 1 := by
    exact (sub_eq_zero.mp (by simpa [lemma23ExponentialGapModel] using hzero)).symm
  rw [hderiv.deriv, hexp_eq]
  simp [hL.ne']

/-- The analytic order of the reference model at any zero is exactly one. -/
theorem lemma23_exponential_gap_model_order_one
    {L : ℝ} (hL : 0 < L) {w : ℂ}
    (hzero : lemma23ExponentialGapModel L w = 0) :
    analyticOrderAt (fun z : ℂ => lemma23ExponentialGapModel L z) w = 1 := by
  have hanalytic : AnalyticAt ℂ (fun z : ℂ => lemma23ExponentialGapModel L z) w := by
    unfold lemma23ExponentialGapModel
    fun_prop
  exact hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero
    (lemma23_exponential_gap_model_simple_zero hL hzero)

/-- If the model zero lies strictly inside the radius `2π/L`, then it is one of its three
central lattice zeros `0` or `± iπ/L`.  In particular this applies to the slightly enlarged
radius `α(1+c' α 𝓛)` in Lemma 4.7 whenever `c' α 𝓛 < 1`. -/
theorem lemma23_exponential_gap_model_zero_in_two_alpha_ball
    {L : ℝ} (hL : 0 < L) {w : ℂ}
    (hw : ‖w‖ < 2 * (Real.pi / L))
    (hzero : lemma23ExponentialGapModel L w = 0) :
    w = 0 ∨ w = ((Real.pi / L : ℝ) : ℂ) * Complex.I ∨
      w = -((Real.pi / L : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hre, n, him⟩ :=
    (lemma23_exponential_gap_model_zero_iff hL w).mp hzero
  have hα : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have hImNorm : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have hnabs : |(n : ℝ)| < 2 := by
    have himAbs : |w.im| = |(n : ℝ)| * (Real.pi / L) := by
      rw [him, abs_mul, abs_neg, abs_of_pos hα]
    have hmul : |(n : ℝ)| * (Real.pi / L) < 2 * (Real.pi / L) := by
      calc
        |(n : ℝ)| * (Real.pi / L) = |w.im| := himAbs.symm
        _ ≤ ‖w‖ := hImNorm
        _ < 2 * (Real.pi / L) := hw
    nlinarith [hmul, hα]
  have hnlt : -2 < (n : ℝ) ∧ (n : ℝ) < 2 := abs_lt.mp hnabs
  have hn_cases : n = -1 ∨ n = 0 ∨ n = 1 := by
    have hnlo : (-2 : ℤ) < n := by exact_mod_cast hnlt.1
    have hnhi : n < (2 : ℤ) := by exact_mod_cast hnlt.2
    omega
  rcases hn_cases with hn | hn | hn
  · right
    left
    apply Complex.ext
    · simp [hre]
    · simp [him, hn]
  · left
    apply Complex.ext
    · exact hre
    · simp [him, hn]
  · right
    right
    apply Complex.ext
    · simp [hre]
    · simp [him, hn]

/-- For any radius strictly between `α` and `2α`, the open disk contains exactly the three
central zeros of the reference model (as a set).  The strict upper bound is what excludes the
next lattice points `±2iα`. -/
theorem lemma23_exponential_gap_model_zeros_in_disk_iff
    {L R : ℝ} (hL : 0 < L)
    (hRlo : Real.pi / L < R) (hRhi : R < 2 * (Real.pi / L))
    (w : ℂ) :
    (‖w‖ < R ∧ lemma23ExponentialGapModel L w = 0) ↔
      w = 0 ∨ w = ((Real.pi / L : ℝ) : ℂ) * Complex.I ∨
        w = -((Real.pi / L : ℝ) : ℂ) * Complex.I := by
  constructor
  · rintro ⟨hw, hzero⟩
    exact lemma23_exponential_gap_model_zero_in_two_alpha_ball hL
      (lt_trans hw hRhi) hzero
  · rintro (rfl | rfl | rfl)
    · refine ⟨?_, ?_⟩
      · simpa using lt_trans (div_pos Real.pi_pos hL) hRlo
      · exact (lemma23_exponential_gap_model_zero_iff hL 0).2
          ⟨by simp, 0, by simp⟩
    · refine ⟨?_, ?_⟩
      · simpa [abs_of_pos Real.pi_pos, abs_of_pos hL] using hRlo
      · exact (lemma23_exponential_gap_model_zero_iff hL _).2
          ⟨by simp, -1, by simp⟩
    · refine ⟨?_, ?_⟩
      · simpa [abs_of_pos Real.pi_pos, abs_of_pos hL] using hRlo
      · exact (lemma23_exponential_gap_model_zero_iff hL _).2
          ⟨by simp, 1, by simp⟩

end ZhangLS.Spec
