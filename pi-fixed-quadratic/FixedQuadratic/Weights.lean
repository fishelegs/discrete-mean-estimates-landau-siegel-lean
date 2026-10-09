import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace FixedQuadratic

/-- The height-linked ceiling weight has only the displayed exp(nu) cost. -/
theorem height_rpow_le_rounded_exp (H ν : ℝ) (hH : 1 ≤ H) (hν : 0 ≤ ν) :
    H^(-ν) ≤ Real.exp ν * Real.exp (-ν*(Nat.ceil (Real.log H) : ℝ)) := by
  have hp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hl : 0 ≤ Real.log H := Real.log_nonneg hH
  have hw : (Nat.ceil (Real.log H) : ℝ) ≤ Real.log H+1 :=
    (Nat.ceil_lt_add_one hl).le
  rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The new approximation input transfers to the original complex period. -/
theorem quadratic_center_period_error (β H ν : ℝ) (j k : ℕ)
    (hH : 1 ≤ H) (hν : 0 ≤ ν) (hjk : j ≤ k)
    (happrox : |Real.pi-β| ≤ H^(-ν)) :
    ‖(j : ℂ)*(2*Complex.I*(β : ℂ)-2*(Real.pi : ℂ)*Complex.I)‖ ≤
      2*(k : ℝ)*Real.exp ν * Real.exp (-ν*(Nat.ceil (Real.log H) : ℝ)) := by
  have he : (j : ℂ)*(2*Complex.I*(β : ℂ)-2*(Real.pi : ℂ)*Complex.I) =
      (2*(j : ℂ))*Complex.I*((β-Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [he, norm_mul, norm_mul]
  norm_num only [norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [hnorm2, mul_one]
  have hd0 : |β-Real.pi| ≤ H^(-ν) := by simpa [abs_sub_comm] using happrox
  have hdist : |β-Real.pi| ≤ Real.exp ν * Real.exp (-ν*(Nat.ceil (Real.log H) : ℝ)) :=
    hd0.trans (height_rpow_le_rounded_exp H ν hH hν)
  have hkr : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hp : 0 ≤ Real.exp ν * Real.exp (-ν*(Nat.ceil (Real.log H) : ℝ)) := by positivity
  calc
    _ ≤ 2*(j : ℝ)*(Real.exp ν * Real.exp (-ν*(Nat.ceil (Real.log H) : ℝ))) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hkr hp
      nlinarith [hh]

/-- Nonzero real centers are pairwise distinct in each coordinate. -/
theorem quadratic_centers_injective (β : ℝ) (hβ : β ≠ 0) (k : ℕ) :
    Function.Injective (fun j : Fin k => (j.val : ℂ)*(2*Complex.I*(β : ℂ))) := by
  have hp : (2*Complex.I*(β : ℂ)) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    exact_mod_cast hβ
  intro j l h
  have he : (j.val : ℂ) = (l.val : ℂ) := mul_right_cancel₀ hp h
  apply Fin.ext
  exact_mod_cast he

end FixedQuadratic
