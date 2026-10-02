import ZhangLS.Spec.Lemma32FourierGeometricKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical

lemma lemma32_sine_unit_interval_lower {u : ℝ} (hu0 : 0≤u) (hu1 : u≤1) :
    2*min u (1-u) ≤ Real.sin (Real.pi*u) := by
  by_cases hh : u≤1/2
  · have h := Real.le_sin_mul (x := 2*u) (by linarith) (by linarith)
    have he : Real.pi/2*(2*u)=Real.pi*u := by ring
    rw [he] at h
    rw [min_eq_left (by linarith)]
    exact h
  · have h := Real.le_sin_mul (x := 2*(1-u)) (by linarith) (by linarith)
    have he : Real.pi/2*(2*(1-u))=Real.pi-Real.pi*u := by ring
    rw [he, Real.sin_pi_sub] at h
    rw [min_eq_right (by linarith)]
    exact h

lemma lemma32_complex_unit_chord_lower {u : ℝ} (hu0 : 0≤u) (hu1 : u≤1) :
    4*min u (1-u) ≤ ‖Complex.exp (Complex.I*((2*Real.pi*u : ℝ) : ℂ))-1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : (2*Real.pi*u)/2=Real.pi*u := by ring
  rw [he, Real.norm_eq_abs]
  have hs := lemma32_sine_unit_interval_lower hu0 hu1
  have ha := le_abs_self (2*Real.sin (Real.pi*u))
  linarith

lemma lemma32_std_character_chord_lower {D : ℕ} [NeZero D] (k : ZMod D) :
    4*min ((k.val : ℝ)/(D : ℝ)) (1-(k.val : ℝ)/(D : ℝ)) ≤
      ‖ZMod.stdAddChar k-1‖ := by
  have hD : (0 : ℝ)<(D : ℝ) := Nat.cast_pos.mpr (NeZero.pos D)
  have hk0 : (0 : ℝ)≤(k.val : ℝ)/(D : ℝ) := div_nonneg (Nat.cast_nonneg _) hD.le
  have hk1 : (k.val : ℝ)/(D : ℝ)≤1 :=
    (div_le_one hD).mpr (Nat.cast_le.mpr (ZMod.val_lt k).le)
  have he : ZMod.stdAddChar k =
      Complex.exp (Complex.I*((2*Real.pi*((k.val : ℝ)/(D : ℝ)) : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [he]
  exact lemma32_complex_unit_chord_lower hk0 hk1

end ZhangLS.Spec
