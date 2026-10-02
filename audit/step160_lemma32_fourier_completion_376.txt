import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace ZhangLS.Spec

noncomputable def lemma32BurgessPower (D : ℕ) (r : ℝ) : ℝ := Real.exp (r*Real.log (D : ℝ))

lemma lemma32_burgess_power_pos (D : ℕ) (r : ℝ) : 0<lemma32BurgessPower D r := Real.exp_pos _

lemma lemma32_burgess_power_one_le {D : ℕ} (hD : 1≤D) {r : ℝ} (hr : 0≤r) :
    1≤lemma32BurgessPower D r := by
  unfold lemma32BurgessPower
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonneg hr (Real.log_nonneg (Nat.one_le_cast.mpr hD)))

lemma lemma32_burgess_power_add (D : ℕ) (r s : ℝ) :
    lemma32BurgessPower D (r+s)=lemma32BurgessPower D r*lemma32BurgessPower D s := by
  unfold lemma32BurgessPower
  rw [add_mul, Real.exp_add]

lemma lemma32_burgess_power_nat_pow (D n : ℕ) (r : ℝ) :
    (lemma32BurgessPower D r)^n=lemma32BurgessPower D ((n : ℝ)*r) := by
  unfold lemma32BurgessPower
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma lemma32_burgess_power_mono {D : ℕ} (hD : 1≤D) {r s : ℝ} (hrs : r≤s) :
    lemma32BurgessPower D r≤lemma32BurgessPower D s := by
  unfold lemma32BurgessPower
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrs
    (Real.log_nonneg (Nat.one_le_cast.mpr hD)))

lemma lemma32_burgess_power_one {D : ℕ} (hD : 0<D) :
    lemma32BurgessPower D 1=(D : ℝ) := by
  simp only [lemma32BurgessPower, one_mul, Real.exp_log (Nat.cast_pos.mpr hD)]

lemma lemma32_burgess_power_sqrt {D : ℕ} (hD : 0<D) :
    Real.sqrt (D : ℝ)=lemma32BurgessPower D (1/2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Nat.cast_pos.mpr hD)]
  unfold lemma32BurgessPower
  congr 1
  ring

lemma lemma32_burgess_log_power_bound (D : ℕ) :
    1+Real.log (D : ℝ)≤512*lemma32BurgessPower D (1/512) := by
  have h := Real.add_one_le_exp (Real.log (D : ℝ)/512)
  have he : Real.log (D : ℝ)/512=(1/512)*Real.log (D : ℝ) := by ring
  rw [he] at h
  unfold lemma32BurgessPower
  linarith

end ZhangLS.Spec
