import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact composite-modulus totient weight for conductor averages

No coprimality of h,r is assumed. The true φ(hr) is compared through
supermultiplicativity with φ(h)φ(r); the r/φ(r) sieve weight is preserved.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec

lemma conductorTotientWeight_three_halves {r:ℝ} (hr:0≤r) :
    r^(3/2:ℝ)=r*Real.sqrt r := by
  by_cases hz:r=0
  · subst r; norm_num
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (lt_of_le_of_ne hr (Ne.symm hz)),
    Real.rpow_one,←Real.sqrt_eq_rpow]

theorem conductorTotientWeight_bound {d h r:ℕ} {R:ℝ}
    (hd:0<d) (hh:0<h) (hr:0<r) (hR:0<R) (hRr:R≤(r:ℝ)) :
    ((d:ℝ)*(h:ℝ)*((h*r).totient:ℝ)*Real.sqrt (r:ℝ))⁻¹ ≤
      ((d:ℝ)*(h:ℝ)*(h.totient:ℝ))⁻¹*((r:ℝ)/(r.totient:ℝ))/R^(3/2:ℝ) := by
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  have hhR : 0<(h:ℝ) := by exact_mod_cast hh
  have hrR : 0<(r:ℝ) := by exact_mod_cast hr
  have hφh : 0<(h.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hh
  have hφr : 0<(r.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr
  have hφhr : 0<((h*r).totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hh hr)
  have hs : 0<Real.sqrt (r:ℝ) := Real.sqrt_pos.mpr hrR
  have hφ : (h.totient:ℝ)*(r.totient:ℝ)≤((h*r).totient:ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative h r
  calc
    _≤((d:ℝ)*(h:ℝ)*((h.totient:ℝ)*(r.totient:ℝ))*Real.sqrt (r:ℝ))⁻¹ := by
      apply inv_anti₀ (by positivity)
      gcongr
    _=((d:ℝ)*(h:ℝ)*(h.totient:ℝ))⁻¹*((r:ℝ)/(r.totient:ℝ))/(r:ℝ)^(3/2:ℝ) := by
      rw [conductorTotientWeight_three_halves hrR.le]
      field_simp
    _≤_ := by
      apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hR _)
      exact Real.rpow_le_rpow hR.le hRr (by norm_num)

end ZhangLS.Spec
