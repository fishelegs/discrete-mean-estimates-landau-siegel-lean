import ZhangLS.Spec.Lemma151Definitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace ZhangLS.Spec
open Complex MeasureTheory

/-- Elementary integration by parts determining the sign of the short tail. -/
theorem lemma151_short_exponential_integral (k : ℂ) (h : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..h, (Complex.exp (k*t)-Complex.exp (k*h))) =
      -k * ∫ t : ℝ in (0 : ℝ)..h, (t : ℂ)*Complex.exp (k*t) := by
  have hu : Continuous (fun t : ℝ => (t : ℂ)) := by fun_prop
  have hv : Continuous (fun t : ℝ => Complex.exp (k*t)) := by fun_prop
  have hu' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    intro t
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
  have hv' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (k*t))
      (Complex.exp (k*t)*k) t := by
    intro t
    simpa using ((hu' t).const_mul k).cexp
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := h) hu.continuousOn hv.continuousOn
    (fun t _ => hu' t) (fun t _ => hv' t)
    (continuous_const.intervalIntegrable 0 h)
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (k*t)*k)).intervalIntegrable 0 h)
  have hh : (∫ t : ℝ in (0 : ℝ)..h, (t : ℂ)*(Complex.exp (k*t)*k)) =
      (∫ t : ℝ in (0 : ℝ)..h, (t : ℂ)*Complex.exp (k*t))*k := by
    simp_rw [← mul_assoc]
    exact intervalIntegral.integral_mul_const k _
  rw [hh] at hip
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, one_mul] at hip
  rw [intervalIntegral.integral_sub (hv.intervalIntegrable 0 h)
    (continuous_const.intervalIntegrable 0 h), intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  linear_combination hip

noncomputable def lemma151BStar : ℂ :=
  (1/0.504 : ℂ) * ∫ t : ℝ in (0 : ℝ)..0.004,
    (t : ℂ)*Complex.exp (((3/2 : ℝ)*t*Real.pi : ℝ)*I)

/-- Exact formal change of variable and integration by parts for Appendix B's
terminal coefficient. This is a model-integral identity, not the arithmetic asymptotic. -/
theorem lemma151_residue_tail_eq_neg_pi_I_bstar (j : ℕ) :
    lemma151ResidueTail j = -I * Real.pi * j * lemma151BStar := by
  let k : ℂ := (3/2 : ℂ)*Real.pi*I
  have ht : (∫ z : ℝ in (0.5 : ℝ)..0.504,
      (Complex.exp (((3/2 : ℝ)*(0.504-z)*Real.pi : ℝ)*I) -
        Complex.exp ((0.006*Real.pi : ℝ)*I))) =
      ∫ t : ℝ in (0 : ℝ)..0.004, (Complex.exp (k*t)-Complex.exp (k*0.004)) := by
    have hs := intervalIntegral.integral_comp_sub_left
      (a := (0.5 : ℝ)) (b := (0.504 : ℝ))
      (fun t : ℝ => Complex.exp (k*t)-Complex.exp (k*0.004)) (0.504 : ℝ)
    norm_num at hs ⊢
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro x hx
    apply congrArg₂ (fun a b : ℂ => Complex.exp a - Complex.exp b)
    · dsimp only [k]
      ring
    · dsimp only [k]
      ring
  have hb : lemma151BStar = (1/0.504 : ℂ) *
      ∫ t : ℝ in (0 : ℝ)..0.004, (t : ℂ)*Complex.exp (k*t) := by
    unfold lemma151BStar
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    apply congrArg (fun a : ℂ => (x : ℂ)*Complex.exp a)
    dsimp only [k]
    push_cast
    ring
  have hi := lemma151_short_exponential_integral k (0.004 : ℝ)
  rw [lemma151ResidueTail, ht]
  norm_num at hi hb ⊢
  rw [hi, hb]
  dsimp [k]
  ring

end ZhangLS.Spec
