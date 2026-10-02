import ZhangLS.Spec.Lemma152KappaLocal
/-! Exact rational form of the actual Section 15 local generating series.
The cancellation is proved with every denominator nonzero. The expression
on the right is later used for holomorphic continuation; it has no x-vu pole.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma152TailRational (a b t x : ℂ) : ℂ :=
  (x*lemma152KappaRational a b x-t*lemma152KappaRational a b t)/(x-t)

noncomputable def lemma152XiRational (a b u v x : ℂ) : ℂ :=
  1 + ((1-a*(v*u))*(1-b*(v*u))/(1-v*u)) *
    (lemma152TailRational a b (v*u) x - lemma152KappaRational a b (v*u) -
      (v/(1-u))*x*lemma152KappaRational a b x)

noncomputable def lemma152LocalRemoval (a b v x : ℂ) : ℂ :=
  ((1-a*x)*(1-b*x))/((1-x)*(1-v*x))

/-- An exact correction whose denominators stay nonzero on Re s>0.
Here u=q⁻¹, v=χ(q), x=q⁻ˢ, a=q⁻ᵝ¹ and b=q⁻ᵝ². -/
noncomputable def lemma152LocalCorrection (a b u v x : ℂ) : ℂ :=
  1 + u*x*(v^2*(a+b-1)-v)/((1-u)*(1-v*x)) -
    v*u*x*(a-1)*(b-1)*(1-u*x)/((1-u)*(1-v*u)*(1-x)*(1-v*x))

lemma lemma152_local_correction_identity (a b u v x : ℂ)
    (hv : v = 0 ∨ v = 1 ∨ v = -1)
    (hxt : x-v*u ≠ 0) (hu : 1-u ≠ 0) (hx : 1-x ≠ 0)
    (hvu : 1-v*u ≠ 0) (hvx : 1-v*x ≠ 0)
    (hax : 1-a*x ≠ 0) (hbx : 1-b*x ≠ 0)
    (hau : 1-a*(v*u) ≠ 0) (hbu : 1-b*(v*u) ≠ 0) :
    lemma152LocalRemoval a b v x * lemma152XiRational a b u v x =
      lemma152LocalCorrection a b u v x := by
  unfold lemma152LocalRemoval lemma152XiRational lemma152TailRational
    lemma152KappaRational lemma152LocalCorrection
  rcases hv with rfl | rfl | rfl
  all_goals
    simp only [zero_mul,one_mul,neg_one_mul,mul_neg,sub_zero,sub_neg_eq_add,zero_pow,
      zero_div,mul_zero,add_zero,sub_self,zero_sub] at *
    repeat' field_simp [hxt,hu,hx,hvu,hvx,hax,hbx,hau,hbu,mul_comm]
    all_goals ring

/-- Ramified primes contribute exactly 1, including nonzero shifts. -/
@[simp] lemma lemma152_local_correction_ramified (a b u x : ℂ) :
    lemma152LocalCorrection a b u 0 x = 1 := by simp [lemma152LocalCorrection]

lemma lemma152_local_correction_zero_shifts (u v x : ℂ) :
    lemma152LocalCorrection 1 1 u v x =
      1 + u*x*(v^2-v)/((1-u)*(1-v*x)) := by simp [lemma152LocalCorrection]

/-- Exactly the unramified factor in the statement of Lemma 15.2. -/
lemma lemma152_local_correction_at_center (u v : ℂ)
    (hv : v = 1 ∨ v = -1) (hu : 1-u ≠ 0) (hup : 1+u ≠ 0) :
    lemma152LocalCorrection 1 1 u v u = (1-v*u^2)/(1-u^2) := by
  rw [lemma152_local_correction_zero_shifts]
  rcases hv with rfl | rfl
  all_goals
    have hsq : 1-u^2 ≠ 0 := by
      rw [show 1-u^2 = (1-u)*(1+u) by ring]
      exact mul_ne_zero hu hup
    simp only [one_pow,one_mul,neg_one_mul,sub_neg_eq_add]
    field_simp
    all_goals ring

/-- The shift perturbation has two small factors, u and x, at every prime. -/
lemma lemma152_local_correction_shift_difference (a b u v x : ℂ) :
    lemma152LocalCorrection a b u v x - lemma152LocalCorrection 1 1 u v x =
      u*x*v^2*((a-1)+(b-1))/((1-u)*(1-v*x)) -
        v*u*x*(a-1)*(b-1)*(1-u*x)/((1-u)*(1-v*u)*(1-x)*(1-v*x)) := by
  unfold lemma152LocalCorrection
  simp only [one_add_one_eq_two,one_mul,sub_self,mul_zero,zero_div,sub_zero]
  ring

/-- Exact displacement of the zero-shift factor away from s=1. -/
lemma lemma152_local_correction_variable_difference (u v x : ℂ)
    (hu : 1-u ≠ 0) (hvx : 1-v*x ≠ 0) (hvu : 1-v*u ≠ 0) :
    lemma152LocalCorrection 1 1 u v x - lemma152LocalCorrection 1 1 u v u =
      u*(v^2-v)*(x-u)/((1-u)*(1-v*x)*(1-v*u)) := by
  rw [lemma152_local_correction_zero_shifts,lemma152_local_correction_zero_shifts]
  have hxv : 1-x*v ≠ 0 := by simpa [mul_comm] using hvx
  have huv : 1-u*v ≠ 0 := by simpa [mul_comm] using hvu
  field_simp [hu,hvx,hvu,hxv,huv]
  all_goals ring

end ZhangLS.Spec
