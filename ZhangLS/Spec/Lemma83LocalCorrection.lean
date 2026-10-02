import ZhangLS.Spec.Lemma83Definitions
/-!
# Exact rational local corrections for Lemma 8.3

Here a=q^(-βⱼ), b=q^(-βⱼ₊₁), c=q^(-βⱼ₊₂), u=1/q,
t=q^(-(1-βⱼ)), x=χ(q)q^(-s), and a*t=u. These algebraic identities
are separated from the (subsequent) convergence and Section 7 coefficient bridges.
No denominator is discarded, including the shifted exceptional-prime denominator.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma83KappaRational (a b c x : ℂ) : ℂ :=
  (1-x)/((1-a*x)*(1-b*x)*(1-c*x))

/-- Evaluated generating series for κ̃(qʳ;1,1-βⱼ), prior to cancellation. -/
noncomputable def lemma83TailRational (a b c t x : ℂ) : ℂ :=
  (x*lemma83KappaRational a b c x-t*lemma83KappaRational a b c t)/(x-t)

noncomputable def lemma83RegularXiRational (a b c t u x : ℂ) : ℂ :=
  1 + (lemma83KappaRational a b c t)⁻¹ *
    (lemma83TailRational a b c t x - lemma83KappaRational a b c t -
      (a/(1-u))*x*lemma83KappaRational a b c x)

noncomputable def lemma83LocalRemoval (b c x : ℂ) : ℂ :=
  (1-b*x)*(1-c*x)/(1-x)

/-- The exact correction at a prime outside dr. -/
noncomputable def lemma83RegularCorrection (b c t x : ℂ) : ℂ :=
  1 - t*x*(1-b)*(1-c)/((1-t)*(1-x))

/-- The exact correction at a prime dividing r. -/
noncomputable def lemma83RCorrection (a x : ℂ) : ℂ := (1-a*x)⁻¹

/-- The exact correction at a prime dividing d but not r. -/
noncomputable def lemma83DCorrection (a u x : ℂ) : ℂ :=
  (1-a*x/(1-u))/(1-a*x)

lemma lemma83_regular_correction_identity (a b c t u x : ℂ)
    (hat : a*t = u) (hxt : x-t ≠ 0) (ht : 1-t ≠ 0) (hx : 1-x ≠ 0)
    (hu : 1-u ≠ 0) (hax : 1-a*x ≠ 0) (hbx : 1-b*x ≠ 0)
    (hcx : 1-c*x ≠ 0) (hbt : 1-b*t ≠ 0) (hct : 1-c*t ≠ 0) :
    lemma83LocalRemoval b c x * lemma83RegularXiRational a b c t u x =
      lemma83RegularCorrection b c t x := by
  have hat' : 1-a*t ≠ 0 := by rwa [hat]
  unfold lemma83LocalRemoval lemma83RegularXiRational lemma83TailRational
    lemma83KappaRational lemma83RegularCorrection
  repeat' field_simp [hxt,ht,hx,hu,hax,hbx,hcx,hbt,hct,hat',mul_comm]
  rw [← hat]
  all_goals ring

lemma lemma83_r_correction_identity (a b c x : ℂ)
    (hx : 1-x ≠ 0) (hax : 1-a*x ≠ 0) (hbx : 1-b*x ≠ 0) (hcx : 1-c*x ≠ 0) :
    lemma83LocalRemoval b c x * lemma83KappaRational a b c x =
      lemma83RCorrection a x := by
  unfold lemma83LocalRemoval lemma83KappaRational lemma83RCorrection
  repeat' field_simp [hx,hax,hbx,hcx,mul_comm]

lemma lemma83_d_correction_identity (a b c u x : ℂ) (hu : 1-u ≠ 0)
    (hx : 1-x ≠ 0) (hax : 1-a*x ≠ 0) (hbx : 1-b*x ≠ 0) (hcx : 1-c*x ≠ 0) :
    lemma83LocalRemoval b c x *
      (lemma83KappaRational a b c x - (a/(1-u))*x*lemma83KappaRational a b c x) =
      lemma83DCorrection a u x := by
  unfold lemma83LocalRemoval lemma83KappaRational lemma83DCorrection
  repeat' field_simp [hu,hx,hax,hbx,hcx,mul_comm]
  all_goals ring

@[simp] lemma lemma83_regular_correction_ramified (b c t : ℂ) :
    lemma83RegularCorrection b c t 0 = 1 := by simp [lemma83RegularCorrection]

@[simp] lemma lemma83_r_correction_ramified (a : ℂ) :
    lemma83RCorrection a 0 = 1 := by simp [lemma83RCorrection]

@[simp] lemma lemma83_d_correction_ramified (a u : ℂ) :
    lemma83DCorrection a u 0 = 1 := by simp [lemma83DCorrection]

@[simp] lemma lemma83_regular_correction_zero_shift (t x : ℂ) :
    lemma83RegularCorrection 1 1 t x = 1 := by simp [lemma83RegularCorrection]

lemma lemma83_r_correction_zero_shift (u v : ℂ) :
    lemma83RCorrection 1 (v*u) = (1-v*u)⁻¹ := by simp [lemma83RCorrection]

lemma lemma83_d_correction_zero_shift (u v : ℂ) (hu : 1-u ≠ 0) :
    lemma83DCorrection 1 u (v*u) = (1-u-v*u)/((1-v*u)*(1-u)) := by
  unfold lemma83DCorrection
  simp only [one_mul]
  field_simp
  all_goals ring

/-- This exceptional factor vanishes: additive errors cannot be converted to relative errors. -/
lemma lemma83_d_correction_two_zero : lemma83DCorrection 1 (1/2) (1/2) = 0 := by
  norm_num [lemma83DCorrection]

end ZhangLS.Spec
