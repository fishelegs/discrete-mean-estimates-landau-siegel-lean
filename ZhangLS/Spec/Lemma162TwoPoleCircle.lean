import Mathlib.Analysis.Complex.CauchyIntegral

/-! Exact two-pole Cauchy identity. The conclusion is an evaluated genuine
circle integral, not a definition of a proposed residue formula. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 1500000

theorem lemma162_two_pole_partial_fractions (H γ w : ℂ)
    (hγ : γ≠0) (hw : w≠0) (hwγ : w≠γ) :
    H/(w^3*(w-γ)) = γ⁻¹^3*(H/(w-γ)) - γ⁻¹^3*(H/w) -
      γ⁻¹^2*(H/w^2) - γ⁻¹*(H/w^3) := by
  have := sub_ne_zero.mpr hwγ
  field_simp
  ring

theorem lemma162_cauchy_pole_integrable (H : ℂ → ℂ) {c a : ℂ} {R : ℝ}
    (hR : 0<R) (hH : ContinuousOn H (sphere c R))
    (ha : a∉sphere c R) (n : ℕ) :
    CircleIntegrable (fun w => H w/(w-a)^n) c R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply hH.div (by fun_prop)
  intro w hw
  exact pow_ne_zero _ (sub_ne_zero.mpr (by intro h; subst w; exact ha hw))

theorem lemma162_cauchy_center (H : ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hR : 0<R) (hH : DifferentiableOn ℂ H (closedBall c R)) (n : ℕ) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w-c)^(n+1)) c R =
      iteratedDeriv n H c/n.factorial := by
  have hh := hH.circleIntegral_one_div_sub_center_pow_smul hR n
  have he : (fun w => (1/(w-c)^(n+1)) • H w) =
      (fun w => H w/(w-c)^(n+1)) := by
    ext w
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he] at hh
  rw [hh,smul_eq_mul]
  have hpi : (2*Real.pi*I : ℂ)≠0 := Complex.two_pi_I_ne_zero
  field_simp

theorem lemma162_cauchy_simple (H : ℂ → ℂ) {c a : ℂ} {R : ℝ}
    (hH : DifferentiableOn ℂ H (closedBall c R)) (ha : a∈ball c R) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w-a)) c R = H a := by
  have hh := (hH.diffContOnCl_ball subset_rfl).two_pi_i_inv_smul_circleIntegral_sub_inv_smul ha
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

/-- The exact sum of both residues, in a form preserving their cancellation. -/
noncomputable def lemma162ThirdDividedDifference (H : ℂ → ℂ) (γ : ℂ) : ℂ :=
  (H γ-H 0-γ*deriv H 0-(γ^2/2)*iteratedDeriv 2 H 0)/γ^3

/-- Two distinct poles inside one circle. This identity computes the integral
from Cauchy's theorem and the actual derivatives of H. -/
theorem lemma162_two_pole_circle_decomposition (H : ℂ → ℂ) {γ : ℂ} {R : ℝ}
    (hγ : γ≠0) (hR : 0<R) (hγs : γ∉sphere 0 R)
    (hH : DifferentiableOn ℂ H (closedBall 0 R)) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w^3*(w-γ))) 0 R =
      γ⁻¹^3*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w-γ)) 0 R) -
        γ⁻¹^3*H 0-γ⁻¹^2*deriv H 0-γ⁻¹*(iteratedDeriv 2 H 0/2) := by
  have h0 : (0 : ℂ)∉sphere 0 R := by
    simpa using ne_of_lt hR
  have hcont := hH.continuousOn.mono sphere_subset_closedBall
  have hg := lemma162_cauchy_pole_integrable H hR hcont hγs 1
  have h1 := lemma162_cauchy_pole_integrable H hR hcont h0 1
  have h2 := lemma162_cauchy_pole_integrable H hR hcont h0 2
  have h3 := lemma162_cauchy_pole_integrable H hR hcont h0 3
  simp only [sub_zero,pow_one] at hg h1 h2 h3
  have hid : circleIntegral (fun w => H w/(w^3*(w-γ))) 0 R =
      circleIntegral (fun w => γ⁻¹^3*(H w/(w-γ)) - γ⁻¹^3*(H w/w) -
        γ⁻¹^2*(H w/w^2) - γ⁻¹*(H w/w^3)) 0 R := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    apply lemma162_two_pole_partial_fractions _ _ _ hγ
    · intro h; subst w; exact h0 hw
    · intro h; subst w; exact hγs hw
  have hg' : CircleIntegrable (fun w => γ⁻¹^3*(H w/(w-γ))) 0 R := hg.const_mul _
  have h1' : CircleIntegrable (fun w => γ⁻¹^3*(H w/w)) 0 R := h1.const_mul _
  have h2' : CircleIntegrable (fun w => γ⁻¹^2*(H w/w^2)) 0 R := h2.const_mul _
  have h3' : CircleIntegrable (fun w => γ⁻¹*(H w/w^3)) 0 R := h3.const_mul _
  have ha : CircleIntegrable (fun w => γ⁻¹^3*(H w/(w-γ))-γ⁻¹^3*(H w/w)) 0 R := hg'.sub h1'
  have hb : CircleIntegrable (fun w => γ⁻¹^3*(H w/(w-γ))-γ⁻¹^3*(H w/w)-γ⁻¹^2*(H w/w^2)) 0 R := ha.sub h2'
  rw [hid,circleIntegral.integral_sub hb h3',circleIntegral.integral_sub ha h2',
    circleIntegral.integral_sub hg' h1']
  simp only [circleIntegral.integral_const_mul]
  have h1val := lemma162_cauchy_center H hR hH 0
  have h2val := lemma162_cauchy_center H hR hH 1
  have h3val := lemma162_cauchy_center H hR hH 2
  simp only [sub_zero,Nat.reduceAdd,pow_one,iteratedDeriv_zero,iteratedDeriv_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.factorial_two,Nat.cast_one,Nat.cast_ofNat,
    div_one] at h1val h2val h3val
  calc
    _ = γ⁻¹^3*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w-γ)) 0 R) -
        γ⁻¹^3*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/w) 0 R) -
        γ⁻¹^2*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/w^2) 0 R) -
        γ⁻¹*((2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/w^3) 0 R) := by ring
    _ = _ := by rw [h1val,h2val,h3val]

/-- The residue at zero, including both lower Taylor terms. -/
noncomputable def lemma162ZeroResidue (H : ℂ → ℂ) (γ : ℂ) : ℂ :=
  -iteratedDeriv 2 H 0/(2*γ)-deriv H 0/γ^2-H 0/γ^3

/-- The residue at the genuine shifted pole. -/
noncomputable def lemma162ShiftResidue (H : ℂ → ℂ) (γ : ℂ) : ℂ := H γ/γ^3

theorem lemma162_residue_sum (H : ℂ → ℂ) {γ : ℂ} (hγ : γ≠0) :
    lemma162ZeroResidue H γ+lemma162ShiftResidue H γ = lemma162ThirdDividedDifference H γ := by
  unfold lemma162ZeroResidue lemma162ShiftResidue lemma162ThirdDividedDifference
  field_simp
  ring

/-- Both distinct poles inside one circle, with no residue oracle. -/
theorem lemma162_two_pole_circle (H : ℂ → ℂ) {γ : ℂ} {R : ℝ}
    (hγ : γ≠0) (hγR : ‖γ‖<R) (hH : DifferentiableOn ℂ H (closedBall 0 R)) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w^3*(w-γ))) 0 R =
      lemma162ThirdDividedDifference H γ := by
  have hR : 0<R := (norm_nonneg _).trans_lt hγR
  rw [lemma162_two_pole_circle_decomposition H hγ hR
    (by simpa [mem_sphere] using ne_of_lt hγR) hH,
    lemma162_cauchy_simple H hH (by simpa using hγR)]
  unfold lemma162ThirdDividedDifference
  field_simp

/-- Every sufficiently small circle about zero has the asserted residue. -/
theorem lemma162_zero_residue_circle (H : ℂ → ℂ) {γ : ℂ} {r : ℝ}
    (hr : 0<r) (hrγ : r<‖γ‖) (hH : DifferentiableOn ℂ H (closedBall 0 r)) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w^3*(w-γ))) 0 r =
      lemma162ZeroResidue H γ := by
  have hγ : γ≠0 := by intro h; simp [h] at hrγ; linarith
  have hγs : γ∉sphere 0 r := by simpa [mem_sphere] using ne_of_gt hrγ
  have hG : DifferentiableOn ℂ (fun w => H w/(w-γ)) (closedBall 0 r) := by
    apply hH.div (by fun_prop)
    intro w hw
    apply sub_ne_zero.mpr
    intro h
    subst w
    have hh : ‖γ‖≤r := by simpa using hw
    linarith
  have hg := (hG.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hr.le
  rw [lemma162_two_pole_circle_decomposition H hγ hr hγs hH,hg]
  unfold lemma162ZeroResidue
  field_simp
  ring

/-- Every sufficiently small circle about gamma has the asserted residue. -/
theorem lemma162_shift_residue_circle (H : ℂ → ℂ) {γ : ℂ} {r : ℝ}
    (hr : 0<r) (hrγ : r<‖γ‖) (hH : DifferentiableOn ℂ H (closedBall γ r)) :
    (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun w => H w/(w^3*(w-γ))) γ r =
      lemma162ShiftResidue H γ := by
  have hG : DifferentiableOn ℂ (fun w => H w/w^3) (closedBall γ r) := by
    apply hH.div (by fun_prop)
    intro w hw
    apply pow_ne_zero
    intro h
    subst w
    have hh : ‖γ‖≤r := by simpa [mem_closedBall,dist_eq_norm] using hw
    linarith
  have hh := lemma162_cauchy_simple (fun w => H w/w^3) (c := γ) (a := γ) hG (by simpa using hr)
  simpa only [div_div,lemma162ShiftResidue] using hh

end ZhangLS.Spec
