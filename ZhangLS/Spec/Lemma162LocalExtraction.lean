import ZhangLS.Spec.Lemma162ActualMLocal

/-! Exact rational finite-D extraction identities. Variables a=q^(-β₁),
b=q^βⱼ, u=1/q remain independent; no β is set to zero in the identities.
The formal u=0 identities record the first-order Euler extraction only.
Global convergence/Dirichlet bridges are separate and not claimed here. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def lemma162LocalLambda (a u v : ℂ) : ℂ := (1-a*v*u)/(1-v*u)
noncomputable def lemma162M01 (a u v x : ℂ) : ℂ :=
  (1-lemma162LocalLambda a u v*x)/((1-x)*(1-v*x))
noncomputable def lemma162M00 (a u v x : ℂ) : ℂ :=
  lemma162M01 a u v x-lemma162LocalLambda a u v*v*x/((1-u)*(1-v*x))
noncomputable def lemma162M10 (u v x : ℂ) : ℂ :=
  (1-v*x/(1-u))/(1-v*x)
noncomputable def lemma162M11 (v x : ℂ) : ℂ := (1-v*x)⁻¹

/-- Source's base local rational factor, before and after extraction. -/
lemma lemma162_m00_source_identity (a u v x : ℂ)
    (hu : 1-u ≠ 0) (hx : 1-x ≠ 0) (hvu : 1-v*u ≠ 0)
    (hvx : 1-v*x ≠ 0) (hax : 1-a*x ≠ 0) (hatu : 1-a*(v*u) ≠ 0) :
    (1-a*x)/((1-x)*(1-v*x))*lemma161XiRational a u v x =
      lemma162M00 a u v x := by
  unfold lemma161XiRational lemma162M00 lemma162M01 lemma162LocalLambda
  have hxv : 1-x*v ≠ 0 := by simpa [mul_comm] using hvx
  have hauv : 1-a*v*u ≠ 0 := by simpa [mul_assoc] using hatu
  repeat' field_simp [hu,hx,hvu,hvx,hax,hatu,hxv,hauv]
  all_goals ring

/-- The four exact local factors are 1 at ramified primes. -/
lemma lemma162_ramified_factors (a u x : ℂ) (hx : 1-x ≠ 0) :
    lemma162M00 a u 0 x = 1 ∧ lemma162M01 a u 0 x = 1 ∧
      lemma162M10 u 0 x = 1 ∧ lemma162M11 0 x = 1 := by
  simp [lemma162M00,lemma162M01,lemma162M10,lemma162M11,lemma162LocalLambda,hx]

noncomputable def lemma162FirstNumerator (a u v b : ℂ) : ℂ :=
  v*lemma162M01 a u v (u*b)+lemma162LocalLambda a u v*b*lemma162M10 u v (u*b)

noncomputable def lemma162FirstRemainder (a u v b : ℂ) : ℂ :=
  v*b*(a*u^2*b-a-v*u*b+v-u+1)/
    ((1-u)*(1-v*u)*(1-u*b)*(1-v*u*b))

/-- Exact finite-q remainder; its factor u=1/q is explicit. -/
lemma lemma162_exact_first_remainder (a u v b : ℂ) (hv : v = 1 ∨ v = -1)
    (hu : 1-u ≠ 0) (hvu : 1-v*u ≠ 0)
    (hub : 1-u*b ≠ 0) (hvub : 1-v*u*b ≠ 0) :
    lemma162FirstNumerator a u v b - (v+b)*lemma162M00 a u v (u*b) =
      u*lemma162FirstRemainder a u v b := by
  unfold lemma162FirstNumerator lemma162FirstRemainder lemma162M00
    lemma162M01 lemma162M10 lemma162LocalLambda
  rcases hv with rfl | rfl
  all_goals
    simp only [one_mul,sub_neg_eq_add,mul_neg,neg_mul] at *
    field_simp [hu,hvu,hub,hvub]
    ring

/-- Hadamard multiplication by (ν*χ)(q)=1+2χ(q), with exact remainder. -/
lemma lemma162_shifted_first_coefficient (a u v b : ℂ) (hv : v = 1 ∨ v = -1)
    (hu : 1-u ≠ 0) (hvu : 1-v*u ≠ 0)
    (hub : 1-u*b ≠ 0) (hvub : 1-v*u*b ≠ 0) :
    (1+2*v)*lemma162FirstNumerator a u v b -
      (2+v+b+2*v*b)*lemma162M00 a u v (u*b) =
        u*(1+2*v)*lemma162FirstRemainder a u v b := by
  have h := lemma162_exact_first_remainder a u v b hv hu hvu hub hvub
  rcases hv with rfl | rfl
  · linear_combination 3*h
  · linear_combination -h

/-- The residual first-order term of the unshifted extraction. This algebraic
identity does not itself prove non-continuation or a convergence failure. -/
lemma lemma162_unshifted_first_coefficient (a u v b : ℂ) (hv : v = 1 ∨ v = -1)
    (hu : 1-u ≠ 0) (hvu : 1-v*u ≠ 0)
    (hub : 1-u*b ≠ 0) (hvub : 1-v*u*b ≠ 0) :
    (1+2*v)*lemma162FirstNumerator a u v b -
      (3+3*v)*lemma162M00 a u v (u*b) =
        (b-1)*(1+2*v)*lemma162M00 a u v (u*b) +
          u*(1+2*v)*lemma162FirstRemainder a u v b := by
  have h := lemma162_shifted_first_coefficient a u v b hv hu hvu hub hvub
  linear_combination h

/-- The local reciprocal of the forced global product
ζ(s)^2 ζ(s−γ) L(s) L(s−γ)^2. -/
noncomputable def lemma162ShiftedRemoval (v b z : ℂ) : ℂ :=
  (1-z)^2*(1-b*z)*(1-v*z)*(1-v*b*z)^2

lemma lemma162_shifted_removal_linear (v b : ℂ) :
    deriv (lemma162ShiftedRemoval v b) 0 = -(2+v+b+2*v*b) := by
  have h1 : HasDerivAt (fun z : ℂ => 1-z) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℂ)).const_sub 1
  have hb : HasDerivAt (fun z : ℂ => 1-b*z) (-b) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_mul b).const_sub 1
  have hv : HasDerivAt (fun z : ℂ => 1-v*z) (-v) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_mul v).const_sub 1
  have hvb : HasDerivAt (fun z : ℂ => 1-(v*b)*z) (-(v*b)) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_mul (v*b)).const_sub 1
  have hd : HasDerivAt (lemma162ShiftedRemoval v b) (-(2+v+b+2*v*b)) 0 := by
    convert (((h1.pow 2).mul hb).mul hv).mul (hvb.pow 2) using 1
    simp
    ring
  exact hd.deriv

/-- At q=2, χ(2)=1, the actual normalizing constant is 2; the base local
factor is retained, rather than divided out. -/
lemma lemma162_special_two_center : lemma162M00 1 (1/2) 1 (1/2) / 2 = 0 := by
  norm_num [lemma162M00,lemma162M01,lemma162LocalLambda]

/-- Zero-shift comparison only, never the definition of actual varpi. -/
lemma lemma162_zero_shift_centers (u : ℂ) (hu : 1-u ≠ 0) (hup : 1+u ≠ 0) :
    lemma162M00 1 u 1 u = (1-2*u)/(1-u)^2 ∧
      lemma162M00 1 u (-1) u = 1/(1-u^2) := by
  unfold lemma162M00 lemma162M01 lemma162LocalLambda
  constructor
  · field_simp [hu]; ring
  · have hu2 : 1-u^2 ≠ 0 := by
      rw [show 1-u^2 = (1-u)*(1+u) by ring]
      exact mul_ne_zero hu hup
    field_simp [hu,hup,hu2]
    ring

/-- The exponents (2,1,1,2) are uniquely forced among products generated by
ζ(s), ζ(s−γ), L(s), L(s−γ), by formal first-order matching. -/
lemma lemma162_extraction_exponents_unique (A B C E : ℂ)
    (h : ∀ v b : ℂ, (v = 1 ∨ v = -1) →
      A+B*b+C*v+E*v*b = 2+v+b+2*v*b) :
    A = 2 ∧ B = 1 ∧ C = 1 ∧ E = 2 := by
  have hp0 := h 1 0 (Or.inl rfl)
  have hm0 := h (-1) 0 (Or.inr rfl)
  have hp1 := h 1 1 (Or.inl rfl)
  have hm1 := h (-1) 1 (Or.inr rfl)
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (hp0+hm0)/2
  · linear_combination (hp1+hm1-hp0-hm0)/2
  · linear_combination (hp0-hm0)/2
  · linear_combination (hp1-hm1-hp0+hm0)/2

end ZhangLS.Spec
