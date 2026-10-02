import ZhangLS.Spec.AllModuliLargeSieve

/-! # Finite weighted Cauchy for the genuine primitive conductor family -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_weighted_cauchy {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (hw : ∀i, 0≤w i) (f g : ι → ℂ) :
    (∑ i∈S, w i*‖f i‖*‖g i‖)^2≤
      (∑ i∈S, w i*‖f i‖^2)*(∑ i∈S, w i*‖g i‖^2) := by
  have hprod (i : ι) : (Real.sqrt (w i)*‖f i‖)*(Real.sqrt (w i)*‖g i‖)=
      w i*‖f i‖*‖g i‖ := by
    calc
      _=(Real.sqrt (w i))^2*(‖f i‖*‖g i‖) := by ring
      _=_ := by rw [Real.sq_sqrt (hw i)]; ring
  have hsqf (i : ι) : (Real.sqrt (w i)*‖f i‖)^2=w i*‖f i‖^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hsqg (i : ι) : (Real.sqrt (w i)*‖g i‖)^2=w i*‖g i‖^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hh := sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)*‖f i‖)
    (fun i => Real.sqrt (w i)*‖g i‖)
  simpa only [hprod,hsqf,hsqg] using hh

/-- Exact weighted Cauchy on every primitive character at each listed modulus.
No primality or coprimality restriction on the moduli is introduced. -/
theorem proposition71_weighted_primitive_cauchy (Q : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀r, 0≤w r)
    (F G : (r : ℕ) → DirichletCharacter ℂ r → ℂ) :
    (∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
      ‖F r θ‖*‖G r θ‖)^2≤
    (∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F r θ‖^2)*
    (∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖G r θ‖^2) := by
  let U : Finset (Σr : ℕ, DirichletCharacter ℂ r) :=
    Q.sigma (fun r => (univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive))
  have hh := proposition71_weighted_cauchy U (fun i => w i.1) (fun i => hw i.1)
    (fun i => F i.1 i.2) (fun i => G i.1 i.2)
  simpa only [U,sum_sigma,mul_sum,mul_assoc] using hh

/-- Consequence of the finite algebraic Cauchy inequality. The two separate
moment bounds must be supplied and are proved for the actual polynomials elsewhere. -/
theorem proposition71_weighted_primitive_cauchy_bound (Q : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀r, 0≤w r)
    (F G : (r : ℕ) → DirichletCharacter ℂ r → ℂ)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hF : (∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
      ‖F r θ‖^2)≤A)
    (hG : (∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
      ‖G r θ‖^2)≤B) :
    (∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
      ‖F r θ‖*‖G r θ‖)≤Real.sqrt A*Real.sqrt B := by
  have hF0 : 0≤∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F r θ‖^2 :=
    sum_nonneg (fun r _ => mul_nonneg (hw r) (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hG0 : 0≤∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖G r θ‖^2 :=
    sum_nonneg (fun r _ => mul_nonneg (hw r) (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hleft : 0≤∑ r∈Q, w r*∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F r θ‖*‖G r θ‖ :=
    sum_nonneg (fun r _ => mul_nonneg (hw r) (sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))))
  apply (sq_le_sq₀ hleft (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB]
  exact (proposition71_weighted_primitive_cauchy Q w hw F G).trans (mul_le_mul hF hG hG0 hA)

end ZhangLS.Spec
