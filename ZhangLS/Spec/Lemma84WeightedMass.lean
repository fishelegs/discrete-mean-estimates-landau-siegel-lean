import ZhangLS.Spec.Lemma84WeightedArithmetic

/-! Explicit harmonic mass bound for the actual μ,χ,λ₀ⱼ,φ weights.
There is no hypothesis bounding these weights: the whole arithmetic bound
is proved from their definitions, uniformly in the modulus and the shifts. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- The outer coefficient in the Section 8 display preceding Lemma 8.2. -/
noncomputable def lemma84Section8Weight {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) : ℂ :=
  (((|ArithmeticFunction.moebius r| : ℝ)*‖χ.evalNat (d*r)‖ /
      ((d:ℝ)*(r:ℝ)*(Nat.totient r:ℝ)) : ℝ) : ℂ) *
    lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)

/-- A fixed absolute arithmetic scale. Its exponent is deliberately generous. -/
noncomputable def lemma84WeightScale (y : ℝ) : ℝ :=
  Real.exp (12/Real.log 2)*Real.exp (2/Real.log 2)*(1+Real.log y)^42

lemma lemma84_weight_scale_nonneg (y : ℝ) : 0≤lemma84WeightScale y := by
  unfold lemma84WeightScale
  positivity

/-- Pointwise bound for the actual arithmetic coefficient, including the
convergent extra r⁻¹ supplied by the true totient denominator. -/
theorem lemma84_actual_weight_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) {d r : ℕ} (hd : 0<d) (hr : 0<r)
    {y : ℝ} (hy : 1<y) (hprod : Real.log (d*r:ℕ)≤y) :
    ‖lemma84Section8Weight χ c j d r‖≤
      lemma84WeightScale y*(d:ℝ)⁻¹*(r:ℝ)⁻¹^2 := by
  have hdr : 0<d*r := Nat.mul_pos hd hr
  have hrdr : (r:ℝ)≤(d*r:ℕ) := by exact_mod_cast Nat.le_mul_of_pos_left r hd
  have hrlog : Real.log r≤y := (Real.log_le_log (by positivity) hrdr).trans hprod
  have hlam := lemma84_lambda_uniform_weight (lemma83PaperBeta D c)
    (lemma83_beta_re D c) j hdr hy hprod
  have hphi := lemma84_reciprocal_totient_uniform hr hy hrlog
  have hmu : (|ArithmeticFunction.moebius r|:ℝ)≤1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=r))
  have hmu0 : 0≤(|ArithmeticFunction.moebius r|:ℝ) := by exact_mod_cast abs_nonneg (ArithmeticFunction.moebius r)
  have hs0 : 0≤(|ArithmeticFunction.moebius r|:ℝ)*‖χ.evalNat (d*r)‖/
      ((d:ℝ)*(r:ℝ)*(Nat.totient r:ℝ)) := by positivity
  rw [lemma84Section8Weight,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs0]
  have hs : (|ArithmeticFunction.moebius r|:ℝ)*‖χ.evalNat (d*r)‖ /
      ((d:ℝ)*(r:ℝ)*(Nat.totient r:ℝ))≤
      (d:ℝ)⁻¹*(r:ℝ)⁻¹*((r:ℝ)⁻¹*(Real.exp (2/Real.log 2)*(1+Real.log y)^6)) := by
    calc
      _ ≤ 1/((d:ℝ)*(r:ℝ)*(Nat.totient r:ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [χ.evalNat_norm_le_one (d*r),norm_nonneg (χ.evalNat (d*r))]
      _ = (d:ℝ)⁻¹*(r:ℝ)⁻¹*(Nat.totient r:ℝ)⁻¹ := by simp [mul_inv_rev]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hphi (by positivity)
  calc
    _ ≤ ((d:ℝ)⁻¹*(r:ℝ)⁻¹*((r:ℝ)⁻¹*(Real.exp (2/Real.log 2)*(1+Real.log y)^6)))*
      (Real.exp (12/Real.log 2)*(1+Real.log y)^36) :=
        mul_le_mul hs hlam (norm_nonneg _) (by positivity)
    _ = _ := by unfold lemma84WeightScale; ring

lemma lemma84_finite_reciprocal_square (S : Finset ℕ) :
    ∑ r∈S, (r:ℝ)⁻¹^2≤2 := by
  have hs : Summable (fun r : ℕ => (r:ℝ)^(-(1+1:ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ = ∑ r∈S, (r:ℝ)^(-(1+1:ℝ)) := by
      apply sum_congr rfl
      intro r hr
      rw [show -(1+1:ℝ)=(-2:ℝ) by norm_num,Real.rpow_neg (by positivity),Real.rpow_two,inv_pow]
    _ ≤ ∑' r : ℕ, (r:ℝ)^(-(1+1:ℝ)) := hs.sum_le_tsum S (fun _ _ => by positivity)
    _ ≤ 2 := by convert lemma83_rpow_tsum_le 1 (by norm_num) using 1 <;> norm_num

/-- Actual finite weighted harmonic bound. The subset is any genuine support
or boundary layer contained in the positive cutoff box; no λ/μ/φ estimate is
an assumption. The constant is absolute and independent of D. -/
theorem lemma84_actual_weight_mass {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (S : Finset (ℕ×ℕ)) (N : ℕ)
    (hS : S⊆(Icc 1 N)×ˢ(Icc 1 N)) {y : ℝ} (hy : 1<y)
    (hlog : ∀a∈S, Real.log (a.1*a.2:ℕ)≤y) :
    (∑ a∈S, ‖lemma84Section8Weight χ c j a.1 a.2‖)≤
      2*lemma84WeightScale y*(harmonic N:ℝ) := by
  have hH : 0≤(harmonic N:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ∑ a∈S, lemma84WeightScale y*(a.1:ℝ)⁻¹*(a.2:ℝ)⁻¹^2 := by
      apply sum_le_sum
      intro a ha
      have hm := mem_product.mp (hS ha)
      exact lemma84_actual_weight_bound χ c j (mem_Icc.mp hm.1).1
        (mem_Icc.mp hm.2).1 hy (hlog a ha)
    _ ≤ ∑ a∈(Icc 1 N)×ˢ(Icc 1 N), lemma84WeightScale y*(a.1:ℝ)⁻¹*(a.2:ℝ)⁻¹^2 :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by
        have := lemma84_weight_scale_nonneg y
        positivity)
    _ = lemma84WeightScale y*(harmonic N:ℝ)*(∑ r∈Icc 1 N, (r:ℝ)⁻¹^2) := by
      rw [sum_product]
      simp only [←mul_sum,←sum_mul,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ lemma84WeightScale y*(harmonic N:ℝ)*2 :=
      mul_le_mul_of_nonneg_left (lemma84_finite_reciprocal_square _) (mul_nonneg (lemma84_weight_scale_nonneg y) hH)
    _ = _ := by ring

end ZhangLS.Spec
