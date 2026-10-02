import ZhangLS.Spec.Lemma161NormalizedProduct

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma161_zero_center_factor {D : ℕ} (χ : RealPrimitiveCharacter D) (q : Nat.Primes) :
    lemma161PrimeFactor χ 0 q 1 = lemma161MainFactor χ q := by
  have hu : ‖(q.val:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hvu : ‖χ.evalNat q.val*(q.val:ℂ)⁻¹‖ < 1 :=
    lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hu
  have hun := lemma83_one_sub_ne_zero hu
  have hvun := lemma83_one_sub_ne_zero hvu
  have hq : (q.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.property.ne_zero
  have hqm : (q.val:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast q.property.ne_one)
  have hqv : (q.val:ℂ)-χ.evalNat q.val ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hh := χ.evalNat_norm_le_one q.val
    rw [← he,Complex.norm_natCast] at hh
    have hq1 : (1:ℝ) < q.val := by exact_mod_cast q.property.one_lt
    linarith
  unfold lemma161PrimeFactor
  rw [lemma83_prime_monomial_one q.property.pos]
  simp only [lemma32PrimeMonomial,mul_zero,zero_mul,neg_zero,Complex.exp_zero]
  rw [lemma161_local_zero_shift]
  unfold lemma161MainFactor
  rw [Nat.cast_sub q.property.one_le,Nat.cast_one]
  simp only [div_eq_mul_inv]
  repeat' field_simp [hun,hvun,hq,hqm,hqv]
  all_goals ring

lemma lemma161_zero_center_equals_main {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma161Star χ 0 1 = lemma161MainTerm χ := by
  unfold lemma161Star lemma161MainTerm
  split_ifs
  · rw [lemma161_restricted_product_eq_subtype]
    congr 1
    exact tprod_congr (fun q => lemma161_zero_center_factor χ q.val)
  · unfold lemma161EulerProduct
    exact tprod_congr (lemma161_zero_center_factor χ)

lemma lemma161_main_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Multipliable (lemma161MainFactor χ) := by
  exact (lemma161_euler_product_multipliable χ 0 rfl 1 (by norm_num)).congr
    (lemma161_zero_center_factor χ)

lemma lemma161_main_restricted_multipliable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (P : Nat.Primes → Prop) :
    Multipliable (fun q : {q : Nat.Primes // P q} => lemma161MainFactor χ q.val) := by
  have hs : Summable (fun q : Nat.Primes => ‖lemma161MainFactor χ q-1‖) :=
    lemma152_majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by rw [← lemma161_zero_center_factor]; exact lemma161_prime_error_uniform χ 0 rfl q 1 (by norm_num))
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable (hs.subtype P)

/-- Every retained central factor is bounded below uniformly. The only zero
factor is exactly χ(2)=1 at q=2, and that factor is not retained. -/
lemma lemma161_main_factor_norm_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (hq : q.val = 2 → χ.evalNat 2 ≠ 1) :
    3/4 ≤ ‖lemma161MainFactor χ q‖ := by
  rw [← lemma161_zero_center_factor]
  unfold lemma161PrimeFactor
  rw [lemma83_prime_monomial_one q.property.pos]
  simp only [lemma32PrimeMonomial,mul_zero,zero_mul,neg_zero,Complex.exp_zero]
  rw [lemma161_local_zero_shift]
  let u : ℝ := (q.val:ℝ)⁻¹
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu2 : u ≤ 1/2 := by
    dsimp [u]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hcast : (q.val:ℂ)⁻¹ = (u:ℂ) := by simp [u]
  rw [hcast]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (q.val:ZMod D) with hv | hv | hv
  · change χ.evalNat q.val = 0 at hv
    rw [hv]
    norm_num
  · change χ.evalNat q.val = 1 at hv
    have hq3 : 3 ≤ q.val := by
      have hh := q.property.two_le
      by_contra hn
      have hq2 : q.val = 2 := by omega
      exact hq hq2 (by simpa [hq2] using hv)
    have hu3 : u ≤ 1/3 := by
      dsimp [u]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3)
        (show (3:ℝ) ≤ q.val by exact_mod_cast hq3)
    have hd : 0 < (1-u)*(1-u) := mul_pos (by linarith) (by linarith)
    have hle : (3/4:ℝ) ≤ 1-u*u/((1-u)*(1-u)) := by
      have hh : u*u/((1-u)*(1-u)) ≤ 1/4 := (div_le_iff₀ hd).mpr (by nlinarith)
      linarith
    rw [hv]
    have he : (1:ℂ)-1*(u:ℂ)*(u:ℂ)/((1-(u:ℂ))*(1-1*(u:ℂ))) =
        ((1-u*u/((1-u)*(1-u)):ℝ):ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact hle
  · change χ.evalNat q.val = -1 at hv
    have hd : 0 < (1-u)*(1+u) := mul_pos (by linarith) (by linarith)
    have hle : (3/4:ℝ) ≤ 1+u*u/((1-u)*(1+u)) := by
      have hh : 0 ≤ u*u/((1-u)*(1+u)) := div_nonneg (mul_nonneg hu0 hu0) hd.le
      linarith
    rw [hv]
    have he : (1:ℂ)-(-1)*(u:ℂ)*(u:ℂ)/((1-(u:ℂ))*(1-(-1)*(u:ℂ))) =
        ((1+u*u/((1-u)*(1+u)):ℝ):ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact hle

end ZhangLS.Spec
