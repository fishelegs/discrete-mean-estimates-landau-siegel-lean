import ZhangLS.Spec.Lemma83RegularProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Set
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma83ExceptionalPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (r q : ℕ) (s : ℂ) : ℂ :=
  if q ∣ r then
    lemma83RCorrection (lemma32PrimeMonomial q β) (χ.evalNat q * lemma32PrimeMonomial q s)
  else
    lemma83DCorrection (lemma32PrimeMonomial q β) ((q : ℂ)⁻¹)
      (χ.evalNat q * lemma32PrimeMonomial q s)

noncomputable def lemma83ExceptionalEulerProduct {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d r : ℕ) (s : ℂ) : ℂ :=
  ∏ q ∈ (d*r).primeFactors, lemma83ExceptionalPrimeFactor χ β r q s

/-- A constructed holomorphic candidate, not defined as a totalized L-quotient. -/
noncomputable def lemma83EulerCorrection {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) (s : ℂ) : ℂ :=
  lemma83RegularEulerProduct χ β j (fun q => ¬q.val ∣ d*r) s *
    lemma83ExceptionalEulerProduct χ (β j) d r s

lemma lemma83_shifted_character_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (s : ℂ) :
    ‖lemma32PrimeMonomial q.val β * (χ.evalNat q.val * lemma32PrimeMonomial q.val s)‖ ≤
      (q.val : ℝ)^(-s.re) := by
  rw [norm_mul,lemma83_shift_monomial_norm q.property.pos β hβ,one_mul,norm_mul]
  calc
    _ ≤ 1*‖lemma32PrimeMonomial q.val s‖ :=
      mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one _) (norm_nonneg _)
    _ = _ := by rw [one_mul,lemma83_prime_monomial_norm_rpow q.property.pos]

lemma lemma83_shifted_character_norm_radius {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma32PrimeMonomial q.val β * (χ.evalNat q.val * lemma32PrimeMonomial q.val s)‖ ≤
      lemma83RegularRadius := by
  rw [norm_mul,lemma83_shift_monomial_norm q.property.pos β hβ,one_mul]
  exact lemma83_character_monomial_norm_radius χ q s hs

lemma lemma83_shifted_character_denominator_ne_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    1 - lemma32PrimeMonomial q.val β * (χ.evalNat q.val * lemma32PrimeMonomial q.val s) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn := (lemma83_shifted_character_norm_radius χ β hβ q s hs).trans_lt
    lemma83_regular_radius_lt_one
  rw [← h,norm_one] at hn
  linarith

lemma lemma83_exceptional_prime_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (r : ℕ) (q : Nat.Primes) :
    DifferentiableOn ℂ (lemma83ExceptionalPrimeFactor χ β r q.val)
      {s : ℂ | 9/10 < s.re} := by
  have hx : DifferentiableOn ℂ (fun s : ℂ => lemma32PrimeMonomial q.val β *
      (χ.evalNat q.val * lemma32PrimeMonomial q.val s)) {s : ℂ | 9/10 < s.re} :=
    (((lemma32_prime_monomial_differentiable q.val).differentiableOn).const_mul _).const_mul _
  have hd : ∀ s ∈ {s : ℂ | 9/10 < s.re},
      1-lemma32PrimeMonomial q.val β * (χ.evalNat q.val * lemma32PrimeMonomial q.val s) ≠ 0 :=
    fun s hs => lemma83_shifted_character_denominator_ne_zero χ β hβ q s hs.le
  unfold lemma83ExceptionalPrimeFactor
  by_cases hqr : q.val ∣ r
  · simp only [if_pos hqr,lemma83RCorrection]
    exact (hx.const_sub 1).inv hd
  · simp only [if_neg hqr,lemma83DCorrection]
    exact ((hx.div_const _).const_sub 1).div (hx.const_sub 1) hd

lemma lemma83_exceptional_product_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d r : ℕ) :
    AnalyticOnNhd ℂ (lemma83ExceptionalEulerProduct χ β d r) {s : ℂ | 9/10 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  apply DifferentiableOn.fun_finsetProd
  intro q hq
  exact lemma83_exceptional_prime_differentiableOn χ β hβ r ⟨q,Nat.prime_of_mem_primeFactors hq⟩

/-- Holomorphy of the full constructed correction, including every exceptional prime. -/
lemma lemma83_euler_correction_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ) :
    AnalyticOnNhd ℂ (lemma83EulerCorrection χ β j d r) {s : ℂ | 9/10 < s.re} :=
  (lemma83_regular_euler_product_analyticOnNhd χ β hβ j _).mul
    (lemma83_exceptional_product_analyticOnNhd χ (β j) (hβ j) d r)

lemma lemma83_r_correction_sub_one (a x : ℂ) (h : 1-a*x ≠ 0) :
    lemma83RCorrection a x - 1 = a*x/(1-a*x) := by
  unfold lemma83RCorrection
  field_simp
  ring

lemma lemma83_d_correction_sub_one (a u x : ℂ) (h : 1-a*x ≠ 0) (hu : 1-u ≠ 0) :
    lemma83DCorrection a u x - 1 = -u*a*x/((1-u)*(1-a*x)) := by
  unfold lemma83DCorrection
  repeat' field_simp [h,hu,mul_comm]
  all_goals ring

noncomputable def lemma83ExceptionalConstant : ℝ := (1-lemma83RegularRadius)⁻¹

lemma lemma83_exceptional_constant_pos : 0 < lemma83ExceptionalConstant :=
  inv_pos.mpr (sub_pos.mpr lemma83_regular_radius_lt_one)

lemma lemma83_r_correction_norm_error (a x : ℂ)
    (hy : ‖a*x‖ ≤ lemma83RegularRadius) :
    ‖lemma83RCorrection a x - 1‖ ≤ lemma83ExceptionalConstant * ‖a*x‖ := by
  have hd : 1-lemma83RegularRadius ≤ ‖1-a*x‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (a*x)
    norm_num only [norm_one] at hh
    linarith
  have hn : 1-a*x ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr lemma83_regular_radius_lt_one).trans_le hd)
  rw [lemma83_r_correction_sub_one a x hn,norm_div]
  calc
    _ ≤ ‖a*x‖/(1-lemma83RegularRadius) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr lemma83_regular_radius_lt_one) hd
    _ = _ := by simp [lemma83ExceptionalConstant,div_eq_mul_inv,mul_comm] <;> ring

lemma lemma83_d_correction_norm_error (a u x : ℂ)
    (hy : ‖a*x‖ ≤ lemma83RegularRadius) (hu : ‖u‖ ≤ 1/2) :
    ‖lemma83DCorrection a u x - 1‖ ≤ lemma83ExceptionalConstant * ‖a*x‖ := by
  have hd : 1-lemma83RegularRadius ≤ ‖1-a*x‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (a*x)
    norm_num only [norm_one] at hh
    linarith
  have hud : 1/2 ≤ ‖1-u‖ := by
    have hh := norm_sub_norm_le (1:ℂ) u
    norm_num only [norm_one] at hh
    linarith
  have hn : 1-a*x ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr lemma83_regular_radius_lt_one).trans_le hd)
  have hun : 1-u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hud)
  rw [lemma83_d_correction_sub_one a u x hn hun]
  have hnum : ‖-u*a*x‖ ≤ (1/2)*‖a*x‖ := by
    rw [mul_assoc,norm_mul,norm_neg]
    exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)
  have hden : (1/2)*(1-lemma83RegularRadius) ≤ ‖(1-u)*(1-a*x)‖ := by
    rw [norm_mul]
    exact mul_le_mul hud hd (sub_pos.mpr lemma83_regular_radius_lt_one).le (norm_nonneg _)
  rw [norm_div]
  calc
    _ ≤ ((1/2)*‖a*x‖)/((1/2)*(1-lemma83RegularRadius)) :=
      div_le_div₀ (by positivity) hnum
        (mul_pos (by norm_num) (sub_pos.mpr lemma83_regular_radius_lt_one)) hden
    _ = _ := by simp [lemma83ExceptionalConstant,div_eq_mul_inv,mul_comm] <;> ring

lemma lemma83_exceptional_prime_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (r : ℕ) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83ExceptionalPrimeFactor χ β r q.val s-1‖ ≤
      lemma83ExceptionalConstant * (q.val:ℝ)^(-s.re) := by
  have hu : ‖((q.val:ℂ)⁻¹)‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hy := lemma83_shifted_character_norm_radius χ β hβ q s hs
  have hb : ‖lemma83ExceptionalPrimeFactor χ β r q.val s-1‖ ≤
      lemma83ExceptionalConstant *
        ‖lemma32PrimeMonomial q.val β * (χ.evalNat q.val * lemma32PrimeMonomial q.val s)‖ := by
    unfold lemma83ExceptionalPrimeFactor
    split_ifs
    · exact lemma83_r_correction_norm_error _ _ hy
    · exact lemma83_d_correction_norm_error _ _ _ hy hu
  exact hb.trans (mul_le_mul_of_nonneg_left (lemma83_shifted_character_norm_le χ β hβ q s)
    lemma83_exceptional_constant_pos.le)

lemma lemma83_exceptional_prime_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (r : ℕ) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83ExceptionalPrimeFactor χ β r q.val s‖ ≤
      1 + lemma83ExceptionalConstant * (q.val:ℝ)^(-s.re) := by
  have he := lemma83_exceptional_prime_error_bound χ β hβ r q s hs
  have hh := norm_add_le (lemma83ExceptionalPrimeFactor χ β r q.val s-1) (1:ℂ)
  rw [sub_add_cancel,norm_one] at hh
  linarith

lemma lemma83_exceptional_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d r : ℕ) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83ExceptionalEulerProduct χ β d r s‖ ≤
      ∏ q ∈ (d*r).primeFactors, (1+lemma83ExceptionalConstant*(q:ℝ)^(-s.re)) := by
  unfold lemma83ExceptionalEulerProduct
  rw [norm_prod]
  apply prod_le_prod (fun q _ => norm_nonneg _)
  intro q hq
  exact lemma83_exceptional_prime_bound χ β hβ r ⟨q,Nat.prime_of_mem_primeFactors hq⟩ s hs

lemma lemma83_euler_correction_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83EulerCorrection χ β j d r s‖ ≤ lemma83RegularProductBound *
      ∏ q ∈ (d*r).primeFactors, (1+lemma83ExceptionalConstant*(q:ℝ)^(-s.re)) := by
  unfold lemma83EulerCorrection
  rw [norm_mul]
  exact mul_le_mul (lemma83_regular_euler_product_bound χ β hβ j _ s hs)
    (lemma83_exceptional_product_bound χ (β j) (hβ j) d r s hs)
    (norm_nonneg _) lemma83_regular_product_bound_pos.le

end ZhangLS.Spec
