import ZhangLS.Spec.Lemma83ProductPerturbation
import ZhangLS.Spec.Lemma83XiBounds
import ZhangLS.Spec.Lemma83ContinuationAgreement
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 600000

lemma lemma83_r_correction_difference (y z : ℂ) (hy : 1-y ≠ 0) (hz : 1-z ≠ 0) :
    lemma83RCorrection 1 y-lemma83RCorrection 1 z = (y-z)/((1-y)*(1-z)) := by
  unfold lemma83RCorrection
  simp only [one_mul]
  field_simp
  ring

lemma lemma83_d_correction_difference (u y z : ℂ)
    (hu : 1-u ≠ 0) (hy : 1-y ≠ 0) (hz : 1-z ≠ 0) :
    lemma83DCorrection 1 u y-lemma83DCorrection 1 u z =
      -u*(y-z)/((1-u)*(1-y)*(1-z)) := by
  unfold lemma83DCorrection
  simp only [one_mul]
  repeat' field_simp [hu,hy,hz]
  all_goals ring

lemma lemma83_r_correction_lipschitz (y z : ℂ)
    (hy : ‖y‖ ≤ lemma83RegularRadius) (hz : ‖z‖ ≤ 1/2) :
    ‖lemma83RCorrection 1 y-lemma83RCorrection 1 z‖ ≤
      (2*lemma83ExceptionalConstant)*‖y-z‖ := by
  have hdy : 1-lemma83RegularRadius ≤ ‖1-y‖ := by
    have hh := norm_sub_norm_le (1:ℂ) y
    norm_num only [norm_one] at hh
    linarith
  have hdz := lemma83_one_sub_norm_ge_half hz
  have hny : 1-y ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr lemma83_regular_radius_lt_one).trans_le hdy)
  have hnz : 1-z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hdz)
  rw [lemma83_r_correction_difference y z hny hnz,norm_div,norm_mul]
  have hd := mul_le_mul hdy hdz (by norm_num : (0:ℝ) ≤ 1/2) (norm_nonneg _)
  calc
    _ ≤ ‖y-z‖/((1-lemma83RegularRadius)*(1/2)) :=
      div_le_div_of_nonneg_left (norm_nonneg _)
        (mul_pos (sub_pos.mpr lemma83_regular_radius_lt_one) (by norm_num)) hd
    _ = _ := by unfold lemma83ExceptionalConstant; field_simp

lemma lemma83_d_correction_lipschitz (u y z : ℂ)
    (hu : ‖u‖ ≤ 1/2) (hy : ‖y‖ ≤ lemma83RegularRadius) (hz : ‖z‖ ≤ 1/2) :
    ‖lemma83DCorrection 1 u y-lemma83DCorrection 1 u z‖ ≤
      (2*lemma83ExceptionalConstant)*‖y-z‖ := by
  have hdy : 1-lemma83RegularRadius ≤ ‖1-y‖ := by
    have hh := norm_sub_norm_le (1:ℂ) y
    norm_num only [norm_one] at hh
    linarith
  have hdz := lemma83_one_sub_norm_ge_half hz
  have hdu := lemma83_one_sub_norm_ge_half hu
  have hny : 1-y ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr lemma83_regular_radius_lt_one).trans_le hdy)
  have hnz : 1-z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hdz)
  have hnu : 1-u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hdu)
  rw [lemma83_d_correction_difference u y z hnu hny hnz,norm_div,norm_mul,norm_neg,
    norm_mul,norm_mul]
  have hnum := mul_le_mul_of_nonneg_right hu (norm_nonneg (y-z))
  have hd : (1/2)*(1-lemma83RegularRadius)*(1/2) ≤ ‖1-u‖*‖1-y‖*‖1-z‖ :=
    mul_le_mul (mul_le_mul hdu hdy (sub_pos.mpr lemma83_regular_radius_lt_one).le (norm_nonneg _))
      hdz (by norm_num) (by positivity)
  calc
    _ ≤ ((1/2)*‖y-z‖)/((1/2)*(1-lemma83RegularRadius)*(1/2)) :=
      div_le_div₀ (by positivity) hnum (by positivity [lemma83_regular_radius_lt_one]) hd
    _ = _ := by unfold lemma83ExceptionalConstant; field_simp

lemma lemma83_exceptional_prime_lipschitz {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (r : ℕ) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83ExceptionalPrimeFactor χ β r q.val s - lemma83ExceptionalPrimeFactor χ 0 r q.val 1‖ ≤
      (2*lemma83ExceptionalConstant)*
        ‖χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β)-χ.evalNat q.val/(q.val:ℂ)‖ := by
  have hy := lemma83_shifted_character_norm_radius χ β hβ q s hs
  have hz : ‖χ.evalNat q.val/(q.val:ℂ)‖ ≤ 1/2 := by
    rw [div_eq_mul_inv,← lemma83_prime_monomial_one q.property.pos]
    exact lemma83_character_monomial_half χ q 1 (by norm_num)
  have he : lemma32PrimeMonomial q.val β * (χ.evalNat q.val*lemma32PrimeMonomial q.val s) =
      χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β) := by
    rw [lemma83_prime_monomial_add]
    ring
  rw [he] at hy
  unfold lemma83ExceptionalPrimeFactor
  have hzmon : lemma32PrimeMonomial q.val 0 = 1 := by simp [lemma32PrimeMonomial]
  rw [hzmon,lemma83_prime_monomial_one q.property.pos]
  by_cases hq : q.val ∣ r
  · simp only [if_pos hq]
    have hh := lemma83_r_correction_lipschitz _ _ hy hz
    simpa only [lemma83RCorrection,one_mul,div_eq_mul_inv,← he] using hh
  · simp only [if_neg hq]
    have hh := lemma83_d_correction_lipschitz _ _ _ (lemma83_prime_reciprocal_norm_le_half q.property) hy hz
    simpa only [lemma83DCorrection,one_mul,div_eq_mul_inv,← he] using hh

noncomputable def lemma83FiniteShiftB : ℝ := 8*Real.pi
noncomputable def lemma83FiniteShiftWeight : ℝ :=
  lemma83ExceptionalConstant*(1+lemma83FiniteShiftB*Real.exp lemma83FiniteShiftB)
noncomputable def lemma83FiniteShiftError : ℝ :=
  16*lemma83ExceptionalConstant*Real.exp lemma83FiniteShiftB

lemma lemma83_finite_shift_weight_pos : 0 < lemma83FiniteShiftWeight := by
  unfold lemma83FiniteShiftWeight lemma83FiniteShiftB
  positivity [lemma83_exceptional_constant_pos]

lemma lemma83_finite_shift_error_pos : 0 < lemma83FiniteShiftError := by
  unfold lemma83FiniteShiftError
  positivity [lemma83_exceptional_constant_pos]

lemma lemma83_character_monomial_small_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (w : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hw : ‖w‖ ≤ 8*a) (hlog : a*Real.log q.val ≤ Real.pi) :
    ‖χ.evalNat q.val*lemma32PrimeMonomial q.val (1+w)-χ.evalNat q.val/(q.val:ℂ)‖ ≤
      (8*Real.exp lemma83FiniteShiftB)*a*Real.log q.val/(q.val:ℝ) := by
  have hl : 0 ≤ Real.log (q.val:ℝ) := Real.log_nonneg (by exact_mod_cast q.property.one_le)
  have hwlog : ‖w‖*Real.log q.val ≤ lemma83FiniteShiftB := by
    unfold lemma83FiniteShiftB
    nlinarith [mul_le_mul_of_nonneg_right hw hl]
  have hh := lemma83_monomial_near_one q.property.pos w
  have hn : ‖χ.evalNat q.val*lemma32PrimeMonomial q.val (1+w)-χ.evalNat q.val/(q.val:ℂ)‖ ≤
      ‖lemma32PrimeMonomial q.val (1+w)-(q.val:ℂ)⁻¹‖ := by
    rw [div_eq_mul_inv,← mul_sub,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)
  apply (hn.trans hh).trans
  have he := Real.exp_le_exp.mpr hwlog
  calc
    _ ≤ (q.val:ℝ)⁻¹*((8*a)*Real.log q.val)*Real.exp lemma83FiniteShiftB := by
      gcongr
    _ = _ := by ring

lemma lemma83_exceptional_prime_small_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (r : ℕ) (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re)
    (a : ℝ) (ha : 0 ≤ a) (hb : ‖β‖ ≤ 3*a) (hs1 : ‖s-1‖ ≤ 5*a)
    (hlog : a*Real.log q.val ≤ Real.pi) :
    ‖lemma83ExceptionalPrimeFactor χ β r q.val s-lemma83ExceptionalPrimeFactor χ 0 r q.val 1‖ ≤
        lemma83FiniteShiftError*a*Real.log q.val/(q.val:ℝ) ∧
      ‖lemma83ExceptionalPrimeFactor χ β r q.val s‖ ≤ 1+lemma83FiniteShiftWeight/(q.val:ℝ) ∧
      ‖lemma83ExceptionalPrimeFactor χ 0 r q.val 1‖ ≤ 1+lemma83FiniteShiftWeight/(q.val:ℝ) := by
  let w : ℂ := s-1+β
  let y : ℂ := χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β)
  let z : ℂ := χ.evalNat q.val/(q.val:ℂ)
  have hw : ‖w‖ ≤ 8*a := (norm_add_le (s-1) β).trans (by linarith)
  have he : 1+w = s+β := by dsimp [w]; ring
  have hδ := lemma83_character_monomial_small_shift χ q w a ha hw hlog
  rw [he] at hδ
  change ‖y-z‖ ≤ _ at hδ
  have hδ' : ‖y-z‖ ≤ lemma83FiniteShiftB*Real.exp lemma83FiniteShiftB/(q.val:ℝ) := by
    apply hδ.trans
    apply (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr q.property.pos)).mpr
    unfold lemma83FiniteShiftB
    nlinarith [mul_le_mul_of_nonneg_left hlog (le_of_lt (Real.exp_pos (8*Real.pi)))]
  have hz : ‖z‖ ≤ 1/(q.val:ℝ) := by
    dsimp [z]
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (χ.evalNat_norm_le_one _) (Nat.cast_nonneg _)
  have hy : ‖y‖ ≤ (1+lemma83FiniteShiftB*Real.exp lemma83FiniteShiftB)/(q.val:ℝ) := by
    have hh := norm_add_le (y-z) z
    rw [sub_add_cancel] at hh
    have hh' := hh.trans (add_le_add hδ' hz)
    convert hh' using 1 <;> ring
  have hxy : lemma32PrimeMonomial q.val β * (χ.evalNat q.val*lemma32PrimeMonomial q.val s) = y := by
    dsimp [y]
    rw [lemma83_prime_monomial_add]
    ring
  have hnorm : ‖lemma83ExceptionalPrimeFactor χ β r q.val s-1‖ ≤
      lemma83ExceptionalConstant*‖y‖ := by
    have hrad := lemma83_shifted_character_norm_radius χ β hβ q s hs
    unfold lemma83ExceptionalPrimeFactor
    split_ifs
    · simpa only [hxy] using lemma83_r_correction_norm_error _ _ hrad
    · simpa only [hxy] using lemma83_d_correction_norm_error _ _ _ hrad
        (lemma83_prime_reciprocal_norm_le_half q.property)
  have hnorm' : ‖lemma83ExceptionalPrimeFactor χ β r q.val s-1‖ ≤
      lemma83FiniteShiftWeight/(q.val:ℝ) := by
    exact (hnorm.trans (mul_le_mul_of_nonneg_left hy lemma83_exceptional_constant_pos.le)).trans_eq
      (by unfold lemma83FiniteShiftWeight; ring)
  have hweight : lemma83ExceptionalConstant ≤ lemma83FiniteShiftWeight := by
    unfold lemma83FiniteShiftWeight lemma83FiniteShiftB
    nlinarith [lemma83_exceptional_constant_pos,Real.pi_pos,Real.exp_pos (8*Real.pi),
      mul_pos Real.pi_pos (Real.exp_pos (8*Real.pi))]
  constructor
  · have hh := lemma83_exceptional_prime_lipschitz χ β hβ r q s hs
    change _ ≤ (2*lemma83ExceptionalConstant)*‖y-z‖ at hh
    apply (hh.trans (mul_le_mul_of_nonneg_left hδ (by positivity [lemma83_exceptional_constant_pos]))).trans_eq
    unfold lemma83FiniteShiftError
    ring
  constructor
  · have hh := norm_add_le (lemma83ExceptionalPrimeFactor χ β r q.val s-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    linarith
  · have hh := lemma83_exceptional_prime_bound χ 0 (by simp) r q 1 (by norm_num)
    simp only [Complex.one_re,Real.rpow_neg_one] at hh
    have hcmp := div_le_div_of_nonneg_right hweight (Nat.cast_nonneg q.val)
    simp only [div_eq_mul_inv] at hcmp ⊢
    exact hh.trans (by linarith)

lemma lemma83_exceptional_product_small_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d r : ℕ) (hd : d ≠ 0) (hr : r ≠ 0)
    (s : ℂ) (hs : 9/10 ≤ s.re) (a y : ℝ) (ha : 0 ≤ a)
    (hb : ‖β‖ ≤ 3*a) (hs1 : ‖s-1‖ ≤ 5*a) (hy : 1 < y)
    (hcut : Real.log (d*r:ℕ) ≤ y) (hscale : a*y ≤ Real.pi)
    (K : ℕ) (hK : 3*lemma83FiniteShiftWeight ≤ (K:ℝ)) :
    ‖lemma83ExceptionalEulerProduct χ β d r s-lemma83Pi χ d r‖ ≤
      (Real.exp (lemma83FiniteShiftWeight/Real.log 2)*lemma83FiniteShiftError)*
        a*(1+Real.log y)^(K+2) := by
  let S := (d*r).primeFactors
  have hlog (p : ℕ) (hp : p ∈ S) : a*Real.log p ≤ Real.pi := by
    have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
    have hpn : (p:ℝ) ≤ (d*r:ℕ) := by exact_mod_cast Nat.le_of_mem_primeFactors hp
    exact (mul_le_mul_of_nonneg_left ((Real.log_le_log hp0 hpn).trans hcut) ha).trans hscale
  have hlocal (p : ℕ) (hp : p ∈ S) := lemma83_exceptional_prime_small_shift χ β hβ r
    ⟨p,Nat.prime_of_mem_primeFactors hp⟩ s hs a ha hb hs1 (hlog p hp)
  have ht := lemma83_product_perturbation S
    (fun p => lemma83ExceptionalPrimeFactor χ β r p s)
    (fun p => lemma83ExceptionalPrimeFactor χ 0 r p 1)
    (fun p => 1+lemma83FiniteShiftWeight/(p:ℝ))
    (fun p => lemma83FiniteShiftError*a*Real.log p/(p:ℝ))
    (fun p _ => le_add_of_nonneg_right (by positivity [lemma83_finite_shift_weight_pos]))
    (fun p hp => (hlocal p hp).2.1) (fun p hp => (hlocal p hp).2.2)
    (fun p hp => (hlocal p hp).1)
  have hp := lemma83_prime_product_uniform_le (d*r) (Nat.pos_of_ne_zero (mul_ne_zero hd hr))
    y lemma83FiniteShiftWeight K hy hcut lemma83_finite_shift_weight_pos.le hK
  have hl := lemma83_prime_log_sum_uniform_le (d*r) (Nat.pos_of_ne_zero (mul_ne_zero hd hr)) y hy hcut
  have he : (∑ p ∈ S, lemma83FiniteShiftError*a*Real.log p/(p:ℝ)) ≤
      lemma83FiniteShiftError*a*(1+Real.log y)^2 := by
    calc
      _ = lemma83FiniteShiftError*a*∑ p ∈ S, Real.log p/(p:ℝ) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg lemma83_finite_shift_error_pos.le ha)
  change ‖lemma83ExceptionalEulerProduct χ β d r s-lemma83ExceptionalEulerProduct χ 0 d r 1‖ ≤ _ at ht
  rw [lemma83_exceptional_product_zero_shift χ d r hd hr] at ht
  have hepos : 0 ≤ ∑ p ∈ S, lemma83FiniteShiftError*a*Real.log p/(p:ℝ) := by
    apply sum_nonneg
    intro p hp
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
    positivity [lemma83_finite_shift_error_pos]
  have hbase : 0 ≤ 1+Real.log y := by linarith [Real.log_nonneg hy.le]
  apply (ht.trans (mul_le_mul hp he hepos (mul_nonneg (Real.exp_pos _).le (pow_nonneg hbase K)))).trans_eq
  rw [pow_add]
  ring

end ZhangLS.Spec
