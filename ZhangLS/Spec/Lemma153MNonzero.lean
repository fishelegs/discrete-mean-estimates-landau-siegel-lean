import ZhangLS.Spec.Lemma152EulerProduct
import ZhangLS.Spec.Lemma32ModulusFactors

/-! Zero-center positivity and nonzero stability shared by Lemmas 15.2–15.3.
No nonzero denominator or main estimate is assumed: the zero-center product is
proved to have real part at least one from its actual Euler factors. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology Set
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma153_zero_center_factor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) :
    lemma152PrimeFactor χ (fun _ => 0) q 1 =
      if q.val ∣ D then 1 else
        (1-χ.evalNat q.val*(q.val:ℂ)^(-2:ℤ))/(1-(q.val:ℂ)^(-2:ℤ)) := by
  have hu : ‖(q.val:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hun := lemma83_one_sub_ne_zero hu
  have hup : 1+(q.val:ℂ)⁻¹ ≠ 0 := by
    simpa using lemma83_one_sub_ne_zero (show ‖-(q.val:ℂ)⁻¹‖ < 1 by simpa using hu)
  unfold lemma152PrimeFactor
  rw [show lemma32PrimeMonomial q.val 1 = (q.val:ℂ)⁻¹ by
    rw [lemma32_prime_monomial_eq_cpow q.property.pos,Complex.cpow_neg_one]]
  simp only [lemma32PrimeMonomial,mul_zero,zero_mul,neg_zero,Complex.exp_zero]
  by_cases hq : q.val ∣ D
  · rw [if_pos hq,χ.evalNat_eq_zero_of_dvd_modulus hq q.property.ne_one,
      lemma152_local_correction_ramified]
  · rw [if_neg hq,lemma152_local_correction_at_center _ _
      (lemma32_character_prime_cases_of_not_dvd χ q.property hq) hun hup]
    simp [zpow_neg,zpow_ofNat,pow_succ]

lemma lemma153_zero_center_equals_main {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma152EulerProduct χ (fun _ => 0) 1 = lemma152MainTerm χ := by
  unfold lemma152EulerProduct lemma152MainTerm
  rw [← tprod_subtype_eq_of_mulSupport_subset
    (f := fun q : Nat.Primes => lemma152PrimeFactor χ (fun _ => 0) q 1)
    (s := {q : Nat.Primes | ¬q.val ∣ D}) (by
      intro q hq
      by_contra hn
      have hd : q.val ∣ D := not_not.mp hn
      exact hq (by
        change lemma152PrimeFactor χ (fun _ => 0) q 1 = 1
        rw [lemma153_zero_center_factor,if_pos hd]))]
  apply tprod_congr
  intro q
  rw [lemma153_zero_center_factor,if_neg q.property]

lemma lemma153_zero_center_factor_real {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) :
    (lemma152PrimeFactor χ (fun _ => 0) q 1).im = 0 ∧
      1 ≤ (lemma152PrimeFactor χ (fun _ => 0) q 1).re := by
  rw [lemma153_zero_center_factor]
  split_ifs with hq
  · norm_num
  · have hqpos : (0:ℝ) < q.val := Nat.cast_pos.mpr q.property.pos
    have hqone : (1:ℝ) < q.val := by exact_mod_cast q.property.one_lt
    have hr : (q.val:ℝ)⁻¹ < 1 := (inv_lt_one₀ hqpos).mpr hqone
    have hr0 : 0 ≤ (q.val:ℝ)⁻¹ := by positivity
    have hr2 : 0 < 1-((q.val:ℝ)⁻¹)^2 := by nlinarith
    have hc : (q.val:ℂ)^(-2:ℤ) = ((((q.val:ℝ)⁻¹)^2:ℝ):ℂ) := by
      simp [zpow_neg,zpow_ofNat]
    rw [hc]
    rcases lemma32_character_prime_cases_of_not_dvd χ q.property hq with hχ | hχ
    · rw [hχ]
      have hd : (1:ℂ)-↑(((q.val:ℝ)⁻¹)^2) ≠ 0 := by
        exact_mod_cast hr2.ne'
      simp only [one_mul,div_self hd,one_im,one_re,le_refl,and_self]
    · rw [hχ]
      have he : (1-(-1:ℂ)*↑(((q.val:ℝ)⁻¹)^2))/(1-↑(((q.val:ℝ)⁻¹)^2)) =
          (((1+((q.val:ℝ)⁻¹)^2)/(1-((q.val:ℝ)⁻¹)^2):ℝ):ℂ) := by
        push_cast
        ring
      rw [he]
      simp only [ofReal_im,ofReal_re,true_and]
      apply (le_div_iff₀ hr2).mpr
      nlinarith

lemma lemma153_real_product_ge_one {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ S, (f i).im = 0 ∧ 1 ≤ (f i).re) :
    (∏ i ∈ S, f i).im = 0 ∧ 1 ≤ (∏ i ∈ S, f i).re := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi]
    have hfi := hf i (mem_insert_self i S)
    have hS := ih (fun j hj => hf j (mem_insert_of_mem hj))
    simp only [mul_re,mul_im,hfi.1,hS.1,mul_zero,zero_mul,add_zero,sub_zero]
    exact ⟨True.intro,one_le_mul_of_one_le_of_one_le hfi.2 hS.2⟩

lemma lemma153_zero_center_re_ge_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    1 ≤ (lemma152EulerProduct χ (fun _ => 0) 1).re := by
  have hp := (lemma152_euler_product_multipliable χ (fun _ => 0) (by simp) 1 (by norm_num)).hasProd
  have ht := Complex.continuous_re.tendsto _ |>.comp hp
  apply ge_of_tendsto' ht
  intro S
  exact (lemma153_real_product_ge_one S _ (fun q _ => lemma153_zero_center_factor_real χ q)).2

lemma lemma153_main_re_ge_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    1 ≤ (lemma152MainTerm χ).re := by
  rw [← lemma153_zero_center_equals_main]
  exact lemma153_zero_center_re_ge_one χ

lemma lemma153_main_norm_ge_one {D : ℕ} (χ : RealPrimitiveCharacter D) :
    1 ≤ ‖lemma152MainTerm χ‖ :=
  (lemma153_main_re_ge_one χ).trans (Complex.re_le_norm _)

lemma lemma153_main_ne_zero {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma152MainTerm χ ≠ 0 := by
  intro h
  have hh := lemma153_main_norm_ge_one χ
  rw [h,norm_zero] at hh
  norm_num at hh

/-- Apply the independently proved quantitative comparison at this point.
This is a stability lemma, not an assumption of the desired comparison. -/
lemma lemma153_nonzero_of_center_distance_lt_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (z : ℂ) (hz : ‖z-lemma152MainTerm χ‖ < 1) : z ≠ 0 := by
  intro h
  subst z
  simp only [zero_sub,norm_neg] at hz
  exact (not_lt_of_ge (lemma153_main_norm_ge_one χ)) hz

end ZhangLS.Spec
