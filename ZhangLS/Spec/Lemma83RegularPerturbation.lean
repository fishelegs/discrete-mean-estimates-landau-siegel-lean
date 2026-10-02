import ZhangLS.Spec.Lemma83ProductPerturbation
import ZhangLS.Spec.Lemma83XiBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 500000

lemma lemma83_shift_monomial_sub_one_bound {p : ℕ} (hp : 0 < p) (β : ℂ) (hβ : β.re = 0) :
    ‖1-lemma32PrimeMonomial p β‖ ≤ ‖β‖*Real.log p := by
  have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have he : -β*(Real.log p:ℂ) = Complex.I*((-β.im*Real.log p:ℝ):ℂ) := by
    apply Complex.ext <;> simp [hβ]
  have hb : β = Complex.I*(β.im:ℂ) := by apply Complex.ext <;> simp [hβ]
  rw [norm_sub_rev,lemma32PrimeMonomial,he]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -β.im*Real.log p)
  apply hh.trans_eq
  nth_rw 2 [hb]
  rw [norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real]
  simp [Real.norm_eq_abs,abs_mul,abs_of_nonneg hl]

/-- A summable linear small-shift majorant for the regular Euler factors. -/
lemma lemma83_regular_prime_small_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (a : ℝ)
    (ha : 0 ≤ a) (hsmall : ∀ i, ‖β i‖ ≤ 3*a)
    (q : Nat.Primes) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83RegularPrimeFactor χ β j q s-1‖ ≤
      (120*lemma83ExceptionalConstant)*a*(q.val:ℝ)^(-(9/5:ℝ)) := by
  let b := lemma32PrimeMonomial q.val (β (j+1))
  let c := lemma32PrimeMonomial q.val (β (j+2))
  let t := lemma32PrimeMonomial q.val (1-β j)
  let x := χ.evalNat q.val*lemma32PrimeMonomial q.val s
  have hb : ‖1-b‖ ≤ 3*a*Real.log q.val :=
    (lemma83_shift_monomial_sub_one_bound q.property.pos _ (hβ _)).trans
      (mul_le_mul_of_nonneg_right (hsmall _) (Real.log_nonneg (by exact_mod_cast q.property.one_le)))
  have hc : ‖1-c‖ ≤ 2 := by
    have hh := norm_sub_le (1:ℂ) c
    dsimp [c] at hh
    rw [norm_one,lemma83_shift_monomial_norm q.property.pos _ (hβ _)] at hh
    norm_num at hh
    exact hh
  have ht : ‖t‖ = (q.val:ℝ)⁻¹ := lemma83_t_monomial_norm q.property.pos _ (hβ _)
  have ht2 : ‖t‖ ≤ 1/2 := by
    rw [ht]
    simpa only [norm_inv,Complex.norm_natCast] using lemma83_prime_reciprocal_norm_le_half q.property
  have htd := lemma83_one_sub_norm_ge_half ht2
  have hxd : 1-lemma83RegularRadius ≤ ‖1-x‖ := by
    have hh := norm_sub_norm_le (1:ℂ) x
    norm_num only [norm_one] at hh
    have hx := lemma83_character_monomial_norm_radius χ q s hs
    change ‖x‖ ≤ _ at hx
    linarith
  have hnum : ‖t*x*(1-b)*(1-c)‖ ≤
      6*a*Real.log q.val*(q.val:ℝ)^(-(19/10:ℝ)) := by
    rw [norm_mul,norm_mul,norm_mul,ht]
    have hh := mul_le_mul (mul_le_mul (lemma83_character_monomial_norm_le χ q s hs) hb
      (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hc
      (norm_nonneg _) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (q.val:ℝ)⁻¹)
    dsimp [x] at *
    calc
      _ ≤ (q.val:ℝ)⁻¹*((q.val:ℝ)^(-(9/10:ℝ))*(3*a*Real.log q.val)*2) := by nlinarith
      _ = _ := by
        rw [← Real.rpow_neg_one,show -(19/10:ℝ) = -1 + -(9/10) by norm_num,
          Real.rpow_add (Nat.cast_pos.mpr q.property.pos)]
        ring
  have hden : (1/2)*(1-lemma83RegularRadius) ≤ ‖(1-t)*(1-x)‖ := by
    rw [norm_mul]
    exact mul_le_mul htd hxd (sub_pos.mpr lemma83_regular_radius_lt_one).le (norm_nonneg _)
  change ‖lemma83RegularCorrection b c t x-1‖ ≤ _
  rw [lemma83RegularCorrection]
  simp only [sub_sub_cancel_left,norm_neg,norm_div]
  have hd := div_le_div₀ (by positivity) hnum
    (mul_pos (by norm_num) (sub_pos.mpr lemma83_regular_radius_lt_one)) hden
  have hlog := Real.log_natCast_le_rpow_div q.val (by norm_num : (0:ℝ)<1/10)
  have hlog' : Real.log q.val ≤ 10*(q.val:ℝ)^(1/10:ℝ) := by nlinarith
  calc
    _ ≤ (6*a*Real.log q.val*(q.val:ℝ)^(-(19/10:ℝ)))/((1/2)*(1-lemma83RegularRadius)) := hd
    _ ≤ (6*a*(10*(q.val:ℝ)^(1/10:ℝ))*(q.val:ℝ)^(-(19/10:ℝ)))/((1/2)*(1-lemma83RegularRadius)) := by
      gcongr
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr lemma83_regular_radius_lt_one.le)
    _ = _ := by
      rw [show -(9/5:ℝ) = 1/10 + -(19/10) by norm_num,
        Real.rpow_add (Nat.cast_pos.mpr q.property.pos)]
      unfold lemma83ExceptionalConstant
      field_simp
      ring

noncomputable def lemma83RegularShiftMass : ℝ :=
  ∑' q : Nat.Primes, (120*lemma83ExceptionalConstant)*(q.val:ℝ)^(-(9/5:ℝ))
noncomputable def lemma83RegularShiftConstant : ℝ :=
  lemma83RegularShiftMass*Real.exp lemma83RegularShiftMass

lemma lemma83_regular_shift_majorant_summable :
    Summable (fun q : Nat.Primes => (120*lemma83ExceptionalConstant)*(q.val:ℝ)^(-(9/5:ℝ))) :=
  ((Real.summable_nat_rpow.mpr (by norm_num : -(9/5:ℝ) < -1)).subtype Nat.Prime).mul_left _

lemma lemma83_regular_shift_mass_nonneg : 0 ≤ lemma83RegularShiftMass := by
  apply tsum_nonneg
  intro q
  positivity [lemma83_exceptional_constant_pos]

lemma lemma83_real_exp_small_scale (a M : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hM : 0 ≤ M) :
    Real.exp (a*M)-1 ≤ a*(M*Real.exp M) := by
  have ham : 0 ≤ a*M := mul_nonneg ha hM
  have hamM : a*M ≤ M := mul_le_of_le_one_left hM ha1
  have hh : |Real.exp (a*M)-1| ≤ |a*M| *Real.exp |a*M| := by
    simpa only [← Complex.ofReal_exp,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs] using lemma83_exp_sub_one_bound ((a*M:ℝ):ℂ)
  rw [abs_of_nonneg ham] at hh
  calc
    _ ≤ |Real.exp (a*M)-1| := le_abs_self _
    _ ≤ a*M*Real.exp (a*M) := hh
    _ ≤ a*M*Real.exp M := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hamM) ham
    _ = _ := by ring

lemma lemma83_regular_product_small_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hsmall : ∀ i, ‖β i‖ ≤ 3*a)
    (P : Nat.Primes → Prop) (s : ℂ) (hs : 9/10 ≤ s.re) :
    ‖lemma83RegularEulerProduct χ β j P s-1‖ ≤ a*lemma83RegularShiftConstant := by
  have hbound (q : Nat.Primes) : ‖lemma83RestrictedRegularFactor χ β j P q s-1‖ ≤
      a*((120*lemma83ExceptionalConstant)*(q.val:ℝ)^(-(9/5:ℝ))) := by
    unfold lemma83RestrictedRegularFactor
    split_ifs
    · convert lemma83_regular_prime_small_shift χ β hβ j a ha hsmall q s hs using 1 <;> ring
    · simp only [sub_self,norm_zero]
      positivity [lemma83_exceptional_constant_pos]
  have hfinite (S : Finset Nat.Primes) :
      ‖(∏ q ∈ S, lemma83RestrictedRegularFactor χ β j P q s)-1‖ ≤ a*lemma83RegularShiftConstant := by
    have hh := S.norm_prod_one_add_sub_one_le (fun q => lemma83RestrictedRegularFactor χ β j P q s-1)
    simp only [add_sub_cancel] at hh
    have hsum : (∑ q ∈ S, ‖lemma83RestrictedRegularFactor χ β j P q s-1‖) ≤
        a*lemma83RegularShiftMass := by
      calc
        _ ≤ ∑ q ∈ S, a*((120*lemma83ExceptionalConstant)*(q.val:ℝ)^(-(9/5:ℝ))) :=
          sum_le_sum (fun q _ => hbound q)
        _ = a*∑ q ∈ S, (120*lemma83ExceptionalConstant)*(q.val:ℝ)^(-(9/5:ℝ)) :=
          (mul_sum ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (lemma83_regular_shift_majorant_summable.sum_le_tsum S
            (fun q _ => by positivity [lemma83_exceptional_constant_pos])) ha
    exact (hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)).trans
      (lemma83_real_exp_small_scale a lemma83RegularShiftMass ha ha1 lemma83_regular_shift_mass_nonneg)
  have ht := (lemma83_regular_euler_product_multipliable χ β hβ j P s hs).hasProd
  apply le_of_tendsto (ht.sub_const 1).norm
  exact Filter.Eventually.of_forall hfinite

end ZhangLS.Spec
