import ZhangLS.Spec.Lemma152MonomialVariation
import ZhangLS.Spec.Lemma161CorrectionVariation

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma161_prime_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0)
    (hsmall : ‖β‖ ≤ 1/10) (q : Nat.Primes) (s : ℂ)
    (hs : 9/10 ≤ s.re) (hs1 : ‖s-1‖ ≤ 1/10) :
    ‖lemma161PrimeFactor χ β q s - lemma161PrimeFactor χ 0 q 1‖ ≤
      10*lemma152CorrectionConstant*(‖β‖+‖s-1‖)*(q.val:ℝ)^(-(17/10:ℝ)) := by
  let a := lemma32PrimeMonomial q.val β
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let x := lemma32PrimeMonomial q.val s
  have hC := lemma152_correction_constant_pos
  have hp0 : 0 < (q.val:ℝ) := Nat.cast_pos.mpr q.property.pos
  have hp1 : 1 ≤ (q.val:ℝ) := by exact_mod_cast q.property.one_lt.le
  have hu : ‖u‖ ≤ 1/2 := by
    simp only [u,norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hx : ‖x‖ ≤ lemma83RegularRadius := lemma152_monomial_norm_radius q s hs
  have ha : ‖a‖ ≤ 1 := by dsimp [a]; rw [lemma83_shift_monomial_norm q.property.pos _ hβ]
  have hv : ‖v‖ ≤ 1 := χ.evalNat_norm_le_one q.val
  have he : ‖a-1‖ ≤ 10*‖β‖*(q.val:ℝ)^(1/5:ℝ) :=
    lemma152_shift_monomial_variation q.property.pos β hsmall
  have hxu := lemma152_center_monomial_variation q.property.pos s hs1
  have hshift := lemma161_shift_variation_bound a u v x hu hv hx
  have hvar := lemma161_variable_variation_bound u v x hu hv hx
  have hshift' : ‖lemma152LocalCorrection a 0 u v x-lemma152LocalCorrection 1 0 u v x‖ ≤
      10*lemma152CorrectionConstant*‖β‖*(q.val:ℝ)^(-(17/10:ℝ)) := by
    calc
      _ ≤ lemma152CorrectionConstant*‖u‖*‖x‖*‖a-1‖ := hshift
      _ ≤ lemma152CorrectionConstant*(q.val:ℝ)⁻¹*(q.val:ℝ)^(-(9/10:ℝ))*
          (10*‖β‖*(q.val:ℝ)^(1/5:ℝ)) := by
        dsimp [u]
        rw [norm_inv,Complex.norm_natCast]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (lemma152_monomial_norm_le q s hs)
          (by positivity)) he (by positivity) (by positivity)
      _ = _ := by
        rw [← Real.rpow_neg_one]
        calc
          _ = (10*lemma152CorrectionConstant*‖β‖)*
            ((q.val:ℝ)^(-1:ℝ)*(q.val:ℝ)^(-(9/10:ℝ))*(q.val:ℝ)^(1/5:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hp0,← Real.rpow_add hp0]; norm_num
  have hvar' : ‖lemma152LocalCorrection 1 0 u v x-lemma152LocalCorrection 1 0 u v u‖ ≤
      10*lemma152CorrectionConstant*‖s-1‖*(q.val:ℝ)^(-(17/10:ℝ)) := by
    calc
      _ ≤ lemma152CorrectionConstant*‖u‖*‖x-u‖ := hvar
      _ ≤ lemma152CorrectionConstant*(q.val:ℝ)⁻¹*(10*‖s-1‖*(q.val:ℝ)^(-(4/5:ℝ))) := by
        dsimp [u]
        rw [norm_inv,Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hxu (by positivity)
      _ = (10*lemma152CorrectionConstant*‖s-1‖)*(q.val:ℝ)^(-(9/5:ℝ)) := by
        rw [← Real.rpow_neg_one]
        calc
          _ = (10*lemma152CorrectionConstant*‖s-1‖)*((q.val:ℝ)^(-1:ℝ)*(q.val:ℝ)^(-(4/5:ℝ))) := by ring
          _ = _ := by rw [← Real.rpow_add hp0]; norm_num
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : -(9/5:ℝ) ≤ -(17/10:ℝ)))
          (by positivity)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (lemma152LocalCorrection a 0 u v x) (lemma152LocalCorrection 1 0 u v x)
    (lemma152LocalCorrection 1 0 u v u)
  have hf : lemma161PrimeFactor χ 0 q 1 = lemma152LocalCorrection 1 0 u v u := by
    unfold lemma161PrimeFactor
    rw [lemma83_prime_monomial_one q.property.pos]
    simp [lemma32PrimeMonomial,u,v]
  rw [hf]
  change ‖lemma152LocalCorrection a 0 u v x-lemma152LocalCorrection 1 0 u v u‖ ≤ _
  exact ht.trans ((add_le_add hshift' hvar').trans (by ring_nf; rfl))

end ZhangLS.Spec
