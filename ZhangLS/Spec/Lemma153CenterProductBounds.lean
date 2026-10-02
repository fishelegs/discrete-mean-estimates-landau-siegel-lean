import ZhangLS.Spec.Lemma153RamifiedStrip
/-! Absolute, modulus-independent product bounds at the center for the
source-repaired Lemma 15.3 correction.  Ramified factors are retained exactly. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma153_center_majorant_summable :
    Summable (fun q : Nat.Primes => 100000*(q.val:ℝ)^(-(3/2:ℝ))) := by
  exact ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).subtype Nat.Prime).mul_left 100000

lemma lemma153_unramified_product_bound_pos : 0 < lemma153UnramifiedProductBound :=
  Real.exp_pos _

lemma lemma153_finite_center_majorant_product_le (S : Finset Nat.Primes) :
    (∏ q ∈ S, (1+100000*(q.val:ℝ)^(-(3/2:ℝ)))) ≤ lemma153UnramifiedProductBound := by
  apply (Real.prod_one_add_le_exp_sum S (fun q : Nat.Primes => by positivity)).trans
  apply Real.exp_le_exp.mpr
  exact lemma153_center_majorant_summable.sum_le_tsum S (fun q _ => by positivity)

/-- The ramified factor at one is real, independent of the shifts, and no
larger than one.  In particular it cannot produce a D-dependent loss. -/
lemma lemma153_ramified_center_norm_le_one (q : Nat.Primes) :
    ‖(1-(q.val:ℂ)⁻¹)^2‖ ≤ 1 := by
  have hq : (1:ℝ) ≤ q.val := by exact_mod_cast q.property.one_lt.le
  have hi : (q.val:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hi0 : 0 ≤ (q.val:ℝ)⁻¹ := by positivity
  have he : (1-(q.val:ℂ)⁻¹) = ((1-(q.val:ℝ)⁻¹ : ℝ):ℂ) := by push_cast; rfl
  rw [norm_pow,he,Complex.norm_of_nonneg (by linarith : 0 ≤ 1-(q.val:ℝ)⁻¹)]
  nlinarith

lemma lemma153_prime_center_norm_le {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    ‖lemma153PrimeFactor χ β γ q 1‖ ≤ 1+100000*(q.val:ℝ)^(-(3/2:ℝ)) := by
  unfold lemma153PrimeFactor
  split_ifs with hq
  · rw [lemma83_prime_monomial_one q.property.pos]
    exact (lemma153_ramified_center_norm_le_one q).trans (by
      have hp := Real.rpow_nonneg (Nat.cast_nonneg q.val : (0:ℝ) ≤ q.val) (-(3/2:ℝ))
      linarith)
  · have hh := norm_le_norm_sub_add (lemma153UnramifiedPrimeFactor χ β γ q 1) (1:ℂ)
    rw [norm_one] at hh
    linarith [lemma153_unramified_factor_error χ β γ hpar q 1 (by norm_num)]

end ZhangLS.Spec
