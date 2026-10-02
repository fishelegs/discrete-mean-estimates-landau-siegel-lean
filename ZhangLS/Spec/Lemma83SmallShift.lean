import ZhangLS.Spec.Lemma83RegularPerturbation
import ZhangLS.Spec.Lemma83ExceptionalPerturbation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 700000

noncomputable def lemma83PrimeProductScale : ℝ :=
  Real.exp (lemma83FiniteShiftWeight/Real.log 2)
noncomputable def lemma83TotalShiftConstant : ℝ :=
  lemma83RegularShiftConstant*(lemma83PrimeProductScale*lemma83FiniteShiftError+lemma83PrimeProductScale) +
    lemma83PrimeProductScale*lemma83FiniteShiftError

lemma lemma83_regular_shift_constant_nonneg : 0 ≤ lemma83RegularShiftConstant :=
  mul_nonneg lemma83_regular_shift_mass_nonneg (Real.exp_pos _).le

lemma lemma83_total_shift_constant_pos : 0 < lemma83TotalShiftConstant := by
  unfold lemma83TotalShiftConstant lemma83PrimeProductScale
  positivity [lemma83_regular_shift_constant_nonneg,lemma83_finite_shift_error_pos]

lemma lemma83_pi_prime_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (d r : ℕ) (hd : d ≠ 0) (hr : r ≠ 0) :
    ‖lemma83Pi χ d r‖ ≤ ∏ p ∈ (d*r).primeFactors, (1+lemma83FiniteShiftWeight/(p:ℝ)) := by
  rw [← lemma83_exceptional_product_zero_shift χ d r hd hr]
  unfold lemma83ExceptionalEulerProduct
  rw [norm_prod]
  apply prod_le_prod (fun p _ => norm_nonneg _)
  intro p hp
  have hh := lemma83_exceptional_prime_small_shift χ 0 (by simp) r
    ⟨p,Nat.prime_of_mem_primeFactors hp⟩ 1 (by norm_num) 0 (by norm_num)
    (by simp) (by simp) (by simp [Real.pi_pos.le])
  exact hh.2.2

lemma lemma83_euler_correction_small_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3)
    (d r : ℕ) (hd : d ≠ 0) (hr : r ≠ 0) (s : ℂ) (hs : 9/10 ≤ s.re)
    (a y : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : ∀ i, ‖β i‖ ≤ 3*a)
    (hs1 : ‖s-1‖ ≤ 5*a) (hy : 1 < y) (hcut : Real.log (d*r:ℕ) ≤ y)
    (hscale : a*y ≤ Real.pi) (K : ℕ) (hK : 3*lemma83FiniteShiftWeight ≤ (K:ℝ)) :
    ‖lemma83EulerCorrection χ β j d r s-lemma83Pi χ d r‖ ≤
      lemma83TotalShiftConstant*a*(1+Real.log y)^(K+2) := by
  let X := (1+Real.log y)^(K+2)
  let A := lemma83PrimeProductScale
  let B := lemma83PrimeProductScale*lemma83FiniteShiftError
  have hbase : 1 ≤ 1+Real.log y := by linarith [Real.log_nonneg hy.le]
  have hpow : (1+Real.log y)^K ≤ X := pow_le_pow_right₀ hbase (by omega)
  have hX : 0 ≤ X := pow_nonneg (zero_le_one.trans hbase) _
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg hA lemma83_finite_shift_error_pos.le
  have hE := lemma83_exceptional_product_small_shift χ (β j) (hβ j) d r hd hr s hs
    a y ha (hb j) hs1 hy hcut hscale K hK
  change ‖lemma83ExceptionalEulerProduct χ (β j) d r s-lemma83Pi χ d r‖ ≤ B*a*X at hE
  have hPi : ‖lemma83Pi χ d r‖ ≤ A*X := by
    apply (lemma83_pi_prime_product_bound χ d r hd hr).trans
    apply (lemma83_prime_product_uniform_le (d*r) (Nat.pos_of_ne_zero (mul_ne_zero hd hr))
      y lemma83FiniteShiftWeight K hy hcut lemma83_finite_shift_weight_pos.le hK).trans
    exact mul_le_mul_of_nonneg_left hpow hA
  have hEnorm : ‖lemma83ExceptionalEulerProduct χ (β j) d r s‖ ≤ (B+A)*X := by
    have hh := norm_add_le (lemma83ExceptionalEulerProduct χ (β j) d r s-lemma83Pi χ d r)
      (lemma83Pi χ d r)
    rw [sub_add_cancel] at hh
    have haa := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hB hX)
    nlinarith
  have hR := lemma83_regular_product_small_shift χ β hβ j a ha ha1 hb
    (fun q => ¬q.val ∣ d*r) s hs
  unfold lemma83EulerCorrection
  rw [show lemma83RegularEulerProduct χ β j (fun q => ¬q.val ∣ d*r) s *
      lemma83ExceptionalEulerProduct χ (β j) d r s-lemma83Pi χ d r =
      (lemma83RegularEulerProduct χ β j (fun q => ¬q.val ∣ d*r) s-1)*
        lemma83ExceptionalEulerProduct χ (β j) d r s +
        (lemma83ExceptionalEulerProduct χ (β j) d r s-lemma83Pi χ d r) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hh := add_le_add
    (mul_le_mul hR hEnorm (norm_nonneg _) (mul_nonneg ha lemma83_regular_shift_constant_nonneg)) hE
  apply hh.trans_eq
  dsimp [A,B,X]
  unfold lemma83TotalShiftConstant
  ring

/-- Every fixed polynomial in log L is eventually smaller than L, uniformly in all arithmetic data. -/
lemma lemma83_polylog_eventually_le (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, C*(1+9*Real.log L)^N ≤ L := by
  have he := (Real.isLittleO_pow_log_id_atTop (n := N)).bound
    (show 0 < (C*(10:ℝ)^N)⁻¹ by positivity)
  filter_upwards [he,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with L hL hl h1
  have hlog : 0 ≤ Real.log L := le_trans (by norm_num) hl
  simp only [Real.norm_eq_abs,abs_pow,abs_of_nonneg hlog,Function.id_def,
    abs_of_nonneg (zero_le_one.trans h1)] at hL
  have hp : (1+9*Real.log L)^N ≤ (10*Real.log L)^N :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ C*(10:ℝ)^N by positivity)
  have hc : C*(10:ℝ)^N ≠ 0 := ne_of_gt (by positivity)
  rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul] at hh
  exact (mul_le_mul_of_nonneg_left hp hC.le).trans (by simpa [mul_pow,mul_assoc] using hh)

end ZhangLS.Spec
