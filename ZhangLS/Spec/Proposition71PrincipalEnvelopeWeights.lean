import ZhangLS.Spec.Proposition71EulerEnvelopeTau
import ZhangLS.Spec.Proposition71ConductorWeights

/-! Fully explicit fixed-divisor majorants for the original principal
contour's exterior arithmetic weights. All tau5 and finite-prime losses are
retained until a genuine four-variable harmonic sum. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 3500000

lemma proposition71_principal_euler_weight_le_tau {d₁ d₂ k : ℕ}
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) {σ : ℝ} (hσ : 1/2≤σ) :
    (lemma34Tau 5 d₁ : ℝ)*proposition71KappaEulerEnvelope d₁ σ*
      proposition71LambdaEulerEnvelope (d₁*d₂*k) σ≤
      (lemma34Tau 163840 d₁ : ℝ)*(lemma34Tau 32 d₂ : ℝ)*(lemma34Tau 32 k : ℝ) := by
  have hK := proposition71_kappa_euler_envelope_le_tau hd₁.ne' hσ
  have hLam := proposition71_lambda_euler_envelope_le_tau (Nat.mul_pos (Nat.mul_pos hd₁ hd₂) hk).ne' hσ
  have hK0 : 0≤proposition71KappaEulerEnvelope d₁ σ := by
    unfold proposition71KappaEulerEnvelope
    apply prod_nonneg
    intro p hp
    have hx := proposition71_prime_inverse_rpow_le_three_quarters (Nat.prime_of_mem_primeFactors hp) hσ
    have hden : 0<1-(p : ℝ)^(-σ) := by linarith
    positivity
  have hLam0 : 0≤proposition71LambdaEulerEnvelope (d₁*d₂*k) σ := by
    unfold proposition71LambdaEulerEnvelope
    apply prod_nonneg
    intro p hp
    have hx := proposition71_prime_inverse_rpow_le_three_quarters (Nat.prime_of_mem_primeFactors hp) hσ
    have hden : 0<1-(p : ℝ)^(-σ) := by linarith
    positivity
  have hprod : (lemma34Tau 32 (d₁*d₂*k) : ℝ)≤
      (lemma34Tau 32 d₁ : ℝ)*(lemma34Tau 32 d₂ : ℝ)*(lemma34Tau 32 k : ℝ) := by
    have h1 := proposition71_tau_submultiplicative 32 (d₁*d₂) k
    have h2 := proposition71_tau_submultiplicative 32 d₁ d₂
    exact_mod_cast h1.trans (Nat.mul_le_mul_right _ h2)
  have h5120 := lemma34_tau_product_le_real 5 1024 d₁ (by norm_num) (by norm_num)
  have h163840 := lemma34_tau_product_le_real 5120 32 d₁ (by norm_num) (by norm_num)
  norm_num only [Nat.reduceMul] at h5120 h163840
  calc
    _≤(lemma34Tau 5 d₁ : ℝ)*(lemma34Tau 1024 d₁ : ℝ)*
        ((lemma34Tau 32 d₁ : ℝ)*(lemma34Tau 32 d₂ : ℝ)*(lemma34Tau 32 k : ℝ)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _))
        (hLam.trans hprod) hLam0 (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _=((lemma34Tau 5 d₁ : ℝ)*(lemma34Tau 1024 d₁ : ℝ)*(lemma34Tau 32 d₁ : ℝ))*
        (lemma34Tau 32 d₂ : ℝ)*(lemma34Tau 32 k : ℝ) := by ring
    _≤((lemma34Tau 5120 d₁ : ℝ)*(lemma34Tau 32 d₁ : ℝ))*
        (lemma34Tau 32 d₂ : ℝ)*(lemma34Tau 32 k : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h5120 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    _≤_ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h163840 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- The actual exterior denominator left after q=p*k/l2 cancels k. -/
lemma proposition71_principal_envelope_weight_majorant {d₁ d₂ k l₂ : ℕ}
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hk : 0<k) (hl₂ : 0<l₂) {σ : ℝ} (hσ : 1/2≤σ) :
    (lemma34Tau 5 d₁ : ℝ)*proposition71KappaEulerEnvelope d₁ σ*
      proposition71LambdaEulerEnvelope (d₁*d₂*k) σ/
        ((d₁ : ℝ)*(d₂ : ℝ)*(k.totient : ℝ)*(l₂ : ℝ))≤
      ((lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*
        ((lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ))*
        ((lemma34Tau 64 k : ℝ)/(k : ℝ))*(1/(l₂ : ℝ)) := by
  have hb := proposition71_principal_euler_weight_le_tau hd₁ hd₂ hk hσ
  have hφ := proposition71_reciprocal_totient_le_tau hk
  have hτ := lemma34_tau_product_le_real 32 2 k (by norm_num) (by norm_num)
  norm_num only [Nat.reduceMul] at hτ
  have hAB : 0≤((lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*
      ((lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ)) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hlInv : 0≤1/(l₂ : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  calc
    _≤(lemma34Tau 163840 d₁ : ℝ)*(lemma34Tau 32 d₂ : ℝ)*(lemma34Tau 32 k : ℝ)/
        ((d₁ : ℝ)*(d₂ : ℝ)*(k.totient : ℝ)*(l₂ : ℝ)) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _=((lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*((lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ))*
        (lemma34Tau 32 k : ℝ)*(k.totient : ℝ)⁻¹*(1/(l₂ : ℝ)) := by ring
    _≤((lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*((lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ))*
        (lemma34Tau 32 k : ℝ)*((lemma34Tau 2 k : ℝ)/(k : ℝ))*(1/(l₂ : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hφ (mul_nonneg hAB (Nat.cast_nonneg _))) hlInv
    _=((lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*((lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ))*
        (((lemma34Tau 32 k : ℝ)*(lemma34Tau 2 k : ℝ))/(k : ℝ))*(1/(l₂ : ℝ)) := by ring
    _≤_ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _)) hAB) hlInv

/-- Complete four-variable harmonic budget for every original finite-prime
factor. This is an actual sum, with no generic summation bound assumed. -/
theorem proposition71_principal_envelope_outer_sum (X : ℕ) (hX : 1≤X)
    {σ : ℝ} (hσ : 1/2≤σ) :
    (∑d₁∈Icc 1 X,∑d₂∈Icc 1 X,∑k∈Icc 1 X,∑l₂∈Icc 1 X,
      (lemma34Tau 5 d₁ : ℝ)*proposition71KappaEulerEnvelope d₁ σ*
        proposition71LambdaEulerEnvelope (d₁*d₂*k) σ/
          ((d₁ : ℝ)*(d₂ : ℝ)*(k.totient : ℝ)*(l₂ : ℝ)))≤
      (1+Real.log (X : ℝ))^163937 := by
  let H := 1+Real.log (X : ℝ)
  have hH : 0≤H := by
    have hx : 1≤(X : ℝ) := by exact_mod_cast hX
    have hh := Real.log_nonneg hx
    dsimp [H]
    linarith
  have h1 := proposition71_tau_harmonic_bound 163840 X hX
  have h2 := proposition71_tau_harmonic_bound 32 X hX
  have h3 := proposition71_tau_harmonic_bound 64 X hX
  have h4 : (∑l∈Icc 1 X,1/(l : ℝ))≤H := by
    have hh := harmonic_le_one_add_log X
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div,H] using hh
  calc
    _≤∑d₁∈Icc 1 X,∑d₂∈Icc 1 X,∑k∈Icc 1 X,∑l₂∈Icc 1 X,
      ((lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*((lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ))*
        ((lemma34Tau 64 k : ℝ)/(k : ℝ))*(1/(l₂ : ℝ)) := by
      apply sum_le_sum; intro d₁ hd₁
      apply sum_le_sum; intro d₂ hd₂
      apply sum_le_sum; intro k hk
      apply sum_le_sum; intro l₂ hl₂
      exact proposition71_principal_envelope_weight_majorant (mem_Icc.mp hd₁).1
        (mem_Icc.mp hd₂).1 (mem_Icc.mp hk).1 (mem_Icc.mp hl₂).1 hσ
    _=(∑d₁∈Icc 1 X,(lemma34Tau 163840 d₁ : ℝ)/(d₁ : ℝ))*
        (∑d₂∈Icc 1 X,(lemma34Tau 32 d₂ : ℝ)/(d₂ : ℝ))*
        (∑k∈Icc 1 X,(lemma34Tau 64 k : ℝ)/(k : ℝ))*
        (∑l₂∈Icc 1 X,1/(l₂ : ℝ)) := by simp only [←sum_mul,←mul_sum]
    _≤H^163840*H^32*H^64*H := by gcongr
    _=H^163937 := by rw [←pow_add,←pow_add,←pow_succ]

end ZhangLS.Spec
