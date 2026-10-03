import ZhangLS.Spec.RoughCollisionKernels

/-! No logarithmic loss is hidden: at X<=P the collision error is
256*C*L^36/D^4, with an explicit o(alpha) certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex Filter
open scoped Classical Topology

noncomputable def roughCollisionUniformBudget (D : ℕ) : ℝ :=
  256*bCoefficientConstant*lemma23PaperL D^36/(D : ℝ)^4
noncomputable def roughCollisionNormalizedConstant : ℝ :=
  256*bCoefficientConstant*(Nat.factorial 45 : ℝ)/Real.pi

/-- The exact logarithmic loss comes from two tau_2 harmonic sums. -/
theorem roughCollision_harmonic_budget {D X : ℕ} (hL : 1≤lemma23PaperL D)
    (hX : 1≤X) (hXP : (X : ℝ)≤lemma23PaperP D) :
    16*bCoefficientConstant*(harmonic X : ℝ)^4/(D^4 : ℕ) ≤
      roughCollisionUniformBudget D := by
  have hX0 : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hH : 0≤(harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    positivity
  have hlog : Real.log (X : ℝ)≤lemma23PaperL D^9 := by
    simpa only [lemma23PaperP,Real.log_exp] using Real.log_le_log hX0 hXP
  have hpow : 1≤lemma23PaperL D^9 := one_le_pow₀ hL
  have hh : (harmonic X : ℝ)≤2*lemma23PaperL D^9 :=
    (harmonic_le_one_add_log X).trans (by linarith)
  have hp := pow_le_pow_left₀ hH hh 4
  unfold roughCollisionUniformBudget
  rw [Nat.cast_pow]
  calc
    _ ≤ 16*bCoefficientConstant*(2*lemma23PaperL D^9)^4/(D : ℝ)^4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hp (by positivity [b_coefficient_constant_nonneg])
    _ = _ := by ring

/-- All constants and the remaining D^-3 rate are explicit. The elementary
45th exponential-series term suffices; no asymptotic oracle is assumed. -/
theorem roughCollision_normalized_budget {D : ℕ} (hD : 0<D)
    (hL : 1≤lemma23PaperL D) :
    roughCollisionUniformBudget D/lemma44PaperAlpha D ≤
      roughCollisionNormalizedConstant/(D : ℝ)^3 := by
  have hDr : (0 : ℝ)<D := by exact_mod_cast hD
  have hL0 : 0<lemma23PaperL D := by linarith
  have hfac : 0<(Nat.factorial 45 : ℝ) := by exact_mod_cast Nat.factorial_pos 45
  have hpow : lemma23PaperL D^45 ≤ (Nat.factorial 45 : ℝ)*(D : ℝ) := by
    have hh := Real.pow_div_factorial_le_exp (lemma23PaperL D) hL0.le 45
    rw [lemma23PaperL,Real.exp_log hDr] at hh
    have hh' := (div_le_iff₀ hfac).mp hh
    simpa only [mul_comm] using hh'
  calc
    _ = (256*bCoefficientConstant/Real.pi)*(lemma23PaperL D^45/(D : ℝ)^4) := by
      unfold roughCollisionUniformBudget lemma44PaperAlpha lemma23PaperP
      rw [Real.log_exp]
      field_simp
    _ ≤ (256*bCoefficientConstant/Real.pi)*
        (((Nat.factorial 45 : ℝ)*(D : ℝ))/(D : ℝ)^4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [b_coefficient_constant_nonneg])
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ = roughCollisionNormalizedConstant/(D : ℝ)^3 := by
      unfold roughCollisionNormalizedConstant
      field_simp

/-- Uniform o(alpha), with the paper's actual alpha=pi/L^9 and fixed actual iotas. -/
theorem roughCollision_budget_isLittleO_alpha :
    (fun D : ℕ => roughCollisionUniformBudget D) =o[atTop]
      (fun D => lemma44PaperAlpha D) := by
  have hlog : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hL : ∀ᶠ D : ℕ in atTop, 1≤lemma23PaperL D := hlog.eventually_ge_atTop 1
  have hD : ∀ᶠ D : ℕ in atTop, 0<D := eventually_gt_atTop 0
  have hα : ∀ᶠ D : ℕ in atTop, 0<lemma44PaperAlpha D := by
    filter_upwards [hL] with D h
    simp only [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    exact div_pos Real.pi_pos (pow_pos (by linarith) _)
  apply (Asymptotics.isLittleO_iff_tendsto' (hα.mono (fun D h hz => (ne_of_gt h hz).elim))).mpr
  have hi : Tendsto (fun D : ℕ => (D : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun D : ℕ => roughCollisionNormalizedConstant/(D : ℝ)^3)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,zero_pow (by decide : (3 : ℕ)≠0),mul_zero] using
      (hi.pow 3).const_mul roughCollisionNormalizedConstant
  apply squeeze_zero' ?_ ?_ hz
  · filter_upwards [hα] with D h
    exact div_nonneg (by unfold roughCollisionUniformBudget; positivity [b_coefficient_constant_nonneg]) h.le
  · filter_upwards [hD,hL] with D hd hl
    exact roughCollision_normalized_budget hd hl

/-- Final closed collision attachment for the actual source kernels, preserving
beta_j(c'), every l1,l2, the original rough Q, and the exact support kernels. -/
theorem roughCollision_actual_source_uniform {D X : ℕ} (hD : 0<D)
    (hL : 1≤lemma23PaperL D) (hX : 1≤X) (hXP : (X : ℝ)≤lemma23PaperP D)
    (l₁ l₂ : ℕ) (c : ℝ) (j : Fin 3) :
    ‖(∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        lemma151First D (l₁*a)*lemma151Second D (l₂*b)*
          lemma151Rho (lemma83PaperBeta D c j) (a*b)/((a : ℂ)*(b : ℂ))) -
      (∑ a ∈ roughCollisionDomain D X,
        lemma151First D (l₁*a)*lemma151Rho (lemma83PaperBeta D c j) a/(a : ℂ))*
      (∑ b ∈ roughCollisionDomain D X,
        lemma151Second D (l₂*b)*lemma151Rho (lemma83PaperBeta D c j) b/(b : ℂ))‖ ≤
      roughCollisionUniformBudget D :=
  (roughCollision_actual_source_kernels D X l₁ l₂ hD hX c j).trans
    (roughCollision_harmonic_budget hL hX hXP)

end ZhangLS.Spec
