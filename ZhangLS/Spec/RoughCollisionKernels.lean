import ZhangLS.Spec.RoughCollisionBound

/-! Uniform collision removal for the actual source U and V kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def roughCollisionDomain (D X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun a => a.Coprime (lemma151Q D))

lemma roughCollision_weighted_defect_bound {β : ℂ} (hβ : β.re=0)
    (u v : ℕ → ℂ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : ∀n, ‖u n‖≤A) (hv : ∀n, ‖v n‖≤B) (a b : ℕ) :
    ‖u a*v b*(lemma151Rho β (a*b)-lemma151Rho β a*lemma151Rho β b)/
      ((a : ℂ)*(b : ℂ))‖ ≤
      2*A*B*(if ¬a.Coprime b then
        ((lemma34Tau 2 a : ℝ)/(a : ℝ))*((lemma34Tau 2 b : ℝ)/(b : ℝ)) else 0) := by
  by_cases hab : a.Coprime b
  · rw [(roughCollision_rho_multiplicative β).map_mul_of_coprime hab]
    simp [hab]
  · rw [if_pos hab,norm_div,norm_mul,norm_mul,norm_mul,norm_natCast,norm_natCast]
    calc
      _ ≤ (A*B)*(2*(lemma34Tau 2 a : ℝ)*(lemma34Tau 2 b : ℝ))/((a : ℝ)*(b : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul (hu a) (hv b) (norm_nonneg _) hA)
          (roughCollision_rho_defect hβ a b) (norm_nonneg _) (mul_nonneg hA hB)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv]; ring

/-- No coprime-factor identity is used on colliding pairs. The defect between
the actual double sum and the product of one-kernel sums is explicitly small. -/
theorem roughCollision_kernel_factorization (D X : ℕ) (hD : 0<D) (hX : 1≤X)
    {β : ℂ} (hβ : β.re=0) (u v : ℕ → ℂ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : ∀n, ‖u n‖≤A) (hv : ∀n, ‖v n‖≤B) :
    ‖(∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        u a*v b*lemma151Rho β (a*b)/((a : ℂ)*(b : ℂ))) -
      (∑ a ∈ roughCollisionDomain D X, u a*lemma151Rho β a/(a : ℂ))*
      (∑ b ∈ roughCollisionDomain D X, v b*lemma151Rho β b/(b : ℂ))‖ ≤
      16*A*B*(harmonic X : ℝ)^4/(D^4 : ℕ) := by
  have he : (∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        u a*v b*lemma151Rho β (a*b)/((a : ℂ)*(b : ℂ))) -
      (∑ a ∈ roughCollisionDomain D X, u a*lemma151Rho β a/(a : ℂ))*
      (∑ b ∈ roughCollisionDomain D X, v b*lemma151Rho β b/(b : ℂ)) =
      ∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        u a*v b*(lemma151Rho β (a*b)-lemma151Rho β a*lemma151Rho β b)/
          ((a : ℂ)*(b : ℂ)) := by
    rw [sum_mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro b hb
    simp only [div_eq_mul_inv,mul_inv]
    ring
  rw [he]
  calc
    _ ≤ ∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        ‖u a*v b*(lemma151Rho β (a*b)-lemma151Rho β a*lemma151Rho β b)/
          ((a : ℂ)*(b : ℂ))‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum fun a ha => norm_sum_le _ _)
    _ ≤ ∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        2*A*B*(if ¬a.Coprime b then
          ((lemma34Tau 2 a : ℝ)/(a : ℝ))*((lemma34Tau 2 b : ℝ)/(b : ℝ)) else 0) := by
      exact sum_le_sum fun a ha => sum_le_sum fun b hb =>
        roughCollision_weighted_defect_bound hβ u v hA hB hu hv a b
    _ = 2*A*B*(∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if a.Coprime (lemma151Q D) ∧ b.Coprime (lemma151Q D) ∧ ¬a.Coprime b
        then ((lemma34Tau 2 a : ℝ)/(a : ℝ))*((lemma34Tau 2 b : ℝ)/(b : ℝ)) else 0) := by
      simp only [roughCollisionDomain,sum_filter,mul_sum]
      apply sum_congr rfl
      intro a ha
      by_cases haQ : a.Coprime (lemma151Q D)
      · rw [if_pos haQ]
        apply sum_congr rfl
        intro b hb
        by_cases hbQ : b.Coprime (lemma151Q D)
        · rw [if_pos hbQ]
          by_cases hab : a.Coprime b
          · rw [if_neg (not_not.mpr hab),if_neg (by tauto)]
          · rw [if_pos hab,if_pos ⟨haQ,hbQ,hab⟩]
        · rw [if_neg hbQ,if_neg (by tauto),mul_zero]
      · rw [if_neg haQ]
        symm
        apply sum_eq_zero
        intro b hb
        rw [if_neg (by tauto),mul_zero]
    _ ≤ 2*A*B*(8*(harmonic X : ℝ)^4/(D^4 : ℕ)) :=
      mul_le_mul_of_nonneg_left (roughCollision_tau_mass D X hD hX) (by positivity)
    _ = _ := by ring

/-- The actual original U,V, actual beta_j(c'), and arbitrary natural kernel
shifts l1,l2 instantiate the uniform bound. All three iota factors are retained. -/
theorem roughCollision_actual_source_kernels (D X l₁ l₂ : ℕ)
    (hD : 0<D) (hX : 1≤X) (c : ℝ) (j : Fin 3) :
    ‖(∑ a ∈ roughCollisionDomain D X, ∑ b ∈ roughCollisionDomain D X,
        lemma151First D (l₁*a)*lemma151Second D (l₂*b)*
          lemma151Rho (lemma83PaperBeta D c j) (a*b)/((a : ℂ)*(b : ℂ))) -
      (∑ a ∈ roughCollisionDomain D X,
        lemma151First D (l₁*a)*lemma151Rho (lemma83PaperBeta D c j) a/(a : ℂ))*
      (∑ b ∈ roughCollisionDomain D X,
        lemma151Second D (l₂*b)*lemma151Rho (lemma83PaperBeta D c j) b/(b : ℂ))‖ ≤
      16*bCoefficientConstant*(harmonic X : ℝ)^4/(D^4 : ℕ) := by
  simpa only [bCoefficientConstant,mul_assoc] using
    roughCollision_kernel_factorization D X hD hX (lemma83_beta_re D c j)
      (fun a => lemma151First D (l₁*a)) (fun b => lemma151Second D (l₂*b))
      (by positivity : 0≤1+‖lemma151Iota2‖)
      (by positivity : 0≤‖lemma151Iota3‖+‖lemma151Iota4‖)
      (fun a => b_first_norm_bound D (l₁*a)) (fun b => b_second_norm_bound D (l₂*b))

end ZhangLS.Spec
