import ZhangLS.Spec.Lemma59RelaxedProducts

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma59_zero_line_distance {ρ σ : ℂ}
    (hρ : ρ.re = 1 / 2) (hσ : σ.re = 1 / 2) : ‖σ - ρ‖ = |σ.im - ρ.im| := by
  apply le_antisymm
  · have h := Complex.norm_le_abs_re_add_abs_im (σ - ρ)
    simpa only [Complex.sub_re,Complex.sub_im,hσ,hρ,sub_self,abs_zero,zero_add] using h
  · simpa only [Complex.sub_im] using Complex.abs_im_le_norm (σ - ρ)

lemma lemma59_zero_ordinate_injective {S : Finset ℂ}
    (hcrit : ∀ ρ ∈ S, ρ.re = 1 / 2) : Set.InjOn (fun ρ : ℂ => ρ.im) S := by
  intro ρ hρ σ hσ he
  apply Complex.ext
  · rw [hcrit ρ hρ,hcrit σ hσ]
  · exact he

lemma lemma59_neg_zero_ordinate_injective {S : Finset ℂ}
    (hcrit : ∀ ρ ∈ S, ρ.re = 1 / 2) : Set.InjOn (fun ρ : ℂ => -ρ.im) S := by
  intro ρ hρ σ hσ he
  exact lemma59_zero_ordinate_injective hcrit hρ hσ (by linarith only [he])

lemma lemma59_harmonic_le_log_succ (n : ℕ) :
    (harmonic n : ℝ) ≤ 1 + Real.log ((n : ℝ) + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  apply (harmonic_le_one_add_log n).trans
  apply add_le_add le_rfl
  apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn)
  linarith only [show 0 ≤ (n : ℝ) by positivity]

lemma lemma59_far_complex_zero_product_bound (S : Finset ℂ) {z : ℂ} {g δ ε : ℝ}
    (hg : 0 < g) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hshift : δ ≤ (1 + ε) * g)
    (hcrit : ∀ ρ ∈ S, ρ.re = 1 / 2) (hbelow : ∀ ρ ∈ S, ρ.im ≤ z.im - g)
    (hsep : ∀ ρ ∈ S, ∀ σ ∈ S, ρ ≠ σ → g ≤ ‖σ - ρ‖) :
    ‖∏ ρ ∈ S, (z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤
      ((S.card : ℝ) + 1) * Real.exp (ε * (1 + Real.log ((S.card : ℝ) + 1))) := by
  classical
  let T := S.image (fun ρ : ℂ => -ρ.im)
  have hcard : T.card = S.card := card_image_iff.mpr (lemma59_neg_zero_ordinate_injective hcrit)
  have hbase : ∀ x ∈ T, g - z.im ≤ x := by
    intro x hx
    obtain ⟨ρ,hρ,rfl⟩ := mem_image.mp hx
    linarith only [hbelow ρ hρ]
  have hgap : ∀ x ∈ T, ∀ y ∈ T, x < y → g ≤ y - x := by
    intro x hx y hy hxy
    obtain ⟨ρ,hρ,rfl⟩ := mem_image.mp hx
    obtain ⟨σ,hσ,rfl⟩ := mem_image.mp hy
    have hne : ρ ≠ σ := by intro he; subst σ; exact (lt_irrefl _) hxy
    have hd := hsep ρ hρ σ hσ hne
    rw [lemma59_zero_line_distance (hcrit ρ hρ) (hcrit σ hσ),
      abs_of_nonpos (by linarith only [hxy])] at hd
    linarith only [hd]
  have heq : (∏ x ∈ T, (z + I * (δ : ℂ) - ((1 / 2 : ℂ) - I * (x : ℂ))) /
      (z - ((1 / 2 : ℂ) - I * (x : ℂ)))) =
      ∏ ρ ∈ S, (z + I * (δ : ℂ) - ρ) / (z - ρ) := by
    rw [prod_image (lemma59_neg_zero_ordinate_injective hcrit)]
    apply prod_congr rfl
    intro ρ hρ
    have hr : (1 / 2 : ℂ) - I * ((-ρ.im : ℝ) : ℂ) = ρ := by
      apply Complex.ext <;> simp [hcrit ρ hρ]
    rw [hr]
  have hp := lemma59_sorted_real_zero_product_bound T hg hδ hε hshift hbase hgap
  rw [heq,hcard] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (lemma59_harmonic_le_log_succ S.card) hε

lemma lemma59_near_complex_zero_card_le_three {S : Finset ℂ} {g a b : ℝ}
    (hcrit : ∀ ρ ∈ S, ρ.re = 1 / 2)
    (hregion : ∀ ρ ∈ S, a < ρ.im ∧ ρ.im < b) (hwidth : b - a ≤ 3 * g)
    (hsep : ∀ ρ ∈ S, ∀ σ ∈ S, ρ ≠ σ → g ≤ ‖σ - ρ‖) : S.card ≤ 3 := by
  classical
  let T := S.image (fun ρ : ℂ => ρ.im)
  have hc : T.card = S.card := card_image_iff.mpr (lemma59_zero_ordinate_injective hcrit)
  rw [← hc]
  refine lemma59_near_real_zero_card_le_three (S := T) ?_ hwidth ?_
  · intro x hx
    obtain ⟨ρ,hρ,rfl⟩ := mem_image.mp hx
    exact hregion ρ hρ
  · intro x hx y hy hxy
    obtain ⟨ρ,hρ,rfl⟩ := mem_image.mp hx
    obtain ⟨σ,hσ,rfl⟩ := mem_image.mp hy
    have hne : ρ ≠ σ := by intro he; subst σ; exact (lt_irrefl _) hxy
    have hd := hsep ρ hρ σ hσ hne
    rw [lemma59_zero_line_distance (hcrit ρ hρ) (hcrit σ hσ),
      abs_of_nonneg (by linarith only [hxy])] at hd
    exact hd

lemma lemma59_log_succ_product_budget_mono {n N : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hn : n ≤ N) :
    ((n : ℝ) + 1) * Real.exp (ε * (1 + Real.log ((n : ℝ) + 1))) ≤
      ((N : ℝ) + 1) * Real.exp (ε * (1 + Real.log ((N : ℝ) + 1))) := by
  have hc : (n : ℝ) ≤ N := by exact_mod_cast hn
  apply mul_le_mul (by linarith only [hc]) _ (Real.exp_pos _).le (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (Real.log_le_log (by positivity) (by linarith only [hc]))) hε

lemma lemma59_separated_complex_zero_product_bound (S : Finset ℂ) {z : ℂ} {g δ ε η : ℝ}
    (hg : 0 < g) (hδ : 0 < δ) (hε : 0 ≤ ε) (hη : 0 < η)
    (hshift : δ ≤ (1 + ε) * g) (hshort : δ ≤ 2 * g)
    (hcrit : ∀ ρ ∈ S, ρ.re = 1 / 2)
    (hsep : ∀ ρ ∈ S, ∀ σ ∈ S, ρ ≠ σ → g ≤ ‖σ - ρ‖)
    (hpoint : ∀ ρ ∈ S, η * δ ≤ ‖z - ρ‖) :
    ‖∏ ρ ∈ S, (z + I * (δ : ℂ) - ρ) / (z - ρ)‖ ≤
      (((S.card : ℝ) + 1) * Real.exp (ε * (1 + Real.log ((S.card : ℝ) + 1)))) *
        (1 + η⁻¹) ^ 3 := by
  classical
  let f : ℂ → ℂ := fun ρ => (z + I * (δ : ℂ) - ρ) / (z - ρ)
  let B := S.filter (fun ρ => ρ.im ≤ z.im - g)
  let R := S.filter (fun ρ => ¬ρ.im ≤ z.im - g)
  let N := R.filter (fun ρ => ρ.im < z.im + δ)
  let A := R.filter (fun ρ => ¬ρ.im < z.im + δ)
  have hB : ‖∏ ρ ∈ B, f ρ‖ ≤
      ((S.card : ℝ) + 1) * Real.exp (ε * (1 + Real.log ((S.card : ℝ) + 1))) := by
    apply (lemma59_far_complex_zero_product_bound B hg hδ.le hε hshift
      (fun ρ hρ => hcrit ρ (mem_filter.mp hρ).1)
      (fun ρ hρ => (mem_filter.mp hρ).2)
      (fun ρ hρ σ hσ hne => hsep ρ (mem_filter.mp hρ).1 σ (mem_filter.mp hσ).1 hne)).trans
    exact lemma59_log_succ_product_budget_mono hε (card_filter_le _ _)
  have hNS (ρ : ℂ) (hρ : ρ ∈ N) : ρ ∈ S :=
    (mem_filter.mp (mem_filter.mp hρ).1).1
  have hcard : N.card ≤ 3 := by
    refine lemma59_near_complex_zero_card_le_three (S := N) (a := z.im - g) (b := z.im + δ)
      (fun ρ hρ => hcrit ρ (hNS ρ hρ)) ?_ (by linarith only [hshort])
      (fun ρ hρ σ hσ hne => hsep ρ (hNS ρ hρ) σ (hNS σ hσ) hne)
    intro ρ hρ
    exact ⟨lt_of_not_ge (mem_filter.mp (mem_filter.mp hρ).1).2,(mem_filter.mp hρ).2⟩
  have hN : ‖∏ ρ ∈ N, f ρ‖ ≤ (1 + η⁻¹) ^ 3 :=
    lemma59_exceptional_zero_product_bound_three N hδ hη hcard
      (fun ρ hρ => hpoint ρ (hNS ρ hρ))
  have hA : ‖∏ ρ ∈ A, f ρ‖ ≤ 1 := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _ρ ∈ A, (1 : ℝ) := by
        apply prod_le_prod (fun _ _ => norm_nonneg _)
        intro ρ hρ
        exact lemma59_above_zero_factor_le_one hδ.le (le_of_not_gt (mem_filter.mp hρ).2)
      _ = 1 := by simp
  have he1 : (∏ ρ ∈ S, f ρ) = (∏ ρ ∈ B, f ρ) * ∏ ρ ∈ R, f ρ :=
    (prod_filter_mul_prod_filter_not S (fun ρ => ρ.im ≤ z.im - g) f).symm
  have he2 : (∏ ρ ∈ R, f ρ) = (∏ ρ ∈ N, f ρ) * ∏ ρ ∈ A, f ρ :=
    (prod_filter_mul_prod_filter_not R (fun ρ => ρ.im < z.im + δ) f).symm
  change ‖∏ ρ ∈ S, f ρ‖ ≤ _
  rw [he1,he2,norm_mul,norm_mul]
  have hn := mul_le_mul hN hA (norm_nonneg _) (by positivity : 0 ≤ (1 + η⁻¹) ^ 3)
  simpa only [mul_one] using mul_le_mul hB hn
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)

end ZhangLS.Spec
