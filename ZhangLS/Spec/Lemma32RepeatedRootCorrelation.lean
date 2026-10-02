import ZhangLS.Spec.Lemma32ActualPrimeCorrelation
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_quadratic_repeated_root_correlation {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (a b c : F) (hbc : b ≠ c) :
    (∑ x : F, χ ((x+a)^2*(x+b)*(x+c))) = -1-χ ((b-a)*(c-a)) := by
  let f : F → ℂ := fun x => χ ((x+a)^2*(x+b)*(x+c))
  let g : F → ℂ := fun x => χ ((x+b)*(x+c))
  have hf : (∑ x : F, f x) = ∑ x ∈ Finset.univ \ {-a}, f x := by
    rw [sum_eq_sum_diff_singleton_add (mem_univ (-a)) f]
    simp [f,χ.map_zero]
  have hg : (∑ x : F, g x) = (∑ x ∈ Finset.univ \ {-a}, g x)+g (-a) :=
    sum_eq_sum_diff_singleton_add (mem_univ (-a)) g
  have he : (∑ x ∈ Finset.univ \ {-a}, f x) = ∑ x ∈ Finset.univ \ {-a}, g x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 : x+a ≠ 0 := by
      intro h
      have hn0 : x ≠ -a := by simpa only [mem_sdiff,mem_univ,mem_singleton,true_and] using hx
      exact hn0 (eq_neg_iff_add_eq_zero.mpr h)
    dsimp [f,g]
    rw [show (x+a)^2*(x+b)*(x+c) = (x+a)^2*((x+b)*(x+c)) by ring,
      map_mul,map_pow,lemma32_quadratic_character_value_square χ hq (x+a) hx0,one_mul]
  have hc : (∑ x : F, g x) = -1 := lemma32_quadratic_two_linear_correlation χ hn hq b c hbc
  have hg0 : g (-a) = χ ((b-a)*(c-a)) := by dsimp [g];congr 1;ring
  change (∑ x : F, f x) = _
  rw [hf,he]
  rw [hc,hg0] at hg
  linear_combination -hg

lemma lemma32_quadratic_repeated_root_correlation_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (a b c : F) (hbc : b ≠ c) :
    ‖∑ x : F, χ ((x+a)^2*(x+b)*(x+c))‖ ≤ 2 := by
  rw [lemma32_quadratic_repeated_root_correlation χ hn hq a b c hbc]
  calc
    _ ≤ ‖(-1 : ℂ)‖+‖χ ((b-a)*(c-a))‖ := norm_sub_le _ _
    _ ≤ 2 := by
      have h := lemma32_quadratic_character_norm_le_one χ hq ((b-a)*(c-a))
      simp only [norm_neg,norm_one]
      linarith

end ZhangLS.Spec
