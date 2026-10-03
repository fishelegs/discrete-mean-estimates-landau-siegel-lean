import ZhangLS.Spec.BCoefficientBounds
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Lemma151Basis
import Mathlib.Analysis.PSeries

/-! Elementary collision estimates for the actual Appendix B rho coefficients.
No contour shift, zero-free-region estimate, or assumption (A) is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset ArithmeticFunction Complex
open scoped Classical ArithmeticFunction.zeta

lemma roughCollision_twist_multiplicative (β : ℂ) (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) : (lemma151Twist β f).IsMultiplicative := by
  constructor
  · simp [lemma151Twist,hf.map_one]
  · intro m n hmn
    simp only [lemma151Twist, ArithmeticFunction.coe_mk, hf.map_mul_of_coprime hmn,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring

/-- The genuine rho is multiplicative only on coprime arguments. -/
theorem roughCollision_rho_multiplicative (β : ℂ) :
    (lemma151Rho β).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (roughCollision_twist_multiplicative β _ ArithmeticFunction.isMultiplicative_moebius.intCast)

lemma roughCollision_rho_tau_bound {β : ℂ} (hβ : β.re=0) (n : ℕ) :
    ‖lemma151Rho β n‖ ≤ (lemma34Tau 2 n : ℝ) := by
  rw [lemma34_tau2_eq_divisor_card]
  exact lemma151_rho_norm_le_tau hβ n

/-- An explicit bound for the nonmultiplicative defect, with no coprimality assumed. -/
theorem roughCollision_rho_defect {β : ℂ} (hβ : β.re=0) (a b : ℕ) :
    ‖lemma151Rho β (a*b)-lemma151Rho β a*lemma151Rho β b‖ ≤
      2*(lemma34Tau 2 a : ℝ)*(lemma34Tau 2 b : ℝ) := by
  have ht : (lemma34Tau 2 (a*b) : ℝ) ≤
      (lemma34Tau 2 a : ℝ)*(lemma34Tau 2 b : ℝ) := by
    exact_mod_cast proposition71_tau_submultiplicative 2 a b
  calc
    _ ≤ ‖lemma151Rho β (a*b)‖+‖lemma151Rho β a*lemma151Rho β b‖ := norm_sub_le _ _
    _ ≤ (lemma34Tau 2 a : ℝ)*(lemma34Tau 2 b : ℝ)+
        (lemma34Tau 2 a : ℝ)*(lemma34Tau 2 b : ℝ) := by
      rw [norm_mul]
      exact add_le_add ((roughCollision_rho_tau_bound hβ _).trans ht)
        (mul_le_mul (roughCollision_rho_tau_bound hβ a) (roughCollision_rho_tau_bound hβ b)
          (norm_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by ring

/-- Every common prime of a rough integer lies on the closed D^4 boundary or above.
The source Q excludes q<D^4 strictly, so changing this to q>D^4 is not justified. -/
theorem roughCollision_common_prime_lower {D a p : ℕ}
    (ha : a.Coprime (lemma151Q D)) (hp : p.Prime) (hpa : p∣a) : D^4≤p := by
  by_contra h
  have hpQ := lemma151_prime_dvd_Q (D := D) hp (by omega)
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes ha hpa hpQ)

/-- Positive multiples of p up to X embed into p times the full positive interval. -/
lemma roughCollision_multiple_subset {p X : ℕ} (hp : 0<p) :
    (Icc 1 X).filter (fun a => p∣a) ⊆ (Icc 1 X).image (fun m => p*m) := by
  intro a ha
  rcases mem_filter.mp ha with ⟨ha,hpa⟩
  have ha0 : 0<a := by have := (mem_Icc.mp ha).1; omega
  refine mem_image.mpr ⟨a/p,mem_Icc.mpr ⟨?_,?_⟩,Nat.mul_div_cancel' hpa⟩
  · exact Nat.div_pos (Nat.le_of_dvd ha0 hpa) hp
  · exact (Nat.div_le_self _ _).trans (mem_Icc.mp ha).2

/-- Weighted multiples retain the exact factor tau_2(p)/p. -/
theorem roughCollision_multiple_harmonic_bound {p X : ℕ} (hp : 0<p) (hX : 1≤X) :
    (∑ a ∈ (Icc 1 X).filter (fun a => p∣a), (lemma34Tau 2 a : ℝ)/(a : ℝ)) ≤
      (lemma34Tau 2 p : ℝ)/(p : ℝ)*(harmonic X : ℝ)^2 := by
  have hinj : Set.InjOn (fun m : ℕ => p*m) (Icc 1 X) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp hab
  calc
    _ ≤ ∑ a ∈ (Icc 1 X).image (fun m => p*m), (lemma34Tau 2 a : ℝ)/(a : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (roughCollision_multiple_subset hp) (by intros; positivity)
    _ = ∑ m ∈ Icc 1 X, (lemma34Tau 2 (p*m) : ℝ)/(p*m : ℕ) := by rw [sum_image hinj]
    _ ≤ ∑ m ∈ Icc 1 X, ((lemma34Tau 2 p : ℝ)/(p : ℝ))*
        ((lemma34Tau 2 m : ℝ)/(m : ℝ)) := by
      apply sum_le_sum
      intro m hm
      have ht : (lemma34Tau 2 (p*m) : ℝ) ≤
          (lemma34Tau 2 p : ℝ)*(lemma34Tau 2 m : ℝ) := by
        exact_mod_cast proposition71_tau_submultiplicative 2 p m
      rw [Nat.cast_mul]
      calc
        _ ≤ ((lemma34Tau 2 p : ℝ)*(lemma34Tau 2 m : ℝ))/((p : ℝ)*(m : ℝ)) :=
          div_le_div_of_nonneg_right ht (by positivity)
        _ = _ := by ring
    _ = (lemma34Tau 2 p : ℝ)/(p : ℝ)*
        (∑ m ∈ Icc 1 X, (lemma34Tau 2 m : ℝ)/(m : ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [div_eq_mul_inv] using lemma34_tau_weighted_sum_le_harmonic_pow 2 X hX)
      (by positivity)

lemma roughCollision_tau_prime {p : ℕ} (hp : p.Prime) : lemma34Tau 2 p=2 := by
  rw [lemma34_tau2_eq_divisor_card,hp.divisors]
  simp [hp.ne_one.symm]

/-- The prime specialization has no D-dependent hidden constant. -/
theorem roughCollision_prime_multiple_bound {p X : ℕ} (hp : p.Prime) (hX : 1≤X) :
    (∑ a ∈ (Icc 1 X).filter (fun a => p∣a), (lemma34Tau 2 a : ℝ)/(a : ℝ)) ≤
      2/(p : ℝ)*(harmonic X : ℝ)^2 := by
  simpa only [roughCollision_tau_prime hp,Nat.cast_ofNat] using
    roughCollision_multiple_harmonic_bound hp.pos hX

end ZhangLS.Spec
