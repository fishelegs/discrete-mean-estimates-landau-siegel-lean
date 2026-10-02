import ZhangLS.Spec.Proposition71Phase
import ZhangLS.Spec.Proposition71Objects

/-! # The actual phase error, summed at the original E scale

The fixed shift constant is absorbed by a D-threshold. This verifies a
quantitative part of the passage from (7.6),(7.9) to (7.10),(7.11), without
assuming either of those averaged analytic estimates.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_prime_windows_equal (D : ℕ) :
    lemma33PrimeWindow D = lemma56PaperPrimes D := by
  ext p
  rw [lemma33_mem_prime_window,lemma56_mem_paper_primes]
  rfl

lemma proposition71_actual_prime_masses_equal (D : ℕ) :
    lemma33ActualPrimeMass D = lemma56PrimeMass D := by
  unfold lemma33ActualPrimeMass lemma56PrimeMass lemma33PrimeIndex
  rw [←Finset.sum_subtype (lemma33PrimeWindow D) (fun _ => Iff.rfl) (fun p => (p : ℝ)),
    proposition71_prime_windows_equal]

lemma proposition71_weighted_three_norm (S : Fin 3 → ℂ) :
    ‖(1/2 : ℂ)*S 0+2*S 1+(3/2 : ℂ)*S 2‖ ≤ 2*∑ j : Fin 3, ‖S j‖ := by
  have h := norm_add_le ((1/2 : ℂ)*S 0+2*S 1) ((3/2 : ℂ)*S 2)
  have h' := norm_add_le ((1/2 : ℂ)*S 0) (2*S 1)
  simp only [norm_mul] at h h'
  norm_num at h h'
  rw [Fin.sum_univ_three]
  nlinarith [norm_nonneg (S 0),norm_nonneg (S 1),norm_nonneg (S 2)]

/-- At sufficiently large D (uniformly in the prime), multiplication by the
main α⁻¹ factor and summation over the genuine prime mass costs only ℒ². -/
theorem proposition71_summed_phase_budget {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ z : ℂ,
      ‖∑ p : lemma33PrimeIndex D,
        (((((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)+1)*
          (p.val : ℂ)*(lemma44PaperAlpha D : ℂ)⁻¹*z‖ ≤
        lemma33ActualPrimeMass D*lemma23PaperL D^2*‖z‖ := by
  obtain ⟨D₀,hD₀⟩ := proposition71_uniform_phase_budget hc
  refine ⟨D₀,?_⟩
  intro D hD z
  have hh := hD₀ D hD
  have ha := (lemma44_alpha_pos_le_one hh.1).1
  have hterm (p : lemma33PrimeIndex D) :
      ‖(((((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)+1)*
          (p.val : ℂ)*(lemma44PaperAlpha D : ℂ)⁻¹*z‖ ≤
        (p.val : ℝ)*lemma23PaperL D^2*‖z‖ := by
    have hp : p.val ∈ lemma56PaperPrimes D := by
      rw [←proposition71_prime_windows_equal]; exact p.property
    have hb := hh.2 p.val hp
    rw [norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ha,Complex.norm_natCast]
    calc
      _ ≤ (lemma44PaperAlpha D*lemma23PaperL D^2)*(p.val : ℝ)*
          (lemma44PaperAlpha D)⁻¹*‖z‖ := by gcongr
      _ = _ := by field_simp
  calc
    _ ≤ ∑ p : lemma33PrimeIndex D, ‖(((((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^
      lemma52PaperBetaThree D c)+1)*(p.val : ℂ)*(lemma44PaperAlpha D : ℂ)⁻¹*z‖ := norm_sum_le _ _
    _ ≤ ∑ p : lemma33PrimeIndex D, (p.val : ℝ)*lemma23PaperL D^2*‖z‖ := sum_le_sum (fun p _ => hterm p)
    _ = _ := by rw [←sum_mul,←sum_mul]; rfl

/-- The exact three S_j values fit the originally displayed E, with absolute
constant 2 and a threshold depending only on the fixed shift constant. -/
theorem proposition71_actual_arithmetic_phase_budget {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ a₁ a₂ : ℕ → ℂ,
      ‖∑ p : lemma33PrimeIndex D,
        (((((p.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)+1)*
          (p.val : ℂ)*(lemma44PaperAlpha D : ℂ)⁻¹*
            ((1/2 : ℂ)*proposition71ArithmeticSum D c 0 a₁ a₂+
              2*proposition71ArithmeticSum D c 1 a₁ a₂+
              (3/2 : ℂ)*proposition71ArithmeticSum D c 2 a₁ a₂)‖ ≤
        2*proposition71ErrorScale D c a₁ a₂ := by
  obtain ⟨D₀,h⟩ := proposition71_summed_phase_budget hc
  refine ⟨D₀,?_⟩
  intro D hD a₁ a₂
  apply (h D hD _).trans
  have hb := proposition71_weighted_three_norm (fun j => proposition71ArithmeticSum D c j a₁ a₂)
  have hm : 0 ≤ lemma33ActualPrimeMass D := by
    unfold lemma33ActualPrimeMass
    exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hb
    (mul_nonneg hm (sq_nonneg (lemma23PaperL D)))
  simpa only [proposition71ErrorScale] using (show
    lemma33ActualPrimeMass D*lemma23PaperL D^2*
      ‖(1/2 : ℂ)*proposition71ArithmeticSum D c 0 a₁ a₂+
        2*proposition71ArithmeticSum D c 1 a₁ a₂+
        (3/2 : ℂ)*proposition71ArithmeticSum D c 2 a₁ a₂‖ ≤
    2*(lemma33ActualPrimeMass D*lemma23PaperL D^2*
      ∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a₁ a₂‖) from by nlinarith only [hh])

end ZhangLS.Spec
