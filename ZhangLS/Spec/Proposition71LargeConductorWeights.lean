import ZhangLS.Spec.Proposition71LocalizedDyadicSaving

/-! # Original conductor weights attached to the genuine localized dyadic mean

The denominator φ(hr), including common prime factors, is retained. The
r/φ(r) weight from the proved sieve absorbs it by totient supermultiplicativity.
No character count or divisor factor is hidden in an implicit constant.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_large_conductor_weight {d h r : ℕ} {R : ℝ}
    (hd : 0<d) (hh : 0<h) (hr : 0<r) (hR : 0<R) (hRr : R≤(r : ℝ)) :
    ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹≤
      ((d : ℝ)*(h : ℝ)*(Nat.totient h : ℝ))⁻¹*
        ((r : ℝ)/(Nat.totient r : ℝ))/R^(3/2 : ℝ) := by
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have hhR : 0<(h : ℝ) := by exact_mod_cast hh
  have hrR : 0<(r : ℝ) := by exact_mod_cast hr
  have hφh : 0<(Nat.totient h : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hh
  have hφr : 0<(Nat.totient r : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr
  have hφhr : 0<(Nat.totient (h*r) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hh hr)
  have hs : 0<Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hφ : (Nat.totient h : ℝ)*(Nat.totient r : ℝ)≤(Nat.totient (h*r) : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative h r
  calc
    _≤((d : ℝ)*(h : ℝ)*((Nat.totient h : ℝ)*(Nat.totient r : ℝ))*Real.sqrt (r : ℝ))⁻¹ := by
      apply inv_anti₀ (by positivity)
      gcongr
    _=((d : ℝ)*(h : ℝ)*(Nat.totient h : ℝ))⁻¹*
        ((r : ℝ)/(Nat.totient r : ℝ))/(r : ℝ)^(3/2 : ℝ) := by
      rw [proposition71_three_halves_eq_mul_sqrt hrR.le]
      field_simp
    _≤_ := by
      apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hR _)
      exact Real.rpow_le_rpow hR.le hRr (by norm_num)

noncomputable def proposition71LocalizedConductorBlock (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) : ℝ :=
  ∑ r∈primitiveDyadicModuli R,
    ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖proposition71SigmaStar D c b a R h d θ‖

lemma proposition71_localized_conductor_block_nonneg (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) :
    0≤proposition71LocalizedConductorBlock D c b a R h d := by
  unfold proposition71LocalizedConductorBlock
  exact sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sum_nonneg (fun _ _ => norm_nonneg _)))

lemma proposition71_localized_conductor_block_le_mean (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) {R : ℝ} (hR : 0<R) {h d : ℕ} (hh : 0<h) (hd : 0<d) :
    proposition71LocalizedConductorBlock D c b a R h d≤
      ((d : ℝ)*(h : ℝ)*(Nat.totient h : ℝ))⁻¹*
        (proposition71LocalizedDyadicMean D c b a R h d/R^(3/2 : ℝ)) := by
  rw [proposition71_localized_dyadic_mean_expanded]
  unfold proposition71LocalizedConductorBlock
  calc
    _≤∑ r∈primitiveDyadicModuli R,
        (((d : ℝ)*(h : ℝ)*(Nat.totient h : ℝ))⁻¹*
          ((r : ℝ)/(Nat.totient r : ℝ))/R^(3/2 : ℝ))*
            ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
              ‖proposition71SigmaStar D c b a R h d θ‖ := by
      apply sum_le_sum
      intro r hr
      have hr' := mem_primitiveDyadicModuli.mp hr
      exact mul_le_mul_of_nonneg_right
        (proposition71_large_conductor_weight hd hh (by omega) hR hr'.2.1)
        (sum_nonneg (fun _ _ => norm_nonneg _))
    _=_ := by
      simp only [div_eq_mul_inv, mul_assoc]
      rw [←mul_sum, sum_mul]
      congr 1
      apply sum_congr rfl
      intro r hr
      ring

/-- The full original d,h weight remains explicit in this actual one-block
bound. In particular the τ₅(d) factor has not been dropped. -/
theorem proposition71_localized_conductor_block_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
        ∀ R : ℝ, (D : ℝ)^(1/4 : ℝ)≤R → ∀ d h : ℕ,
          0<d → 0<h → ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D →
            proposition71LocalizedConductorBlock D c b a R h d≤
              C*B*lemma23PaperP D^2*(D : ℝ)^(-1/16 : ℝ)*
                ((lemma34Tau 5 d : ℝ)/(d : ℝ))*((Nat.totient h : ℝ)⁻¹) := by
  obtain ⟨C,hC,D₀,hD₀,hm⟩ := proposition71_actual_localized_dyadic_power_saving
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D hD c b B hB a ha R hR d h hd hh hcut
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp := (Real.rpow_pos_of_pos hDp (1/4 : ℝ)).trans_le hR
  have hs := hm D hD c b B hB a ha R hR d h hd hh hcut
  apply (proposition71_localized_conductor_block_le_mean D c b a hRp hh hd).trans
  apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have hhR : 0<(h : ℝ) := by exact_mod_cast hh
  field_simp

end ZhangLS.Spec
