import ZhangLS.Spec.Proposition71CharacterConductorWeights

/-! # Exact arithmetic summation of individual conductor-error bounds

This finite algebraic bridge retains every primitive character and φ(hr).
Its input is an individual norm bound, not an averaged cancellation estimate.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def proposition71ConductorNormAggregate (X Q : ℕ)
    (A : ℕ → ℕ → ℕ → Prop)
    (F : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ) : ℝ :=
  ∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q,
    if A d h r then
      ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
        ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F d h r θ‖
    else 0

lemma proposition71_conductor_norm_aggregate_nonneg (X Q : ℕ)
    (A : ℕ → ℕ → ℕ → Prop)
    (F : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ) :
    0≤proposition71ConductorNormAggregate X Q A F := by
  unfold proposition71ConductorNormAggregate
  apply sum_nonneg; intro d hd
  apply sum_nonneg; intro h hh
  apply sum_nonneg; intro r hr
  split
  · positivity
  · exact le_rfl

theorem proposition71_conductor_norm_aggregate_bound (X Q : ℕ) (hX : 1≤X)
    (A : ℕ → ℕ → ℕ → Prop)
    (F : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ) {K : ℝ} (hK : 0≤K)
    (hF : ∀d∈Icc 1 X, ∀h∈Icc 1 X, ∀r∈Icc 2 Q, A d h r →
      ∀ θ : DirichletCharacter ℂ r, θ.IsPrimitive →
        ‖F d h r θ‖≤K*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)) :
    proposition71ConductorNormAggregate X Q A F≤K*(Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7 := by
  have hterm {d h r : ℕ} (hd : d∈Icc 1 X) (hh : h∈Icc 1 X) (hr : r∈Icc 2 Q) :
      (if A d h r then
        ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
          ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F d h r θ‖ else 0)≤
      K*((lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
        ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by
    split_ifs with hA
    swap
    · positivity
    have hdp : 0<d := (mem_Icc.mp hd).1
    have hhp : 0<h := (mem_Icc.mp hh).1
    have hrp : 0<r := by have := (mem_Icc.mp hr).1; omega
    letI : NeZero r := ⟨by omega⟩
    have hc : (((univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive)).card : ℝ)≤Nat.totient r := by
      exact_mod_cast proposition71_primitive_character_count (r := r)
    have hs : (∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F d h r θ‖)≤
        (Nat.totient r : ℝ)*(K*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)) := by
      calc
        _≤∑ _θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
            K*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ) :=
          sum_le_sum (fun θ hθ => hF d hd h hh r hr hA θ (mem_filter.mp hθ).2)
        _≤_ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hc (by positivity)
    have hφ : 0<(Nat.totient (h*r) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hhp hrp)
    have hdR : 0<(d : ℝ) := by exact_mod_cast hdp
    have hhR : 0<(h : ℝ) := by exact_mod_cast hhp
    have hrR : 0<(r : ℝ) := by exact_mod_cast hrp
    have hsR : 0<Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
    apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq
    field_simp
    rw [Real.sq_sqrt hrR.le]
    ring
  unfold proposition71ConductorNormAggregate
  calc
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q,
        K*((lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
          ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by
      apply sum_le_sum; intro d hd
      apply sum_le_sum; intro h hh
      exact sum_le_sum (fun r hr => hterm hd hh hr)
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
        K*((lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
          ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by
      apply sum_le_sum; intro d hd
      apply sum_le_sum; intro h hh
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr; have hh := mem_Icc.mp hr; exact mem_Icc.mpr ⟨by omega,hh.2⟩
      · intro r hr hnot; positivity
    _=K*(∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
        (lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
          ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by simp only [mul_sum]
    _≤K*((Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7) :=
      mul_le_mul_of_nonneg_left (proposition71_counted_conductor_weight_sum X Q hX) hK
    _=_ := by ring

end ZhangLS.Spec
