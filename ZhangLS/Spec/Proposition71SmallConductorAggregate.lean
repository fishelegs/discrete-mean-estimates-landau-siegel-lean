import ZhangLS.Spec.Proposition71SmallSigma
import ZhangLS.Spec.Proposition71CharacterConductorWeights

/-! # Actual small-conductor aggregate with all original weights retained

This is the l≤P² portion of the positive majorant in (7.13). It is not the
whole θ₁₂ term: conductor reduction, Gauss factors and the omitted l tail
remain separate obligations.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71SmallConductorAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (X Q : ℕ) : ℝ :=
  ∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q,
    ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖proposition71SigmaTruncated D c b a h d θ‖

/-- All character counts and φ(hr) factors have been genuinely summed.
The remaining Q^(3/2) loss is exactly what the D^(1/4) split absorbs. -/
theorem proposition71_small_conductor_aggregate_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → 1<D →
      2000≤lemma23PaperL D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ c b B : ℝ, 0≤B → |b|≤(D : ℝ)/2 →
          ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ X Q : ℕ,
            1≤X → Q<D → proposition71SmallConductorAggregate D c b a X Q≤
              C*B*lemma56PrimeMass D/(D : ℝ)*lemma23PaperL D^3245*
                (Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7 := by
  obtain ⟨C,hC,D₀,hsigma⟩ := proposition71_actual_small_sigma_bound
  refine ⟨C,hC,D₀,?_⟩
  intro D hDN hD hL χ hA c b B hB hb a ha X Q hX hQD
  let K : ℝ := C*B*lemma56PrimeMass D/(D : ℝ)*lemma23PaperL D^3245
  have hM := lemma56_prime_mass_nonneg D
  have hDp : 0<(D : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hLp : 0≤lemma23PaperL D := by linarith
  have hK : 0≤K := by dsimp [K]; positivity
  have hterm {d h r : ℕ} (hd : d∈Icc 1 X) (hh : h∈Icc 1 X) (hr : r∈Icc 2 Q) :
      ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
        (∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
          ‖proposition71SigmaTruncated D c b a h d θ‖)≤
      K*((lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
        ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by
    have hdp : 0<d := (mem_Icc.mp hd).1
    have hhp : 0<h := (mem_Icc.mp hh).1
    have hr1 : 1<r := (mem_Icc.mp hr).1
    letI : NeZero r := ⟨by omega⟩
    have hc : (((univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive)).card : ℝ)≤Nat.totient r := by
      exact_mod_cast proposition71_primitive_character_count (r := r)
    have hsig : (∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖proposition71SigmaTruncated D c b a h d θ‖)≤
          (Nat.totient r : ℝ)*(K*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)) := by
      calc
        _≤∑ _θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
            K*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ) := by
          apply sum_le_sum
          intro θ hθ
          have hv := hsigma χ θ hDN hD hL hA (mem_filter.mp hθ).2 hr1
            ((mem_Icc.mp hr).2.trans_lt hQD) c b B hB hb a ha h d hhp hdp
          convert hv using 1 <;> dsimp [K] <;> ring
        _≤_ := by
          rw [sum_const,nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hc (by positivity)
    have hφ : 0<(Nat.totient (h*r) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hhp (Nat.zero_lt_of_lt hr1))
    have hdR : 0<(d : ℝ) := by exact_mod_cast hdp
    have hhR : 0<(h : ℝ) := by exact_mod_cast hhp
    have hrR : 0<(r : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hr1
    have hsR : 0<Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
    apply (mul_le_mul_of_nonneg_left hsig (by positivity)).trans_eq
    field_simp
    rw [Real.sq_sqrt hrR.le]
    ring
  unfold proposition71SmallConductorAggregate
  calc
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q,
        K*((lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
          ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum (fun r hr => hterm hd hh hr)
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
        K*((lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
          ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr; have hr := mem_Icc.mp hr; exact mem_Icc.mpr ⟨by omega,hr.2⟩
      · intro r hr hnot; positivity
    _=K*(∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
        (lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
          ((d : ℝ)*(Nat.totient (h*r) : ℝ))) := by simp only [mul_sum]
    _≤K*((Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7) :=
      mul_le_mul_of_nonneg_left (proposition71_counted_conductor_weight_sum X Q hX) hK
    _=_ := by dsimp [K]; ring

end ZhangLS.Spec
