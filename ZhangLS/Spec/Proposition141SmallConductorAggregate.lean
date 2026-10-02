import ZhangLS.Spec.Proposition141SmallConductorRow
import ZhangLS.Spec.Proposition141ConductorBudget

/-! # The actual finite-long-index small-conductor aggregate

This proves the positive conductor majorant from the actual primitive sums,
including the exact D | hr condition, the original r<D³ split, removal of the
χ-induced character, and the full D/(d h φ(hr) sqrt(r)) weight. The long cutoff
is finite and explicit; its infinite tail is not silently discarded.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

noncomputable def proposition141SmallSupportedModuli (D h:ℕ) : Finset ℕ :=
  (proposition141SmallConductorModuli D h).filter (fun r=>((r*h:ℕ):ℝ)≤lemma23PaperP D)

noncomputable def proposition141SmallPrimitiveFamily {D:ℕ}
    (χ:RealPrimitiveCharacter D) (h r:ℕ) : Finset (DirichletCharacter ℂ r) :=
  univ.filter (fun θ=>θ.IsPrimitive ∧ ∀hDN:D∣r*h,
    θ.changeLevel (r.dvd_mul_right h)≠χ.chi.changeLevel hDN)

lemma proposition141_small_supported_mem {D h r:ℕ}
    (hr:r∈proposition141SmallSupportedModuli D h) :
    1<r ∧ r<D^3 ∧ D∣r*h ∧ ((r*h:ℕ):ℝ)≤lemma23PaperP D := by
  have hr' := mem_filter.mp hr
  have hh := (mem_filter.mp hr'.1).2
  exact ⟨hh.1,hh.2.1,by simpa only [Nat.mul_comm] using hh.2.2,hr'.2⟩

noncomputable def proposition141FiniteSmallConductorAggregate {D:ℕ}
    (χ:RealPrimitiveCharacter D) (β:ℂ) (κ:ℕ→ℂ) (D₁ X:ℕ)
    (S:ℕ→ℕ→ℕ→Finset ℕ) : ℝ :=
  ∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈proposition141SmallSupportedModuli D h,
    (D:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))*
      ∑θ∈proposition141SmallPrimitiveFamily χ h r,
        ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖

/-- The exact positive supported weight has the already proved counted
budget; the congruence is dropped only in an upper bound of nonnegative terms. -/
lemma proposition141_small_supported_weight_sum (D X:ℕ) (hX:1≤X) :
    (∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈proposition141SmallSupportedModuli D h,
      (D:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) ≤
    (D:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ)*(1+Real.log (X:ℝ))^7 := by
  have ht1 : lemma34Tau 5 1=1 := (lemma34_tau_multiplicative 5).map_one
  have hb := proposition141_small_counted_weight_sum D 1 X hX
  simp only [ht1,Nat.cast_one,mul_one] at hb
  apply le_trans _ hb
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro h hh
  calc
    _ ≤ ∑r∈proposition141SmallConductorModuli D h,
      (D:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _=>by positivity)
    _ = _ := by simp only [Nat.mul_comm]

/-- Complete finite-long small-conductor aggregate proved from the actual
nonprincipal 5.6/Mellin chain. The constants and threshold are uniform in
κ*, β, both finite cutoffs and all permitted positive-index restrictions. -/
theorem proposition141_uniform_finite_small_conductor_aggregate :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),
      D₀≤D → NormalizedAssumptionA χ → ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
      ∀B:ℝ,0≤B → ∀κ:ℕ→ℂ,Proposition141KappaBound B κ → ∀D₁ X Y:ℕ,
      0<D₁ → 1≤X → 1≤Y → ∀S:ℕ→ℕ→ℕ→Finset ℕ,
      (∀d∈Icc 1 X,∀h∈Icc 1 X,∀r∈proposition141SmallSupportedModuli D h,S d h r⊆Icc 1 Y) →
      proposition141FiniteSmallConductorAggregate χ β κ D₁ X S ≤
        C*B*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
          (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*
          ((D:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ))*(1+Real.log (Y:ℝ))^5*(1+Real.log (X:ℝ))^7 := by
  obtain ⟨C,hC,D₀,hD₀,hrow⟩ := proposition141_uniform_small_conductor_row_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D χ hlarge hA β hβ B hB κ hκ D₁ X Y hD₁ hX hY S hS
  let K := C*B*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
    (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*(1+Real.log (Y:ℝ))^5
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hlog : 0≤1+Real.log (Y:ℝ) := by
    have hy := Real.log_nonneg (by exact_mod_cast hY : (1:ℝ)≤Y)
    linarith
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (d:ℕ) (hd:d∈Icc 1 X) (h:ℕ) (hh:h∈Icc 1 X)
      (r:ℕ) (hr:r∈proposition141SmallSupportedModuli D h) :
      (D:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))*
        (∑θ∈proposition141SmallPrimitiveFamily χ h r,
          ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h (S d h r)‖) ≤
      K*((D:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) := by
    have hrs := proposition141_small_supported_mem hr
    letI : NeZero r := ⟨by omega⟩
    letI : NeZero h := ⟨by have := (mem_Icc.mp hh).1; omega⟩
    apply hrow χ hrs.2.2.1 hlarge hA hrs.2.2.2 hrs.1 hrs.2.1
      (proposition141SmallPrimitiveFamily χ h r) ?_ β hβ B hB κ hκ D₁ d Y hD₁
      (mem_Icc.mp hd).1 hY (S d h r) (hS d hd h hh r hr)
    intro θ hθ
    have hp := (mem_filter.mp hθ).2
    exact ⟨hp.1,hp.2 hrs.2.2.1⟩
  unfold proposition141FiniteSmallConductorAggregate
  calc
    _ ≤ ∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈proposition141SmallSupportedModuli D h,
      K*((D:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum (fun r hr=>hpoint d hd h hh r hr)
    _ = K*(∑d∈Icc 1 X, ∑h∈Icc 1 X, ∑r∈proposition141SmallSupportedModuli D h,
      (D:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) := by simp only [mul_sum]
    _ ≤ K*((D:ℝ)*((D^3:ℕ):ℝ)^(3/2:ℝ)*(1+Real.log (X:ℝ))^7) :=
      mul_le_mul_of_nonneg_left (proposition141_small_supported_weight_sum D X hX) hK
    _ = _ := by dsimp [K]; ring

end ZhangLS.Spec
