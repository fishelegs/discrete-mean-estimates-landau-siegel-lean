import ZhangLS.Spec.Proposition141PrimitiveSmallSum
import ZhangLS.Spec.Proposition71CharacterConductorWeights

/-! # The actual counted small-conductor row in (14.8)

The primitive family is an actual finite subfamily after removal of the
χ-induced branch; r>1 has already removed principal characters. Its norm
estimate is proved from the actual primitive sum and then counted by φ(r).
The full D/(d h φ(hr) sqrt(r)) weight is kept through this calculation.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

lemma proposition141_primitive_subfamily_card {r:ℕ} [NeZero r]
    (F:Finset (DirichletCharacter ℂ r)) (hF:∀θ∈F,θ.IsPrimitive) : F.card≤r.totient := by
  apply (card_le_card (show F⊆(univ:Finset (DirichletCharacter ℂ r)).filter (fun θ=>θ.IsPrimitive) from
    fun θ hθ=>mem_filter.mpr ⟨mem_univ _,hF θ hθ⟩)).trans
  exact proposition71_primitive_character_count

/-- Exact scalar identity explaining the cancellation of h and one power
of r. No totient or divisor weight is absorbed into a hidden constant. -/
lemma proposition141_counted_row_scalar {D d h r K T F φ:ℝ}
    (hd:0<d) (hh:0<h) (hφ:0<φ) :
    D/(d*h*φ*Real.sqrt r)*(F*(K*T*(h*r))) =
      K*(D*T*Real.sqrt r*F/(d*φ)) := by
  calc
    _ = K*(D*T*F/(d*φ))*(r/Real.sqrt r) := by field_simp
    _ = _ := by rw [Real.div_sqrt]; ring

/-- The actual finite-l small-conductor row, summed over any genuine
primitive subfamily satisfying the χ-induced exclusion. -/
theorem proposition141_uniform_small_conductor_row_bound :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧
      ∀{D r h:ℕ} [NeZero r] [NeZero h] (χ:RealPrimitiveCharacter D)
      (hDN:D∣r*h),D₀≤D → NormalizedAssumptionA χ →
      ((r*h:ℕ):ℝ)≤lemma23PaperP D → 1<r → r<D^3 →
      ∀F:Finset (DirichletCharacter ℂ r),
      (∀θ∈F,θ.IsPrimitive ∧ θ.changeLevel (r.dvd_mul_right h)≠χ.chi.changeLevel hDN) →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀B:ℝ,0≤B →
      ∀κ:ℕ→ℂ,Proposition141KappaBound B κ → ∀D₁ d X:ℕ,
      0<D₁ → 0<d → 1≤X → ∀S:Finset ℕ,S⊆Icc 1 X →
      (D:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ))*
        (∑θ∈F,‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S‖) ≤
      (C*B*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
        (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*(1+Real.log (X:ℝ))^5)*
      ((D:ℝ)*(lemma34Tau 5 d:ℝ)*Real.sqrt (r:ℝ)*(r.totient:ℝ)/
        ((d:ℝ)*((r*h).totient:ℝ))) := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_primitive_small_character_sum_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D r h _ _ χ hDN hlarge hA hNP hr hrD F hF β hβ B hB κ hκ D₁ d X hD₁ hd hX S hS
  let K := C*B*(lemma34Tau 5 D₁:ℝ)*lemma23PaperL D^7200*lemma56PrimeMass D*
    (lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*(1+Real.log (X:ℝ))^5
  have hM := lemma56_prime_mass_nonneg D
  have hdec := (lemma56_decay_pos D).le
  have hlog : 0≤1+Real.log (X:ℝ) := by
    have hx := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
    linarith
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (θ:DirichletCharacter ℂ r) (hθ:θ∈F) :
      ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S‖ ≤
        K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ)) := by
    have hb := hbound χ hDN θ hlarge hA hNP (hF θ hθ).1 hr hrD (hF θ hθ).2
      β hβ B hB κ hκ D₁ d X hD₁ hd hX S hS
    convert hb using 1 <;> dsimp [K] <;> ring
  have hcard : (F.card:ℝ)≤(r.totient:ℝ) := by
    exact_mod_cast proposition141_primitive_subfamily_card F (fun θ hθ=>(hF θ hθ).1)
  have hsum : (∑θ∈F,‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S‖) ≤
      (r.totient:ℝ)*(K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ))) := by
    calc
      _ ≤ ∑θ∈F,K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ)) := sum_le_sum hpoint
      _ = (F.card:ℝ)*(K*(lemma34Tau 5 d:ℝ)*((h:ℝ)*(r:ℝ))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hw : 0≤(D:ℝ)/((d:ℝ)*(h:ℝ)*((r*h).totient:ℝ)*Real.sqrt (r:ℝ)) := by positivity
  have hb := mul_le_mul_of_nonneg_left hsum hw
  apply hb.trans_eq
  exact proposition141_counted_row_scalar (by exact_mod_cast hd)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne h))
    (by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (by omega : 0<r) (Nat.pos_of_ne_zero (NeZero.ne h))))

end ZhangLS.Spec
