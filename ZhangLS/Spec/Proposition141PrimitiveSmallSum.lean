import ZhangLS.Spec.Proposition141SmallCoefficientSum
import ZhangLS.Spec.InducedGaussFiniteSums

/-! # Actual primitive-conductor attachment for the small-r character sum

Changing level is proved pointwise, including nonunits. The factor (l,h)=1
is the literal one produced by induction, and prime units follow from the
actual window and hr≤P. Both removed characters remain explicit before 5.6.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical ComplexConjugate

noncomputable def proposition141PrimitiveFiniteCharacterSum {D r : ℕ}
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d h : ℕ) (S : Finset ℕ) : ℂ :=
  ∑l∈S.filter (fun l => l.Coprime h), κ (D₁*d*l)*θ (l:ZMod r)*
    proposition141ActualShiftedPrimeKernel χ θ β (h:ℝ) (r:ℝ) (l:ℝ)

/-- The true family primes are units for the extra induction factor. -/
lemma proposition141_prime_coprime_extra_factor {D r h p : ℕ}
    (hr : 0<r) (hh : 0<h) (hNP : ((r*h:ℕ):ℝ)≤lemma23PaperP D)
    (hp : p∈lemma56PaperPrimes D) : p.Coprime h := by
  have hp' := (lemma56_mem_paper_primes D p).mp hp
  have hhN : h≤r*h := by nlinarith
  have hhp : h<p := by
    have hhR : (h:ℝ)≤((r*h:ℕ):ℝ) := by exact_mod_cast hhN
    exact_mod_cast (hhR.trans hNP).trans_lt hp'.2.1
  apply hp'.1.coprime_iff_not_dvd.mpr
  intro hdvd
  exact (not_le_of_gt hhp) (Nat.le_of_dvd hh hdvd)

/-- Exact induction transformation for the finite long sum. The nonunit
l branches vanish rather than being silently identified with primitive values. -/
theorem proposition141_primitive_lifted_finite_sum {D r h : ℕ} [NeZero r] [NeZero h]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r) (β : ℂ)
    (κ : ℕ→ℂ) (D₁ d : ℕ) (S : Finset ℕ)
    (hNP : ((r*h:ℕ):ℝ)≤lemma23PaperP D) :
    proposition141FiniteSmallCharacterSum χ (θ.changeLevel (r.dvd_mul_right h)) β κ D₁ d h r S =
      proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S := by
  have hpunit (p : ℕ) (hp : p∈lemma56PaperPrimes D) : p.Coprime h :=
    proposition141_prime_coprime_extra_factor (Nat.pos_of_ne_zero (NeZero.ne r))
      (Nat.pos_of_ne_zero (NeZero.ne h)) hNP hp
  have hk (l : ℝ) :
      proposition141ActualShiftedPrimeKernel χ (θ.changeLevel (r.dvd_mul_right h)) β h r l=
      proposition141ActualShiftedPrimeKernel χ θ β h r l := by
    unfold proposition141ActualShiftedPrimeKernel
    apply sum_congr rfl
    intro p hp
    rw [inducedGauss_changeLevel_nat θ p,if_pos (hpunit p hp)]
  unfold proposition141FiniteSmallCharacterSum proposition141PrimitiveFiniteCharacterSum
  rw [sum_filter]
  apply sum_congr rfl
  intro l hl
  rw [inducedGauss_changeLevel_nat θ l,hk]
  by_cases hc : l.Coprime h <;> simp [hc]

/-- Primitivity and r>1 exclude the principal lifted character through its
actual conductor; the χ-induced exclusion remains separately explicit. -/
lemma proposition141_primitive_lift_nonprincipal {r h : ℕ} [NeZero r] [NeZero h]
    (θ : DirichletCharacter ℂ r) (hθ : θ.IsPrimitive) (hr : 1<r) :
    θ.changeLevel (r.dvd_mul_right h)≠1 := by
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  intro he
  have hc := congrArg DirichletCharacter.conductor he
  rw [lemma44_conductor_changeLevel θ,show θ.conductor=r from hθ,DirichletCharacter.conductor_one] at hc
  omega

/-- The small-conductor bound now applies to the actual primitive θ sum
with its induced (l,h)=1 filter. No extra averaged estimate is assumed. -/
theorem proposition141_uniform_primitive_small_character_sum_bound :
    ∃C:ℝ,0<C ∧ ∃D₀:ℕ,2≤D₀ ∧
      ∀{D r h:ℕ} [NeZero r] [NeZero h] (χ:RealPrimitiveCharacter D)
      (hDN:D∣r*h) (θ:DirichletCharacter ℂ r),
      D₀≤D → NormalizedAssumptionA χ → ((r*h:ℕ):ℝ)≤lemma23PaperP D →
      θ.IsPrimitive → 1<r → r<D^3 →
      θ.changeLevel (r.dvd_mul_right h)≠χ.chi.changeLevel hDN →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀B:ℝ,0≤B →
      ∀κ:ℕ→ℂ,Proposition141KappaBound B κ → ∀D₁ d X:ℕ,
      0<D₁ → 0<d → 1≤X → ∀S:Finset ℕ,S⊆Icc 1 X →
      ‖proposition141PrimitiveFiniteCharacterSum χ θ β κ D₁ d h S‖ ≤
        C*B*(lemma34Tau 5 D₁:ℝ)*(lemma34Tau 5 d:ℝ)*lemma23PaperL D^7200*
          ((h:ℝ)*(r:ℝ))*lemma56PrimeMass D*(lemma56Decay D+(D:ℝ)^(-(7:ℤ)))*
            (1+Real.log (X:ℝ))^5 := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_uniform_finite_small_character_sum_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D r h _ _ χ hDN θ hlarge hA hNP hprim hr hrD hχ β hβ B hB κ hκ D₁ d X hD₁ hd hX S hS
  letI : NeZero (r*h) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne h)⟩
  have hn := proposition141_primitive_lift_nonprincipal (h:=h) θ hprim hr
  have hc : (θ.changeLevel (r.dvd_mul_right h)).conductor<D^3 := by
    rw [lemma44_conductor_changeLevel θ,show θ.conductor=r from hprim]
    exact hrD
  have hb := hbound χ hDN (θ.changeLevel (r.dvd_mul_right h)) hlarge hA hNP hn hχ hc
    β hβ B hB κ hκ D₁ d X hD₁ hd hX (h:ℝ) (r:ℝ)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne h))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)) S hS
  rwa [proposition141_primitive_lifted_finite_sum χ θ β κ D₁ d S hNP] at hb

end ZhangLS.Spec
