import ZhangLS.Spec.Proposition71ConductorWeights
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Actual primitive-character counts and the exact φ(hr) conductor weight -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_primitive_character_count {r : ℕ} [NeZero r] :
    ((univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive)).card≤Nat.totient r := by
  apply (card_filter_le _ _).trans_eq
  rw [card_univ,←Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

lemma proposition71_three_halves_eq_mul_sqrt {r : ℝ} (hr : 0≤r) :
    r^(3/2 : ℝ)=r*Real.sqrt r := by
  by_cases h : r=0
  · subst r; norm_num
  rw [show (3/2 : ℝ)=1+1/2 by norm_num,Real.rpow_add (lt_of_le_of_ne hr (Ne.symm h)),
    Real.rpow_one,←Real.sqrt_eq_rpow]

/-- Counting actual primitive characters costs φ(r), which cancels against
φ(hr) up to the honest remaining factor φ(h). -/
lemma proposition71_counted_totient_weight {h r : ℕ} (hh : 0<h) (hr : 0<r) :
    (Nat.totient r : ℝ)/(Nat.totient (h*r) : ℝ)≤(Nat.totient h : ℝ)⁻¹ := by
  have hφh : 0<(Nat.totient h : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hh
  have hφhr : 0<(Nat.totient (h*r) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hh hr)
  have hb : (Nat.totient h : ℝ)*(Nat.totient r : ℝ)≤(Nat.totient (h*r) : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative h r
  rw [←one_div]
  exact (div_le_div_iff₀ hφhr hφh).mpr (by simpa only [one_mul,mul_one,mul_comm] using hb)

/-- The square-root conductor count costs no more than Q^(3/2). -/
lemma proposition71_sqrt_conductor_sum (Q : ℕ) :
    (∑ r∈Icc 1 Q, Real.sqrt (r : ℝ))≤(Q : ℝ)^(3/2 : ℝ) := by
  calc
    _≤∑ _r∈Icc 1 Q, Real.sqrt (Q : ℝ) := by
      apply sum_le_sum
      intro r hr
      exact Real.sqrt_le_sqrt (by exact_mod_cast (mem_Icc.mp hr).2)
    _=(Q : ℝ)*Real.sqrt (Q : ℝ) := by simp
    _=_ := (proposition71_three_halves_eq_mul_sqrt (Nat.cast_nonneg Q)).symm

/-- The complete actual counted conductor weight, with no discarded φ or τ
factor. This is stronger than the coarser τ₂(r)-weighted bound. -/
theorem proposition71_counted_conductor_weight_sum (X Q : ℕ) (hX : 1≤X) :
    (∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
      (lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
        ((d : ℝ)*(Nat.totient (h*r) : ℝ)))≤
      (Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7 := by
  have hterm {d h r : ℕ} (hd : d∈Icc 1 X) (hh : h∈Icc 1 X) (hr : r∈Icc 1 Q) :
      (lemma34Tau 5 d : ℝ)*Real.sqrt (r : ℝ)*(Nat.totient r : ℝ)/
        ((d : ℝ)*(Nat.totient (h*r) : ℝ))≤
      ((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ))*Real.sqrt (r : ℝ) := by
    have hb := proposition71_counted_totient_weight (mem_Icc.mp hh).1 (mem_Icc.mp hr).1
    have hh' := proposition71_reciprocal_totient_le_tau (mem_Icc.mp hh).1
    calc
      _=((lemma34Tau 5 d : ℝ)/(d : ℝ))*Real.sqrt (r : ℝ)*
          ((Nat.totient r : ℝ)/(Nat.totient (h*r) : ℝ)) := by ring
      _≤((lemma34Tau 5 d : ℝ)/(d : ℝ))*Real.sqrt (r : ℝ)*
          ((lemma34Tau 2 h : ℝ)/(h : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb.trans hh') (by positivity)
      _=_ := by ring
  calc
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 1 Q,
        ((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ))*Real.sqrt (r : ℝ) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro h hh
      exact sum_le_sum (fun r hr => hterm hd hh hr)
    _=(∑ d∈Icc 1 X, (lemma34Tau 5 d : ℝ)/(d : ℝ))*
        (∑ h∈Icc 1 X, (lemma34Tau 2 h : ℝ)/(h : ℝ))*
        (∑ r∈Icc 1 Q, Real.sqrt (r : ℝ)) := by simp only [←sum_mul,←mul_sum]
    _≤(1+Real.log (X : ℝ))^5*(1+Real.log (X : ℝ))^2*(Q : ℝ)^(3/2 : ℝ) := by
      have h5 := proposition71_tau_harmonic_bound 5 X hX
      have h2 := proposition71_tau_harmonic_bound 2 X hX
      have hq := proposition71_sqrt_conductor_sum Q
      have h50 : 0≤∑ d∈Icc 1 X, (lemma34Tau 5 d : ℝ)/(d : ℝ) := sum_nonneg (fun _ _ => by positivity)
      have h20 : 0≤∑ h∈Icc 1 X, (lemma34Tau 2 h : ℝ)/(h : ℝ) := sum_nonneg (fun _ _ => by positivity)
      have hq0 : 0≤∑ r∈Icc 1 Q, Real.sqrt (r : ℝ) := sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
      gcongr
    _=_ := by ring

end ZhangLS.Spec
