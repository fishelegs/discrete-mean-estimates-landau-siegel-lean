import ZhangLS.Spec.Proposition71OffLocalTail
import ZhangLS.Spec.Proposition71ConductorAggregateAlgebra
import ZhangLS.Spec.Proposition71DyadicCover
import ZhangLS.Spec.Proposition71TailScalarBudget

/-! # All genuine outer weights of the literal localization error

The original strict d h r<PT⁻² condition and the true dyadic modulus filter
are retained. The final bound includes every character, conductor, d,h and
dyadic block. No tail is absorbed before its actual outer weights are summed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71OffLocalConductorAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (X Q : ℕ) : ℝ :=
  proposition71ConductorNormAggregate X Q
    (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D ∧ r∈primitiveDyadicModuli R)
    (fun d h _ θ => proposition71SigmaOffLocalTail D c b a R h d θ)

lemma proposition71_hr_le_cutoff_of_dhr {D d h r : ℕ} (hd : 0<d)
    (hcut : ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D) :
    ((h*r : ℕ) : ℝ)≤lemma81Cutoff D := by
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hh := mul_le_mul_of_nonneg_right hd1 (by positivity : (0:ℝ)≤(h : ℝ)*(r : ℝ))
  have he : ((h*r : ℕ) : ℝ)≤((d*h*r : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul,one_mul,mul_assoc] using hh
  exact he.trans hcut.le

theorem proposition71_offlocal_conductor_aggregate_bound :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 1<D → 2000≤lemma23PaperL D →
      ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
        ∀ R : ℝ, 1≤R → ∀ X Q : ℕ, 1≤X →
          proposition71OffLocalConductorAggregate D c b a R X Q≤
            proposition71OffLocalTailConstant*B*lemma56PrimeMass D*lemma23PaperP D^4*
              Real.exp (-lemma23PaperL D^10/2)*(Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7 := by
  obtain ⟨D₀,hD₀,htail⟩ := proposition71_actual_offlocal_tail_bound
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hD hL c b B hB a ha R hR X Q hX
  have hC := proposition71_offlocal_tail_constant_pos
  have hM := lemma56_prime_mass_nonneg D
  apply proposition71_conductor_norm_aggregate_bound X Q hX _ _ (by positivity)
  intro d hd h hh r hr hA θ hθ
  have hs := (htail θ hDN hD hL c b B hB a ha R hR h d (mem_Icc.mp hh).1 hA.2
    (proposition71_hr_le_cutoff_of_dhr (mem_Icc.mp hd).1 hA.1)).2
  convert hs using 1 <;> ring

noncomputable def proposition71OffLocalLargeAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) : ℝ :=
  ∑ j∈range (proposition71DyadicBlockCount D),
    proposition71OffLocalConductorAggregate D c b a (proposition71DyadicScale D j)
      ⌊lemma23PaperP D⌋₊ ⌊lemma23PaperP D⌋₊

/-- The full literal localization error has a uniform actual-mass/D bound.
All polynomial and logarithmic losses are displayed before absorption. -/
theorem proposition71_offlocal_large_aggregate_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
        proposition71OffLocalLargeAggregate D c b a≤C*B*lemma56PrimeMass D/(D : ℝ) := by
  obtain ⟨Dg,hDg,hagg⟩ := proposition71_offlocal_conductor_aggregate_bound
  have hC := proposition71_offlocal_tail_constant_pos
  refine ⟨proposition71OffLocalTailConstant*2^9,by positivity,
    max Dg ⌈Real.exp 2000⌉₊,hDg.trans (le_max_left _ _),?_⟩
  intro D hDN c b B hB a ha
  have hg := (le_max_left _ _).trans hDN
  have hDe := (le_max_right _ _).trans hDN
  have hD2 : 2≤D := hDg.trans hg
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hL : 2000≤lemma23PaperL D := by
    have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hDe)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos 2000) he
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0≤lemma23PaperL D := by linarith
  have hM := lemma56_prime_mass_nonneg D
  have hP : 0≤lemma23PaperP D := (Real.exp_pos _).le
  have hP1 : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg hLp 9)
  let X := ⌊lemma23PaperP D⌋₊
  have hX : 1≤X := Nat.le_floor (by simpa only [Nat.cast_one] using hP1)
  have hXP : (X : ℝ)≤lemma23PaperP D := Nat.floor_le hP
  have hXpow : (X : ℝ)^(3/2 : ℝ)≤lemma23PaperP D^2 := by
    calc
      _≤lemma23PaperP D^(3/2 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg X) hXP (by norm_num)
      _≤lemma23PaperP D^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
      _=_ := Real.rpow_two _
  have hlog : Real.log (X : ℝ)≤lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<X) hXP
    simpa [lemma23PaperP] using hh
  have hlog0 : 0≤1+Real.log (X : ℝ) := by have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X); linarith
  have hlog7 : (1+Real.log (X : ℝ))^7≤2^7*lemma23PaperL D^63 := by
    have h9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL1
    have hh := pow_le_pow_left₀ hlog0 (show 1+Real.log (X : ℝ)≤2*lemma23PaperL D^9 by linarith) 7
    simpa only [mul_pow,←pow_mul] using hh
  have hcount := proposition71_dyadic_block_count_bound hL1
  have hR (j : ℕ) : 1≤proposition71DyadicScale D j :=
    (Real.one_le_rpow (by exact_mod_cast (show 1≤D by omega)) (by norm_num : (0:ℝ)≤1/4)).trans
      (proposition71_dyadic_scale_lower D j)
  unfold proposition71OffLocalLargeAggregate
  calc
    _≤∑ _j∈range (proposition71DyadicBlockCount D),
        proposition71OffLocalTailConstant*B*lemma56PrimeMass D*lemma23PaperP D^4*
          Real.exp (-lemma23PaperL D^10/2)*(X : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7 := by
      apply sum_le_sum; intro j hj
      exact hagg D hg (by omega) hL c b B hB a ha _ (hR j) X X hX
    _=(proposition71DyadicBlockCount D : ℝ)*(proposition71OffLocalTailConstant*B*lemma56PrimeMass D*
        lemma23PaperP D^4*Real.exp (-lemma23PaperL D^10/2)*(X : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7) := by simp
    _≤(4*lemma23PaperL D^9)*(proposition71OffLocalTailConstant*B*lemma56PrimeMass D*
        lemma23PaperP D^4*Real.exp (-lemma23PaperL D^10/2)*lemma23PaperP D^2*(2^7*lemma23PaperL D^63)) := by gcongr
    _=(proposition71OffLocalTailConstant*2^9)*B*lemma56PrimeMass D*
        (lemma23PaperP D^6*lemma23PaperL D^72*Real.exp (-lemma23PaperL D^10/2)) := by ring
    _≤(proposition71OffLocalTailConstant*2^9)*B*lemma56PrimeMass D*(D : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (proposition71_tail_scalar_budget (by omega) hL) (by positivity)
    _=_ := by ring

end ZhangLS.Spec
