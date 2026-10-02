import ZhangLS.Spec.Proposition71SmallConductorAggregate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # A genuine power saving for the repaired D^(1/4) small-conductor split

All φ and τ losses have already been summed. This module absorbs only the
explicit remaining logarithmic powers. The final Proposition7.1 objects are
unchanged; this is an internal proof partition.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
open scoped Topology
set_option maxHeartbeats 3000000

lemma proposition71_log_power_eighth_threshold (k : ℕ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → lemma23PaperL D^k≤(D : ℝ)^(1/8 : ℝ) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := (1/8 : ℝ)) (k : ℝ)
    (by norm_num)).bound (by norm_num : (0:ℝ)<1)
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp ht
  refine ⟨D₀,?_⟩
  intro D hD
  have hh := hD₀ D hD
  simp only [Real.rpow_natCast,one_mul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) k),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg D) (1/8 : ℝ))] at hh
  exact hh

/-- The actual truncated, weighted small-conductor aggregate has a uniform
D⁻¹ᐟ² saving after the explicit quarter-power split. -/
theorem proposition71_quarter_small_conductor_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ c b B : ℝ, 0≤B → |b|≤(D : ℝ)/2 →
          ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ X Q : ℕ,
            1≤X → (X : ℝ)≤lemma23PaperP D → (Q : ℝ)≤(D : ℝ)^(1/4 : ℝ) →
              proposition71SmallConductorAggregate D c b a X Q≤
                C*B*lemma56PrimeMass D*(D : ℝ)^(-1/2 : ℝ) := by
  obtain ⟨C,hC,Dk,hkernel⟩ := proposition71_small_conductor_aggregate_bound
  obtain ⟨Da,habsorb⟩ := proposition71_log_power_eighth_threshold 3308
  refine ⟨C*2^7,by positivity,max 2 (max Dk (max Da ⌈Real.exp 2000⌉₊)),le_max_left _ _,?_⟩
  intro D hD χ hA c b B hB hb a ha X Q hX hXP hQD
  have hD2 : 2≤D := (le_max_left _ _).trans hD
  have hDk : Dk≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDa : Da≤D := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hDe : ⌈Real.exp 2000⌉₊≤D := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hL : 2000≤lemma23PaperL D := by
    have he : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hDe)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos 2000) he
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hD1 : 1<(D : ℝ) := by exact_mod_cast (show 1<D by omega)
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hM := lemma56_prime_mass_nonneg D
  have hQlt : Q<D := by
    have hlt : (D : ℝ)^(1/4 : ℝ)<D := by
      simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hD1
        (by norm_num : (1/4 : ℝ)<1)
    exact_mod_cast hQD.trans_lt hlt
  have hk := hkernel D hDk (by omega) hL χ hA c b B hB hb a ha X Q hX hQlt
  have hlog : Real.log (X : ℝ)≤lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<X) hXP
    simpa [lemma23PaperP] using hh
  have hlog0 : 0≤1+Real.log (X : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
    linarith
  have hpow : (1+Real.log (X : ℝ))^7≤2^7*lemma23PaperL D^63 := by
    have h9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL1
    have hh := pow_le_pow_left₀ hlog0 (show 1+Real.log (X : ℝ)≤2*lemma23PaperL D^9 by linarith) 7
    simpa only [mul_pow,←pow_mul] using hh
  have hQsave := proposition71_quarter_split_small_budget hDp (Nat.cast_nonneg Q) hQD
  have hlogsave := habsorb D hDa
  apply hk.trans
  calc
    _≤C*B*lemma56PrimeMass D/(D : ℝ)*lemma23PaperL D^3245*
        (Q : ℝ)^(3/2 : ℝ)*(2^7*lemma23PaperL D^63) := by gcongr
    _=(C*2^7)*B*lemma56PrimeMass D*lemma23PaperL D^3308*
        ((Q : ℝ)^(3/2 : ℝ)/(D : ℝ)) := by ring
    _≤(C*2^7)*B*lemma56PrimeMass D*lemma23PaperL D^3308*(D : ℝ)^(-5/8 : ℝ) := by gcongr
    _≤(C*2^7)*B*lemma56PrimeMass D*(D : ℝ)^(1/8 : ℝ)*(D : ℝ)^(-5/8 : ℝ) := by gcongr
    _=_ := by
      rw [mul_assoc ((C*2^7)*B*lemma56PrimeMass D),←Real.rpow_add hDp]
      norm_num

end ZhangLS.Spec
