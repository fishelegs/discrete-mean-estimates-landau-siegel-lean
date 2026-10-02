import ZhangLS.Spec.Proposition71LargeConductorAggregate
import ZhangLS.Spec.Proposition71DyadicCover

/-! # All localized large-conductor blocks, with the original prime mass

The dyadic count, both outer arithmetic sums, and normalization by the actual
prime mass under (A) are proved here. The difference between σ and σ* remains
a separate localization/tail obligation; no estimate for that difference is
assumed in this module.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma proposition71_log_power_rpow_threshold (k : ℕ) {s : ℝ} (hs : 0<s) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → lemma23PaperL D^k≤(D : ℝ)^s := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := s) (k : ℝ) hs).bound (by norm_num : (0:ℝ)<1)
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp ht
  refine ⟨D₀,?_⟩
  intro D hD
  have hh := hD₀ D hD
  simp only [Real.rpow_natCast,one_mul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg D) k),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg D) s)] at hh
  exact hh

noncomputable def proposition71LocalizedLargeAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (X : ℕ) : ℝ :=
  ∑ j∈range (proposition71DyadicBlockCount D),
    proposition71LocalizedDyadicAggregate D c b a (proposition71DyadicScale D j) X

lemma proposition71_localized_large_aggregate_nonneg (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (X : ℕ) : 0≤proposition71LocalizedLargeAggregate D c b a X := by
  exact sum_nonneg (fun j hj => proposition71_localized_dyadic_aggregate_nonneg D c b a _ X)

/-- The full actual localized large-conductor positive majorant has a uniform
power saving after all r,θ,d,h and dyadic sums, normalized by the actual mass. -/
theorem proposition71_localized_large_aggregate_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
          ∀ X : ℕ, 1≤X → (X : ℝ)≤lemma23PaperP D →
            proposition71LocalizedLargeAggregate D c b a X≤
              C*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ) := by
  obtain ⟨C,hC,Dg,hDg,hagg⟩ := proposition71_localized_dyadic_aggregate_bound
  obtain ⟨Dm,hmass⟩ := lemma56_uniform_actual_prime_mass_lower
  obtain ⟨Da,habs⟩ := proposition71_log_power_rpow_threshold 149 (by norm_num : (0:ℝ)<1/32)
  refine ⟨C*2^11,by positivity,max Dg (max Dm (max Da ⌈Real.exp 1⌉₊)),hDg.trans (le_max_left _ _),?_⟩
  intro D hD χ hA c b B hB a ha X hX hXP
  have hg := (le_max_left _ _).trans hD
  have hm := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have haD := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have heD := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  have hD2 : 2≤D := hDg.trans hg
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hL : 1≤lemma23PaperL D := by
    have he : Real.exp 1≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast heD)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos 1) he
  have hLp : 0<lemma23PaperL D := by linarith
  have hM := lemma56_prime_mass_nonneg D
  have hprime : lemma23PaperP D^2≤4*lemma56PrimeMass D*lemma23PaperL D^77 := by
    have hp := (div_le_iff₀ (pow_pos hLp 77)).mp (hmass χ hm (by omega) hA)
    linarith
  have hlog : Real.log (X : ℝ)≤lemma23PaperL D^9 := by
    have hh := Real.log_le_log (by exact_mod_cast hX : (0:ℝ)<X) hXP
    simpa [lemma23PaperP] using hh
  have hlog0 : 0≤1+Real.log (X : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
    linarith
  have hpow : (1+Real.log (X : ℝ))^7≤2^7*lemma23PaperL D^63 := by
    have h9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL
    have hh := pow_le_pow_left₀ hlog0 (show 1+Real.log (X : ℝ)≤2*lemma23PaperL D^9 by linarith) 7
    simpa only [mul_pow,←pow_mul] using hh
  have hcount := proposition71_dyadic_block_count_bound hL
  have hlogsave := habs D haD
  unfold proposition71LocalizedLargeAggregate
  calc
    _≤∑ _j∈range (proposition71DyadicBlockCount D),
        C*B*lemma23PaperP D^2*(D : ℝ)^(-1/16 : ℝ)*(1+Real.log (X : ℝ))^7 := by
      apply sum_le_sum; intro j hj
      exact hagg D hg c b B hB a ha _ (proposition71_dyadic_scale_lower D j) X hX
    _=(proposition71DyadicBlockCount D : ℝ)*
        (C*B*lemma23PaperP D^2*(D : ℝ)^(-1/16 : ℝ)*(1+Real.log (X : ℝ))^7) := by simp
    _≤(4*lemma23PaperL D^9)*
        (C*B*(4*lemma56PrimeMass D*lemma23PaperL D^77)*(D : ℝ)^(-1/16 : ℝ)*
          (2^7*lemma23PaperL D^63)) := by gcongr
    _=(C*2^11)*B*lemma56PrimeMass D*lemma23PaperL D^149*(D : ℝ)^(-1/16 : ℝ) := by ring
    _≤(C*2^11)*B*lemma56PrimeMass D*(D : ℝ)^(1/32 : ℝ)*(D : ℝ)^(-1/16 : ℝ) := by gcongr
    _=_ := by
      rw [mul_assoc ((C*2^11)*B*lemma56PrimeMass D),←Real.rpow_add hDp]
      norm_num

end ZhangLS.Spec
