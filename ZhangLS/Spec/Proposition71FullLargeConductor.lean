import ZhangLS.Spec.Proposition71FullSigmaBlock
import ZhangLS.Spec.Proposition71LargeConductorSaving

/-! # The genuine unlocalized large-conductor part of the Section7 majorant

Every σ is the actual absolutely convergent infinite series. The original
strict d h r cutoff is retained; the internal lower boundary is D^(1/4).
The proved exact localization and fully summed literal tail justify passing
from σ* back to σ. No localization estimate is an input.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def proposition71ActualLargeConductorAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) : ℝ :=
  proposition71ConductorNormAggregate ⌊lemma23PaperP D⌋₊ ⌊lemma23PaperP D⌋₊
    (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D ∧ (D : ℝ)^(1/4 : ℝ)≤(r : ℝ))
    (fun d h _ θ => proposition71SigmaSeries D c b a h d θ)

lemma proposition71_actual_large_conductor_dyadic_cover {D : ℕ} (hD : 2≤D)
    (c b : ℝ) (a : ℕ → ℂ) :
    proposition71ActualLargeConductorAggregate D c b a≤
      ∑ j∈range (proposition71DyadicBlockCount D),
        proposition71FullSigmaConductorBlock D c b a (proposition71DyadicScale D j) ⌊lemma23PaperP D⌋₊ := by
  apply proposition71_conductor_aggregate_cover
    (range (proposition71DyadicBlockCount D)) ⌊lemma23PaperP D⌋₊ ⌊lemma23PaperP D⌋₊
  intro d hd h hh r hr hA
  have hr1 : 1<r := (mem_Icc.mp hr).1
  have hrP : (r : ℝ)≤lemma23PaperP D :=
    (by exact_mod_cast (mem_Icc.mp hr).2 : (r : ℝ)≤⌊lemma23PaperP D⌋₊).trans
      (Nat.floor_le (Real.exp_pos _).le)
  obtain ⟨j,hj,hjr⟩ := proposition71_dyadic_cover hD hr1 hA.2 hrP
  exact ⟨j,hj,hA.1,hjr⟩

/-- A genuine power saving for the complete infinite-σ large-conductor sum,
with all original arithmetic weights and the actual prime mass. -/
theorem proposition71_actual_large_conductor_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c b B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
          proposition71ActualLargeConductorAggregate D c b a≤
            C*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ) := by
  obtain ⟨Cm,hCm,Dm,hDm,hmain⟩ := proposition71_localized_large_aggregate_power_saving
  obtain ⟨Ce,hCe,De,hDe,herror⟩ := proposition71_offlocal_large_aggregate_power_saving
  obtain ⟨Ds,hDs,hsplit⟩ := proposition71_full_sigma_block_le_local_and_tail
  refine ⟨Cm+Ce,add_pos hCm hCe,
    max Dm (max De (max Ds ⌈Real.exp 2000⌉₊)),hDm.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA c b B hB a ha
  have hm := (le_max_left _ _).trans hDN
  have he := (le_max_left _ _).trans ((le_max_right _ _).trans hDN)
  have hs := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))
  have hExp := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))
  have hD2 : 2≤D := hDm.trans hm
  have hD1 : 1≤(D : ℝ) := by exact_mod_cast (show 1≤D by omega)
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hL : 2000≤lemma23PaperL D := by
    have hex : Real.exp 2000≤(D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hExp)
    simpa [lemma23PaperL] using Real.log_le_log (Real.exp_pos 2000) hex
  have hP : 1≤lemma23PaperP D := Real.one_le_exp_iff.mpr (pow_nonneg (by linarith : 0≤lemma23PaperL D) 9)
  have hM := lemma56_prime_mass_nonneg D
  have hmain' := hmain D hm χ hA c b B hB a ha ⌊lemma23PaperP D⌋₊
    (Nat.le_floor (by simpa only [Nat.cast_one] using hP)) (Nat.floor_le (by positivity))
  have herr := herror D he c b B hB a ha
  have hi : (D : ℝ)⁻¹≤(D : ℝ)^(-1/32 : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num : (-1 : ℝ)≤-1/32)
    simpa only [Real.rpow_neg_one] using hh
  calc
    _≤∑ j∈range (proposition71DyadicBlockCount D),
        proposition71FullSigmaConductorBlock D c b a (proposition71DyadicScale D j) ⌊lemma23PaperP D⌋₊ :=
      proposition71_actual_large_conductor_dyadic_cover hD2 c b a
    _≤∑ j∈range (proposition71DyadicBlockCount D),
        (proposition71LocalizedDyadicAggregate D c b a (proposition71DyadicScale D j) ⌊lemma23PaperP D⌋₊+
          proposition71OffLocalConductorAggregate D c b a (proposition71DyadicScale D j)
            ⌊lemma23PaperP D⌋₊ ⌊lemma23PaperP D⌋₊) := by
      apply sum_le_sum; intro j hj
      exact hsplit D hs (by omega) hL c b B hB a ha _ _
    _=proposition71LocalizedLargeAggregate D c b a ⌊lemma23PaperP D⌋₊+
        proposition71OffLocalLargeAggregate D c b a := by rw [sum_add_distrib]; rfl
    _≤Cm*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ)+Ce*B*lemma56PrimeMass D/(D : ℝ) :=
      add_le_add hmain' herr
    _≤(Cm+Ce)*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0≤Ce*B*lemma56PrimeMass D)
      rw [←div_eq_mul_inv] at hh
      nlinarith only [hh]

end ZhangLS.Spec
