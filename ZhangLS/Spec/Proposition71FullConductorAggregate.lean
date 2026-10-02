import ZhangLS.Spec.Proposition71FullLargeConductor
import ZhangLS.Spec.Proposition71FullSmallConductor
import ZhangLS.Spec.Proposition71ConductorModulusRestriction

/-! # The complete genuine positive conductor majorant on the right of (7.13)

The internal D^(1/4) split is now fully rejoined. Every σ is its actual
infinite series, every primitive conductor r>1 is included, and the original
strict d h r<PT⁻² and φ(hr) weights are retained. The separate derivation of
(7.13) from the original Gauss expression is not asserted here.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def proposition71ActualConductorAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) : ℝ :=
  proposition71ConductorNormAggregate ⌊lemma23PaperP D⌋₊ ⌊lemma23PaperP D⌋₊
    (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D)
    (fun d h _ θ => proposition71SigmaSeries D c b a h d θ)

/-- No positive strict-support triple is omitted by the finite index box. -/
lemma proposition71_strict_triple_indices {D d h r : ℕ} (hd : 0<d) (hh : 0<h) (hr : 0<r)
    (hcut : ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D) :
    d∈Icc 1 ⌊lemma23PaperP D⌋₊ ∧ h∈Icc 1 ⌊lemma23PaperP D⌋₊ ∧ r∈Icc 1 ⌊lemma23PaperP D⌋₊ := by
  have hf := proposition71_factors_le_product hd hh hr
  have hp : ((d*h*r : ℕ) : ℝ)≤lemma23PaperP D := hcut.le.trans (proposition71_cutoff_le_P D)
  refine ⟨mem_Icc.mpr ⟨hd,?_⟩,mem_Icc.mpr ⟨hh,?_⟩,mem_Icc.mpr ⟨hr,?_⟩⟩
  · exact Nat.le_floor ((by exact_mod_cast hf.1 : (d : ℝ)≤((d*h*r : ℕ) : ℝ)).trans hp)
  · exact Nat.le_floor ((by exact_mod_cast hf.2.1 : (h : ℝ)≤((d*h*r : ℕ) : ℝ)).trans hp)
  · exact Nat.le_floor ((by exact_mod_cast hf.2.2 : (r : ℝ)≤((d*h*r : ℕ) : ℝ)).trans hp)

lemma proposition71_actual_conductor_split (D : ℕ) (c b : ℝ) (a : ℕ → ℂ) :
    proposition71ActualConductorAggregate D c b a≤
      proposition71ActualSmallConductorAggregate D c b a+
        proposition71ActualLargeConductorAggregate D c b a := by
  let X := ⌊lemma23PaperP D⌋₊
  let Q := ⌊(D : ℝ)^(1/4 : ℝ)⌋₊
  let A := fun d h r : ℕ => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D
  let F := fun (d h r : ℕ) (θ : DirichletCharacter ℂ r) => proposition71SigmaSeries D c b a h d θ
  have hs := proposition71_conductor_aggregate_predicate_split X X A (fun _ _ r => r≤Q) F
  change proposition71ActualConductorAggregate D c b a=
    proposition71ConductorNormAggregate X X (fun d h r => A d h r ∧ r≤Q) F+
      proposition71ConductorNormAggregate X X (fun d h r => A d h r ∧ ¬r≤Q) F at hs
  rw [hs]
  apply add_le_add
  · exact proposition71_conductor_aggregate_upper_restrict X X Q A F
  · apply proposition71_conductor_aggregate_mono X X _ _ F F
    intro d hd h hh r hr hA
    have hR : (D : ℝ)^(1/4 : ℝ)<(r : ℝ) := Nat.lt_of_floor_lt (by simpa [Q] using not_le.mp hA.2)
    exact ⟨⟨hA.1,hR.le⟩,fun θ hθ => le_rfl⟩

/-- The complete unlocalized right-hand positive majorant of (7.13), with
its actual infinite coefficients, has a genuine uniform power saving. -/
theorem proposition71_actual_conductor_power_saving :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c b B : ℝ, 0≤B →
        |b|≤(D : ℝ)/2 → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
          proposition71ActualConductorAggregate D c b a≤C*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ) := by
  obtain ⟨Cs,hCs,Ds,hDs,hsmall⟩ := proposition71_actual_small_conductor_power_saving
  obtain ⟨Cl,hCl,Dl,hDl,hlarge⟩ := proposition71_actual_large_conductor_power_saving
  refine ⟨Cs+Cl,add_pos hCs hCl,max Ds Dl,hDs.trans (le_max_left _ _),?_⟩
  intro D hDN χ hA c b B hB hb a ha
  have hs := (le_max_left _ _).trans hDN
  have hl := (le_max_right _ _).trans hDN
  have hD2 : 2≤D := hDs.trans hs
  have hD1 : 1≤(D : ℝ) := by exact_mod_cast (show 1≤D by omega)
  have hM := lemma56_prime_mass_nonneg D
  have hp : (D : ℝ)^(-1/2 : ℝ)≤(D : ℝ)^(-1/32 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
  calc
    _≤proposition71ActualSmallConductorAggregate D c b a+proposition71ActualLargeConductorAggregate D c b a :=
      proposition71_actual_conductor_split D c b a
    _≤Cs*B*lemma56PrimeMass D*(D : ℝ)^(-1/2 : ℝ)+Cl*B*lemma56PrimeMass D*(D : ℝ)^(-1/32 : ℝ) :=
      add_le_add (hsmall D hs χ hA c b B hB hb a ha) (hlarge D hl χ hA c b B hB a ha)
    _≤_ := by
      have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0≤Cs*B*lemma56PrimeMass D)
      nlinarith only [hh]

end ZhangLS.Spec
