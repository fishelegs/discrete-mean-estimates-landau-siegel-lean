import GlobalFiniteClosure
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A terminating rational search for the global constant

The executable part uses only finite tables with entries -1, 0, 1, natural
numbers, rational arithmetic, and concrete finite decidability. Analytic
L-values occur only in erased proofs of termination and correctness.
No finite family is evaluated here, and no numerical value of the resulting
constant is claimed. In particular, no class-number formula is used.
-/

namespace EffectiveConstantSearch

open Finset Filter
open scoped Topology

-- Retain proof-erased executable code in the verification log.
set_option trace.Compiler.result true

/-- A concrete finite coefficient alphabet. -/
inductive Sign where
  | neg | zero | pos
  deriving DecidableEq

instance : Fintype Sign where
  elems := {.neg, .zero, .pos}
  complete x := by cases x <;> simp

/-- Rational interpretation, used in every executable test. -/
def coefficient : Sign → ℚ
  | .neg => -1
  | .zero => 0
  | .pos => 1

abbrev Table (D : ℕ) := ZMod D → Sign

/-- Arithmetic-only character and nonprincipality tests. -/
def Valid {D : ℕ} (f : Table D) : Prop :=
  coefficient (f 1) = 1 ∧
  (∀ a b : ZMod D, coefficient (f (a * b)) = coefficient (f a) * coefficient (f b)) ∧
  (∀ a : ZMod D, ¬ a.val.Coprime D → coefficient (f a) = 0) ∧
  (∃ a : ZMod D, a.val.Coprime D ∧ coefficient (f a) ≠ 1)

/-- This instance does not use classical decidability. -/
instance validDecidable {D : ℕ} [NeZero D] (f : Table D) : Decidable (Valid f) := by
  unfold Valid
  infer_instance

lemma isUnit_iff_val_coprime {D : ℕ} [NeZero D] (a : ZMod D) :
    IsUnit a ↔ a.val.Coprime D := by
  simpa only [ZMod.natCast_zmod_val] using ZMod.isUnit_iff_coprime a.val D

/-- Used only in proofs: a table that passes the tests is an actual character. -/
noncomputable def character {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f) :
    DirichletCharacter ℂ D where
  toFun a := (coefficient (f a) : ℂ)
  map_one' := by rw [hf.1]; norm_num
  map_mul' a b := by rw [hf.2.1 a b]; push_cast; rfl
  map_nonunit' a ha := by
    rw [hf.2.2.1 a (fun h => ha ((isUnit_iff_val_coprime a).mpr h))]
    norm_num

lemma character_real {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f)
    (a : ZMod D) : (character f hf a).im = 0 := by
  change ((coefficient (f a) : ℚ) : ℂ).im = 0
  simp

lemma character_ne_one {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f) :
    character f hf ≠ 1 := by
  obtain ⟨a, ha, hfa⟩ := hf.2.2.2
  intro h
  have heq := congrArg (fun χ : DirichletCharacter ℂ D => χ a) h
  rw [MulChar.one_apply ((isUnit_iff_val_coprime a).mpr ha)] at heq
  apply hfa
  change ((coefficient (f a) : ℚ) : ℂ) = 1 at heq
  exact_mod_cast heq

/-- Exactly computable ordered harmonic sum with a natural cutoff. -/
def harmonicSum {D : ℕ} (f : Table D) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 N, coefficient (f k) / (k : ℚ)

lemma harmonicSum_cast {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f) (N : ℕ) :
    (harmonicSum f N : ℝ) =
      ∑ k ∈ Finset.Icc 1 N, (character f hf k).re / (k : ℝ) := by
  simp [harmonicSum, character]

/-- The already-proved ordered-tail estimate, specialized to the rational table. -/
lemma harmonicSum_error {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f)
    {N : ℕ} (hN : 0 < N) :
    |(harmonicSum f N : ℝ) - ((character f hf).LFunction 1).re| ≤
      2 * (D : ℝ) / (N : ℝ) := by
  have h := Splice.abs_characterHarmonicSum_re_sub_LFunction_one_le
    (character f hf) (character_ne_one f hf)
    (Splice.character_sum_Icc_norm_le (character f hf) (character_ne_one f hf))
    (T := (N : ℝ)) (by exact_mod_cast hN)
  simpa only [Nat.floor_natCast, ← harmonicSum_cast f hf N] using h

/-- A decidable positive certificate at cutoff `n+1`. -/
def Pass {D : ℕ} (f : Table D) (n : ℕ) : Prop :=
  (2 * (D : ℚ) + 1) / ((n : ℚ) + 1) < harmonicSum f (n + 1)

instance passDecidable {D : ℕ} (f : Table D) (n : ℕ) : Decidable (Pass f n) := by
  unfold Pass
  infer_instance

lemma pass_sound {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f) (n : ℕ)
    (hp : Pass f n) :
    (1 : ℝ) / ((n : ℝ) + 1) < ((character f hf).LFunction 1).re := by
  have ht := harmonicSum_error f hf (Nat.succ_pos n)
  have hpR : (2 * (D : ℝ) + 1) / ((n : ℝ) + 1) < (harmonicSum f (n + 1) : ℝ) := by
    unfold Pass at hp
    have h := (Rat.cast_lt (K := ℝ)).mpr hp
    push_cast at h
    exact h
  have heq : (2 * (D : ℝ) + 1) / ((n : ℝ) + 1) =
      2 * (D : ℝ) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at ht
  rw [heq] at hpR
  linarith [(abs_le.mp ht).2]

/-- Each valid table eventually passes, using genuine strict L-value positivity. -/
lemma eventually_pass {D : ℕ} [NeZero D] (f : Table D) (hf : Valid f) :
    ∀ᶠ n : ℕ in atTop, Pass f n := by
  let L : ℝ := ((character f hf).LFunction 1).re
  have hL : 0 < L := GlobalFiniteClosure.LFunction_one_re_pos
    (character f hf) (character_ne_one f hf) (character_real f hf)
  obtain ⟨m, hm⟩ := exists_nat_gt ((4 * (D : ℝ) + 1) / L)
  refine (eventually_ge_atTop m).mono fun n hn => ?_
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hmn : (m : ℝ) < (n : ℝ) + 1 := by exact_mod_cast (Nat.lt_succ_of_le hn)
  have hnum : 4 * (D : ℝ) + 1 < ((n : ℝ) + 1) * L :=
    (div_lt_iff₀ hL).mp (hm.trans hmn)
  have hsmall : (4 * (D : ℝ) + 1) / ((n : ℝ) + 1) < L :=
    (div_lt_iff₀ hden).mpr (by nlinarith [hnum])
  have ht := harmonicSum_error f hf (Nat.succ_pos n)
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at ht
  have heq : (4 * (D : ℝ) + 1) / ((n : ℝ) + 1) =
      (2 * (D : ℝ) + 1) / ((n : ℝ) + 1) + 2 * (D : ℝ) / ((n : ℝ) + 1) := by ring
  rw [heq] at hsmall
  have hpR : (2 * (D : ℝ) + 1) / ((n : ℝ) + 1) < (harmonicSum f (n + 1) : ℝ) := by
    dsimp [L] at hsmall
    linarith [(abs_le.mp ht).1]
  unfold Pass
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  exact hpR

abbrev SmallModulus (B : ℕ) := {D : Fin B // 3 ≤ (D : ℕ)}

instance smallModulus_neZero {B : ℕ} (D : SmallModulus B) : NeZero (D.1 : ℕ) := by
  refine ⟨?_⟩
  have hD := D.2
  omega

/-- A concretely enumerable finite family, not an abstract finite character type. -/
abbrev SmallTable (B : ℕ) := Σ D : SmallModulus B, Table (D.1 : ℕ)

instance (B : ℕ) : Fintype (SmallTable B) := inferInstance

/-- Invalid tables are skipped by an executable finite decision procedure. -/
def AllPass (B n : ℕ) : Prop :=
  ∀ x : SmallTable B, Valid x.2 → Pass x.2 n

instance allPassDecidable (B n : ℕ) : Decidable (AllPass B n) := by
  unfold AllPass
  infer_instance

/-- Finiteness plus positivity proves search termination, without computing a bound. -/
theorem search_terminates (B : ℕ) : ∃ n : ℕ, AllPass B n := by
  have h : ∀ x : SmallTable B, ∀ᶠ n : ℕ in atTop, Valid x.2 → Pass x.2 n := by
    intro x
    by_cases hx : Valid x.2
    · exact (eventually_pass x.2 hx).mono fun n hn _ => hn
    · exact Filter.Eventually.of_forall fun n hn => (hx hn).elim
  exact (Filter.eventually_all.mpr h).exists

/-- A total executable natural search. Its termination argument is proof-erased. -/
def searchIndex (B : ℕ) : ℕ := Nat.find (search_terminates B)

/-- The returned rational is positive, with a fixed cap for the large-conductor branch. -/
def constant (B : ℕ) : ℚ := min (1 / 1536) (1 / ((searchIndex B : ℚ) + 1))

set_option trace.Compiler.result false

lemma searchIndex_spec (B : ℕ) : AllPass B (searchIndex B) := Nat.find_spec (search_terminates B)

lemma constant_pos (B : ℕ) : 0 < constant B := by
  unfold constant
  exact lt_min (by norm_num) (by positivity)

lemma constant_le_large (B : ℕ) : (constant B : ℝ) ≤ 1 / 1536 := by
  simp only [constant, Rat.cast_min, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_ofNat]
  exact min_le_left _ _

lemma constant_le_small (B : ℕ) : (constant B : ℝ) ≤ 1 / ((searchIndex B : ℝ) + 1) := by
  simp only [constant, Rat.cast_min, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_ofNat]
  exact min_le_right _ _

/-- Encoding a given complex character is used only in the coverage proof. -/
noncomputable def encode (z : ℂ) : Sign :=
  if z = 0 then .zero else if z = 1 then .pos else .neg

lemma encode_spec (z : ℂ) (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    ((coefficient (encode z) : ℚ) : ℂ) = z := by
  rcases hz with rfl | rfl | rfl <;> norm_num [encode, coefficient]

/-- Every real-valued character is covered by one finite signed table. -/
theorem exists_valid_table {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hreal : ∀ a : ZMod D, (χ a).im = 0) (hne : χ ≠ 1) :
    ∃ (f : Table D) (hf : Valid f), character f hf = χ := by
  classical
  let f : Table D := fun a => encode (χ a)
  have hquad : χ.IsQuadratic :=
    MulChar.isQuadratic_iff_sq_eq_one.mpr (Splice.real_character_sq χ hreal)
  have heq (a : ZMod D) : ((coefficient (f a) : ℚ) : ℂ) = χ a :=
    encode_spec (χ a) (hquad a)
  have hf : Valid f := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Rat.cast_injective (α := ℂ)
      simpa only [heq, Rat.cast_one] using χ.map_one
    · intro a b
      apply Rat.cast_injective (α := ℂ)
      simpa only [Rat.cast_mul, heq] using (map_mul χ a b)
    · intro a ha
      apply Rat.cast_injective (α := ℂ)
      simpa only [Rat.cast_zero, heq] using
        χ.map_nonunit (fun h => ha ((isUnit_iff_val_coprime a).mp h))
    · obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hne
      refine ⟨a, (isUnit_iff_val_coprime (a : ZMod D)).mp a.isUnit, ?_⟩
      intro h
      apply ha
      rw [← heq, h]
      norm_num
  refine ⟨f, hf, ?_⟩
  exact MulChar.ext' heq

lemma log_conductor_ge_one {D : ℕ} (hD : 3 ≤ D) : 1 ≤ Real.log (D : ℝ) := by
  have h3 : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hlog : Real.log 3 ≤ Real.log (D : ℝ) := Real.log_le_log (by norm_num) h3
  have hlog3 := Real.log_three_gt_d9
  linarith

/-- Full correctness of the concrete rational search, for the actual analytic value. -/
theorem constant_correct (D : ℕ) [NeZero D] (hD : 3 ≤ D)
    (χ : DirichletCharacter ℂ D) (hreal : ∀ a : ZMod D, (χ a).im = 0)
    (hprim : χ.IsPrimitive) :
    (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) ^ 2022 < (χ.LFunction 1).re := by
  have hne : χ ≠ 1 := GlobalFiniteClosure.primitive_ne_one hD hprim
  by_cases hlarge : 2 ^ 24 ≤ D
  · rw [← GlobalFiniteClosure.norm_LFunction_one_eq_re χ hne hreal]
    exact GlobalFiniteClosure.large_conductor_power_bound D hlarge χ hreal hprim hne
      (constant_le_large (2 ^ 24))
  · obtain ⟨f, hf, heq⟩ := exists_valid_table χ hreal hne
    let m : SmallModulus (2 ^ 24) := ⟨⟨D, lt_of_not_ge hlarge⟩, hD⟩
    let x : SmallTable (2 ^ 24) := ⟨m, f⟩
    have hp : Pass f (searchIndex (2 ^ 24)) := searchIndex_spec (2 ^ 24) x hf
    have hL := pass_sound f hf (searchIndex (2 ^ 24)) hp
    rw [heq] at hL
    have hpow : 1 ≤ Real.log (D : ℝ) ^ 2022 := one_le_pow₀ (log_conductor_ge_one hD)
    have hc0 : 0 ≤ (constant (2 ^ 24) : ℝ) := by exact_mod_cast (constant_pos (2 ^ 24)).le
    have hdiv : (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) ^ 2022 ≤ constant (2 ^ 24) :=
      div_le_self hc0 hpow
    exact lt_of_le_of_lt (hdiv.trans (constant_le_small (2 ^ 24))) hL

/-- A total program and its certified positive global bound, with no extra input hypotheses. -/
theorem effective_global_bound :
    0 < constant (2 ^ 24) ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ a : ZMod D, (χ a).im = 0) → χ.IsPrimitive →
          (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) ^ 2022 < (χ.LFunction 1).re := by
  refine ⟨constant_pos (2 ^ 24), ?_⟩
  intro D hD
  letI : NeZero D := ⟨by omega⟩
  intro χ hreal hprim
  exact constant_correct D hD χ hreal hprim

/-- The same computed constant gives the stronger global logarithmic bound. -/
theorem constant_correct_log (D : ℕ) [NeZero D] (hD : 3 ≤ D)
    (χ : DirichletCharacter ℂ D) (hreal : ∀ a : ZMod D, (χ a).im = 0)
    (hprim : χ.IsPrimitive) :
    (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) < (χ.LFunction 1).re := by
  have hne : χ ≠ 1 := GlobalFiniteClosure.primitive_ne_one hD hprim
  have hlog : 0 < Real.log (D : ℝ) := GlobalFiniteClosure.log_conductor_pos hD
  by_cases hlarge : 2 ^ 24 ≤ D
  · calc
      (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) ≤ (1 / 1536) / Real.log (D : ℝ) :=
        div_le_div_of_nonneg_right (constant_le_large (2 ^ 24)) hlog.le
      _ = 1 / (1536 * Real.log (D : ℝ)) := by ring
      _ < (χ.LFunction 1).re :=
        (LargeConductorTheorem.real_part_lower_bounds D hlarge χ hreal hprim hne).1
  · obtain ⟨f, hf, heq⟩ := exists_valid_table χ hreal hne
    let m : SmallModulus (2 ^ 24) := ⟨⟨D, lt_of_not_ge hlarge⟩, hD⟩
    let x : SmallTable (2 ^ 24) := ⟨m, f⟩
    have hp : Pass f (searchIndex (2 ^ 24)) := searchIndex_spec (2 ^ 24) x hf
    have hL := pass_sound f hf (searchIndex (2 ^ 24)) hp
    rw [heq] at hL
    have hc0 : 0 ≤ (constant (2 ^ 24) : ℝ) := by exact_mod_cast (constant_pos (2 ^ 24)).le
    have hdiv : (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) ≤ constant (2 ^ 24) :=
      div_le_self hc0 (log_conductor_ge_one hD)
    exact lt_of_le_of_lt (hdiv.trans (constant_le_small (2 ^ 24))) hL

/-- Stronger packaged correctness, still without an evaluated numerical witness. -/
theorem effective_global_log_bound :
    0 < constant (2 ^ 24) ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ a : ZMod D, (χ a).im = 0) → χ.IsPrimitive →
          (constant (2 ^ 24) : ℝ) / Real.log (D : ℝ) < (χ.LFunction 1).re := by
  refine ⟨constant_pos (2 ^ 24), ?_⟩
  intro D hD
  letI : NeZero D := ⟨by omega⟩
  intro χ hreal hprim
  exact constant_correct_log D hD χ hreal hprim

/- Tiny execution test only: D = 3, never the enormous target cutoff. -/
#eval searchIndex 4

#print axioms search_terminates
#print axioms searchIndex
#print axioms constant
#print axioms exists_valid_table
#print axioms constant_correct
#print axioms effective_global_bound
#print axioms constant_correct_log
#print axioms effective_global_log_bound

end EffectiveConstantSearch
