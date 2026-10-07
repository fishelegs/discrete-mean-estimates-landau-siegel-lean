import LargeConductorTheorem
import Splice.LValueNonnegative
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Global existential closure for the actual Dirichlet L-value

The large-conductor input is the proved declaration
`LargeConductorTheorem.norm_lower_bounds`. Below its cutoff, Mathlib's
`DirichletCharacter.LFunction_apply_one_ne_zero` makes the weighted norm
strictly positive for every nonprincipal character. The set of such
characters at the finitely many positive levels below the cutoff is finite.
An elementary finite induction produces a common strictly positive lower
bound. Thus neither a finite-family minimum nor its positivity is assumed.

The conclusion concerns the complex norm of the actual analytic continuation
`χ.LFunction 1`. The real-part corollaries additionally use the proved
nonnegativity and reality of this analytic value to identify its norm with
its real part. No positivity or class-number formula is assumed. Primitivity
makes a separate nonprincipality hypothesis redundant when D >= 3.

The final real and rational constants are existential. No explicit numerical
value or extracted effective procedure for these constants is claimed.
This file is prepared source-first; compilation and transitive axiom checks
must be reported separately from its mathematical statements.
-/

namespace GlobalFiniteClosure

/-- A finite family of strictly positive real numbers has a common strictly
positive strict lower bound. This also handles the empty family. -/
theorem finite_positive_lower_bound {ι : Type*} [Finite ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c < f i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ s : Finset ι, (∀ i ∈ s, 0 < f i) →
      ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c < f i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
        intro hs
        have ha0 : 0 < f a := hs a (Finset.mem_insert_self a s)
        obtain ⟨c, hc0, hc⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
        refine ⟨min c (f a / 2), lt_min hc0 (half_pos ha0), ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self ha0)
        · exact lt_of_le_of_lt (min_le_left _ _) (hc i hi)
  obtain ⟨c, hc0, hc⟩ := hfin Finset.univ (fun i _ => hf i)
  exact ⟨c, hc0, fun i => hc i (Finset.mem_univ i)⟩

/-- Positive conductors below the already-established large-conductor cutoff. -/
abbrev SmallModulus := {D : Fin (2 ^ 24) // 3 ≤ (D : ℕ)}

instance smallModulus_neZero (D : SmallModulus) : NeZero (D.1 : ℕ) := by
  refine ⟨?_⟩
  have hD := D.2
  omega

/-- All nonprincipal characters at the small conductors. No reality or
primitivity restriction is needed in this finite branch. -/
abbrev SmallCharacter :=
  Σ D : SmallModulus, {χ : DirichletCharacter ℂ (D.1 : ℕ) // χ ≠ 1}

/-- Finiteness follows from the bounded conductor type and Mathlib's
finiteness theorem for multiplicative characters into a domain. -/
instance smallCharacter_finite : Finite SmallCharacter := by
  dsimp only [SmallCharacter]
  infer_instance

lemma log_conductor_pos {D : ℕ} (hD : 3 ≤ D) : 0 < Real.log (D : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < D by omega)

/-- The positive quantity to which the finite-family argument is applied. -/
noncomputable def weightedNorm (x : SmallCharacter) : ℝ :=
  ‖x.2.1.LFunction 1‖ * Real.log ((x.1.1 : ℕ) : ℝ) ^ 2022

lemma weightedNorm_pos (x : SmallCharacter) : 0 < weightedNorm x := by
  unfold weightedNorm
  exact mul_pos
    (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero x.2.2))
    (pow_pos (log_conductor_pos x.1.2) _)

/-- The small-conductor branch, derived entirely from genuine nonvanishing
and actual finiteness; it has no assumed minimum or positivity premise. -/
theorem exists_small_conductor_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ) [NeZero D], 3 ≤ D → D < 2 ^ 24 →
        ∀ χ : DirichletCharacter ℂ D, χ ≠ 1 →
          c < ‖χ.LFunction 1‖ * Real.log (D : ℝ) ^ 2022 := by
  obtain ⟨c, hc0, hc⟩ := finite_positive_lower_bound weightedNorm weightedNorm_pos
  refine ⟨c, hc0, ?_⟩
  intro D _ hD hsmall χ hne
  let m : SmallModulus := ⟨⟨D, hsmall⟩, hD⟩
  let x : SmallCharacter := ⟨m, χ, hne⟩
  simpa only [weightedNorm, x, m] using hc x

/-- The large-conductor estimate dominates the requested logarithmic power
once the positive constant is at most `1 / 1536`. -/
theorem large_conductor_power_bound
    (D : ℕ) [NeZero D] (hD : 2 ^ 24 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {c : ℝ} (hc : c ≤ 1 / 1536) :
    c / Real.log (D : ℝ) ^ 2022 < ‖χ.LFunction 1‖ := by
  have hlog12 : 12 ≤ Real.log (D : ℝ) :=
    ExplicitCutoffAdapter.log_conductor_ge_twelve (by exact_mod_cast hD)
  have hlog1 : 1 ≤ Real.log (D : ℝ) := le_trans (by norm_num) hlog12
  have hlog0 : 0 < Real.log (D : ℝ) := lt_of_lt_of_le (by norm_num) hlog1
  have hpow : Real.log (D : ℝ) ≤ Real.log (D : ℝ) ^ 2022 :=
    le_self_pow₀ hlog1 (by norm_num)
  calc
    c / Real.log (D : ℝ) ^ 2022 ≤ (1 / 1536) / Real.log (D : ℝ) ^ 2022 :=
      div_le_div_of_nonneg_right hc (pow_nonneg hlog0.le _)
    _ ≤ (1 / 1536) / Real.log (D : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hlog0 hpow
    _ = 1 / (1536 * Real.log (D : ℝ)) := by rw [div_div]
    _ < ‖χ.LFunction 1‖ :=
      (LargeConductorTheorem.norm_lower_bounds D hD χ hreal hprim hne).1

/-- Global existential norm bound, retaining the explicit nonprincipality
hypothesis so that the two branches can be inspected directly. -/
theorem exists_global_norm_lower_bound_nonprincipal :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ) [NeZero D], 3 ≤ D →
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
          c / Real.log (D : ℝ) ^ 2022 < ‖χ.LFunction 1‖ := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_small_conductor_bound
  refine ⟨min c₀ (1 / 1536), lt_min hc₀0 (by norm_num), ?_⟩
  intro D _ hD χ hreal hprim hne
  by_cases hlarge : 2 ^ 24 ≤ D
  · exact large_conductor_power_bound D hlarge χ hreal hprim hne (min_le_right _ _)
  · apply (div_lt_iff₀ (pow_pos (log_conductor_pos hD) _)).2
    exact lt_of_le_of_lt (min_le_left _ _) (hc₀ D hD (lt_of_not_ge hlarge) χ hne)

/-- A primitive character at a level at least three is nonprincipal. -/
theorem primitive_ne_one {D : ℕ} [NeZero D] (hD : 3 ≤ D)
    {χ : DirichletCharacter ℂ D} (hprim : χ.IsPrimitive) : χ ≠ 1 := by
  intro hone
  have hc : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp hone
  have hlevel : χ.conductor = D := (DirichletCharacter.isPrimitive_def χ).mp hprim
  omega

/-- Global existential norm bound with nonprincipality discharged from
primitivity and D >= 3. The analytic API's `NeZero D` is redundant under D >= 3. -/
theorem exists_global_norm_lower_bound_primitive :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ) [NeZero D], 3 ≤ D →
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive →
          c / Real.log (D : ℝ) ^ 2022 < ‖χ.LFunction 1‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_global_norm_lower_bound_nonprincipal
  refine ⟨c, hc0, ?_⟩
  intro D _ hD χ hreal hprim
  exact hc D hD χ hreal hprim (primitive_ne_one hD hprim)

/-- The same theorem with the analytic API's nonzero instance constructed
from the displayed conductor hypothesis rather than requested separately. -/
theorem exists_global_norm_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive →
          c / Real.log (D : ℝ) ^ 2022 < ‖χ.LFunction 1‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_global_norm_lower_bound_primitive
  refine ⟨c, hc0, ?_⟩
  intro D hD
  letI : NeZero D := ⟨by omega⟩
  intro χ hreal hprim
  exact hc D hD χ hreal hprim

/-- Density of the rationals gives a positive rational constant. This is an
existence statement, with no numerical witness or effective algorithm claimed. -/
theorem exists_global_rational_norm_lower_bound :
    ∃ q : ℚ, 0 < q ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive →
          (q : ℝ) / Real.log (D : ℝ) ^ 2022 < ‖χ.LFunction 1‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_global_norm_lower_bound
  obtain ⟨q, hq0, hqc⟩ := exists_pos_rat_lt hc0
  refine ⟨q, hq0, ?_⟩
  intro D hD
  letI : NeZero D := ⟨by omega⟩
  intro χ hreal hprim
  exact lt_trans (div_lt_div_of_pos_right hqc (pow_pos (log_conductor_pos hD) _))
    (hc D hD χ hreal hprim)

/-- Genuine nonnegativity and reality identify the analytic value's norm
with its real part for every real, nonprincipal character. -/
theorem norm_LFunction_one_eq_re {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
  have heq := Splice.LFunction_one_eq_ofReal_re χ hne
    (Splice.character_sum_Icc_norm_le χ hne) hreal
  have hnonneg : 0 ≤ (χ.LFunction 1).re := Splice.LOne_nonneg χ hne hreal
  calc
    ‖χ.LFunction 1‖ = ‖((χ.LFunction 1).re : ℂ)‖ :=
      congrArg (fun z : ℂ => ‖z‖) heq
    _ = (χ.LFunction 1).re := Complex.norm_of_nonneg hnonneg

/-- Strict real-part positivity is derived from actual nonvanishing,
nonnegativity, and reality; it is not an input to the finite closure. -/
theorem LFunction_one_re_pos {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hreal : ∀ x : ZMod D, (χ x).im = 0) :
    0 < (χ.LFunction 1).re := by
  rw [← norm_LFunction_one_eq_re χ hne hreal]
  exact norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hne)

/-- The global real-part theorem has only the actual character hypotheses:
level at least three, reality, and primitivity. -/
theorem exists_global_real_part_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive →
          c / Real.log (D : ℝ) ^ 2022 < (χ.LFunction 1).re := by
  obtain ⟨c, hc0, hc⟩ := exists_global_norm_lower_bound
  refine ⟨c, hc0, ?_⟩
  intro D hD
  letI : NeZero D := ⟨by omega⟩
  intro χ hreal hprim
  rw [← norm_LFunction_one_eq_re χ (primitive_ne_one hD hprim) hreal]
  exact hc D hD χ hreal hprim

/-- The same global bound in the real-valued `Splice.LOne` notation. -/
theorem exists_global_LOne_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive →
          c / Real.log (D : ℝ) ^ 2022 < Splice.LOne χ := by
  exact exists_global_real_part_lower_bound

/-- A positive rational global constant also works for the actual real part. -/
theorem exists_global_rational_real_part_lower_bound :
    ∃ q : ℚ, 0 < q ∧
      ∀ (D : ℕ) (hD : 3 ≤ D),
        letI : NeZero D := ⟨by omega⟩
        ∀ χ : DirichletCharacter ℂ D,
          (∀ x : ZMod D, (χ x).im = 0) → χ.IsPrimitive →
          (q : ℝ) / Real.log (D : ℝ) ^ 2022 < (χ.LFunction 1).re := by
  obtain ⟨q, hq0, hq⟩ := exists_global_rational_norm_lower_bound
  refine ⟨q, hq0, ?_⟩
  intro D hD
  letI : NeZero D := ⟨by omega⟩
  intro χ hreal hprim
  rw [← norm_LFunction_one_eq_re χ (primitive_ne_one hD hprim) hreal]
  exact hq D hD χ hreal hprim

#check DirichletCharacter.LFunction_apply_one_ne_zero
#check finite_positive_lower_bound
#check exists_small_conductor_bound
#check large_conductor_power_bound
#check exists_global_norm_lower_bound_nonprincipal
#check primitive_ne_one
#check exists_global_norm_lower_bound_primitive
#check exists_global_norm_lower_bound
#check exists_global_rational_norm_lower_bound
#check norm_LFunction_one_eq_re
#check LFunction_one_re_pos
#check exists_global_real_part_lower_bound
#check exists_global_LOne_lower_bound
#check exists_global_rational_real_part_lower_bound

#print axioms DirichletCharacter.LFunction_apply_one_ne_zero
#print axioms finite_positive_lower_bound
#print axioms exists_small_conductor_bound
#print axioms large_conductor_power_bound
#print axioms exists_global_norm_lower_bound_nonprincipal
#print axioms primitive_ne_one
#print axioms exists_global_norm_lower_bound_primitive
#print axioms exists_global_norm_lower_bound
#print axioms exists_global_rational_norm_lower_bound
#print axioms norm_LFunction_one_eq_re
#print axioms LFunction_one_re_pos
#print axioms exists_global_real_part_lower_bound
#print axioms exists_global_LOne_lower_bound
#print axioms exists_global_rational_real_part_lower_bound

end GlobalFiniteClosure
