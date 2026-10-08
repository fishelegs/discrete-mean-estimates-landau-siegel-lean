import StaircaseDivision

noncomputable section

namespace PiWeightedColon

open Polynomial

theorem stairBound_smul {M : ℕ} (b : F2) (f : Plane) (hf : StairBound M f) :
    StairBound M (b • f) := by
  intro s a hsa
  simp only [coeff, Polynomial.coeff_smul, smul_eq_mul]
  change b * coeff f s a = 0
  rw [hf s a hsa, mul_zero]

def staircaseBoundSpace (M : ℕ) : Submodule F2 Plane where
  carrier := {f | StairBound M f}
  zero_mem' := stairBound_zero M
  add_mem' := fun hf hg => stairBound_add hf hg
  smul_mem' := fun b f hf => stairBound_smul b f hf

/-- The supplied rectangular staircase and the floored weight condition are
exactly equivalent, including both endpoint bounds. -/
theorem staircase_index_iff (N s a : ℕ) :
    stairWeight s a ≤ 4 * N + 1 ↔
      a ≤ 2 * N + 1 ∧ s ≤ 4 * (N - a / 2) + 1 := by
  unfold stairWeight
  omega

/-- The actual F₂ span of precisely the monomials in the stated staircase. -/
def V_N (N : ℕ) : Submodule F2 Plane :=
  Submodule.span F2 {f | ∃ s a, a ≤ 2 * N + 1 ∧
    s ≤ 4 * (N - a / 2) + 1 ∧ f = mono s a}

theorem V_N_le_bound (N : ℕ) : V_N N ≤ staircaseBoundSpace (4 * N + 1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, a, ha, hs, rfl⟩
  exact stairBound_bimono 1 ((staircase_index_iff N s a).mpr ⟨ha, hs⟩)

theorem bimono_eq_smul (s a : ℕ) (b : F2) : bimono s a b = b • mono s a := by
  simp [bimono, mono, Polynomial.smul_monomial, smul_eq_mul]

theorem bound_le_V_N (N : ℕ) : staircaseBoundSpace (4 * N + 1) ≤ V_N N := by
  intro f hf
  rw [← sum_monomial_eq f, sum_def]
  apply (V_N N).sum_mem
  intro s _
  rw [← sum_monomial_eq (f.coeff s), sum_def, map_sum]
  apply (V_N N).sum_mem
  intro a ha
  have hw : stairWeight s a ≤ 4 * N + 1 := by
    by_contra h
    exact mem_support_iff.mp ha (hf s a (by omega))
  obtain ⟨hya, hts⟩ := (staircase_index_iff N s a).mp hw
  have hm : mono (R := F2) s a ∈ V_N N := Submodule.subset_span
    ⟨s, a, hya, hts, rfl⟩
  have hb := (V_N N).smul_mem (coeff f s a) hm
  simpa only [← bimono_eq_smul, bimono, coeff] using hb

theorem V_N_eq_bound (N : ℕ) : V_N N = staircaseBoundSpace (4 * N + 1) :=
  le_antisymm (V_N_le_bound N) (bound_le_V_N N)

theorem V_N_membership (N : ℕ) (f : Plane) :
    f ∈ V_N N ↔ StairBound (4 * N + 1) f := by rw [V_N_eq_bound]; rfl

/-- Bounded division stated directly on the actual staircase span. -/
theorem V_N_bounded_division (N : ℕ) (f : Plane) (hf : f ∈ V_N N) :
    ∃ h : Plane, ∃ A B : Line,
      f = globalQ * h + linearRemainder A B ∧
      (if N = 0 then h = 0 else h ∈ V_N (N - 1)) ∧
      A.natDegree ≤ 4 * N + 1 ∧ B.natDegree ≤ 4 * N + 1 := by
  obtain ⟨h, A, B, he, hq, ha, hb⟩ :=
    staircase_division (4 * N + 1) f ((V_N_membership N f).mp hf)
  refine ⟨h, A, B, he, ?_, ha, hb⟩
  cases N with
  | zero => exact quotBound_scale_zero h hq
  | succ N =>
    rw [if_neg (Nat.succ_ne_zero N), Nat.succ_sub_one]
    exact (V_N_membership N h).mpr (quotBound_scale_succ N h hq)

/-- The all-scale algebraic vanishing theorem in the explicit coefficient
support model. No division or remainder hypotheses remain. -/
theorem staircase_dataIntersection_zero (N : ℕ) : ∀ f : Plane,
    StairBound (4 * N + 1) f → f ∈ dataIntersection N → f = 0 := by
  induction N with
  | zero =>
    intro f hf hI
    obtain ⟨h, A, B, he, hq, ha, hb⟩ := staircase_division 1 f hf
    have hz := quotBound_scale_zero h hq
    have hfactor := dataIntersection_factor_Q 0 f h A B hI he ha hb
    simpa [hz] using hfactor
  | succ N ih =>
    intro f hf hI
    obtain ⟨h, A, B, he, hq, ha, hb⟩ := staircase_division (4 * (N + 1) + 1) f hf
    have hfactor := dataIntersection_factor_Q (N + 1) f h A B hI he ha hb
    have hm : h ∈ (dataIntersection (N + 1)).colon {globalQ} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm, ← hfactor]
      exact hI
    rw [intersection_colon] at hm
    have hz := ih h (quotBound_scale_succ N h hq) hm
    simpa [hz] using hfactor

/-- The theorem for the actual monomial span V_N. -/
theorem V_N_dataIntersection_zero (N : ℕ) (f : Plane)
    (hf : f ∈ V_N N) (hI : f ∈ dataIntersection N) : f = 0 :=
  staircase_dataIntersection_zero N f ((V_N_membership N f).mp hf) hI

theorem V_N_inf_dataIntersection (N : ℕ) :
    V_N N ⊓ (dataIntersection N).restrictScalars F2 = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    exact V_N_dataIntersection_zero N f hf.1 hf.2
  · exact bot_le

end PiWeightedColon
